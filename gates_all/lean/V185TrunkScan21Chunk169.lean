import V185TrunkScan21Chunk168

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_2059063 : List Nat := [1, 1, 3, 1, 2, 1, 4, 8]
def baseStart_2059063 : Nat := 118140960795 + 2059063 * 2 ^ 59
def prefixEnd_2059063 : Nat := 4983230072969 + 3 ^ 40 * 2059063 * 2
def baseEnd_2059063 : Nat := 156635409909449280036007

theorem tailTrace_2059063 : CollatzResearch.WordTrace tailWord_2059063 prefixEnd_2059063 156635409909449280036007 := by
  unfold tailWord_2059063
  simp only [CollatzResearch.WordTrace]
  refine ⟨75100197339373885808429843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50066798226249257205619895 75100197339373885808429843)
  ·
    refine ⟨112650296009060828712644765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75100197339373885808429843 112650296009060828712644765)
    ·
      refine ⟨42243861003397810767241787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112650296009060828712644765 42243861003397810767241787)
      ·
        refine ⟨63365791505096716150862681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42243861003397810767241787 63365791505096716150862681)
        ·
          refine ⟨47524343628822537113147011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63365791505096716150862681 47524343628822537113147011)
          ·
            refine ⟨71286515443233805669720517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47524343628822537113147011 71286515443233805669720517)
            ·
              refine ⟨13366221645606338563072597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71286515443233805669720517 13366221645606338563072597)
              ·
                refine ⟨156635409909449280036007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13366221645606338563072597 156635409909449280036007)
                ·
                  rfl

theorem cell21_2059063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_2059063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059063 prefixEnd_2059063 := by exact prefixLift 2059063
  have htrace : WordTrace (prefixWord ++ tailWord_2059063) baseStart_2059063 baseEnd_2059063 := by
    simpa [prefixWord, tailWord_2059063, baseEnd_2059063] using wordTrace_append hprefix tailTrace_2059063
  have hstable : (prefixWord ++ tailWord_2059063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059063).length < 2 ^ (prefixWord ++ tailWord_2059063).sum := by decide
  have hdescent : baseEnd_2059063 < baseStart_2059063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059111 : List Nat := [1, 1, 5, 1, 2, 2, 3, 1, 5]
def baseStart_2059111 : Nat := 118140960795 + 2059111 * 2 ^ 59
def prefixEnd_2059111 : Nat := 4983230072969 + 3 ^ 40 * 2059111 * 2
def baseEnd_2059111 : Nat := 469917183982310423307923

theorem tailTrace_2059111 : CollatzResearch.WordTrace tailWord_2059111 prefixEnd_2059111 469917183982310423307923 := by
  unfold tailWord_2059111
  simp only [CollatzResearch.WordTrace]
  refine ⟨75101948043199990006177187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50067965362133326670784791 75101948043199990006177187)
  ·
    refine ⟨112652922064799985009265781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75101948043199990006177187 112652922064799985009265781)
    ·
      refine ⟨10561211443574998594618667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 112652922064799985009265781 10561211443574998594618667)
      ·
        refine ⟨15841817165362497891928001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10561211443574998594618667 15841817165362497891928001)
        ·
          refine ⟨11881362874021873418946001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15841817165362497891928001 11881362874021873418946001)
          ·
            refine ⟨8911022155516405064209501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11881362874021873418946001 8911022155516405064209501)
            ·
              refine ⟨3341633308318651899078563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8911022155516405064209501 3341633308318651899078563)
              ·
                refine ⟨5012449962477977848617845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3341633308318651899078563 5012449962477977848617845)
                ·
                  refine ⟨469917183982310423307923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5012449962477977848617845 469917183982310423307923)
                  ·
                    rfl

theorem cell21_2059111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_2059111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059111 prefixEnd_2059111 := by exact prefixLift 2059111
  have htrace : WordTrace (prefixWord ++ tailWord_2059111) baseStart_2059111 baseEnd_2059111 := by
    simpa [prefixWord, tailWord_2059111, baseEnd_2059111] using wordTrace_append hprefix tailTrace_2059111
  have hstable : (prefixWord ++ tailWord_2059111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059111).length < 2 ^ (prefixWord ++ tailWord_2059111).sum := by decide
  have hdescent : baseEnd_2059111 < baseStart_2059111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059139 : List Nat := [1, 1, 1, 3, 4, 1, 1, 9]
def baseStart_2059139 : Nat := 118140960795 + 2059139 * 2 ^ 59
def prefixEnd_2059139 : Nat := 4983230072969 + 3 ^ 40 * 2059139 * 2
def baseEnd_2059139 : Nat := 156641191321262865613733

theorem tailTrace_2059139 : CollatzResearch.WordTrace tailWord_2059139 prefixEnd_2059139 156641191321262865613733 := by
  unfold tailWord_2059139
  simp only [CollatzResearch.WordTrace]
  refine ⟨75102969287098550788196471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50068646191399033858797647 75102969287098550788196471)
  ·
    refine ⟨112654453930647826182294707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75102969287098550788196471 112654453930647826182294707)
    ·
      refine ⟨168981680895971739273442061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112654453930647826182294707 168981680895971739273442061)
      ·
        refine ⟨63368130335989402227540773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 168981680895971739273442061 63368130335989402227540773)
        ·
          refine ⟨11881524437998012917663895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63368130335989402227540773 11881524437998012917663895)
          ·
            refine ⟨17822286656997019376495843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11881524437998012917663895 17822286656997019376495843)
            ·
              refine ⟨26733429985495529064743765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17822286656997019376495843 26733429985495529064743765)
              ·
                refine ⟨156641191321262865613733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26733429985495529064743765 156641191321262865613733)
                ·
                  rfl

theorem cell21_2059139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_2059139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059139 prefixEnd_2059139 := by exact prefixLift 2059139
  have htrace : WordTrace (prefixWord ++ tailWord_2059139) baseStart_2059139 baseEnd_2059139 := by
    simpa [prefixWord, tailWord_2059139, baseEnd_2059139] using wordTrace_append hprefix tailTrace_2059139
  have hstable : (prefixWord ++ tailWord_2059139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059139).length < 2 ^ (prefixWord ++ tailWord_2059139).sum := by decide
  have hdescent : baseEnd_2059139 < baseStart_2059139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059162 : List Nat := [3, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_2059162 : Nat := 118140960795 + 2059162 * 2 ^ 59
def prefixEnd_2059162 : Nat := 4983230072969 + 3 ^ 40 * 2059162 * 2
def baseEnd_2059162 : Nat := 469928822877145667957819

theorem tailTrace_2059162 : CollatzResearch.WordTrace tailWord_2059162 prefixEnd_2059162 469928822877145667957819 := by
  unfold tailWord_2059162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18775952041503806429070935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50069205444010150477522493 18775952041503806429070935)
  ·
    refine ⟨28163928062255709643606403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18775952041503806429070935 28163928062255709643606403)
    ·
      refine ⟨42245892093383564465409605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28163928062255709643606403 42245892093383564465409605)
      ·
        refine ⟨7921104767509418337264301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42245892093383564465409605 7921104767509418337264301)
        ·
          refine ⟨2970414287816031876474113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7921104767509418337264301 2970414287816031876474113)
          ·
            refine ⟨2227810715862023907355585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970414287816031876474113 2227810715862023907355585)
            ·
              refine ⟨1670858036896517930516689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227810715862023907355585 1670858036896517930516689)
              ·
                refine ⟨1253143527672388447887517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1670858036896517930516689 1253143527672388447887517)
                ·
                  refine ⟨469928822877145667957819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253143527672388447887517 469928822877145667957819)
                  ·
                    rfl

theorem cell21_2059162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_2059162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059162 prefixEnd_2059162 := by exact prefixLift 2059162
  have htrace : WordTrace (prefixWord ++ tailWord_2059162) baseStart_2059162 baseEnd_2059162 := by
    simpa [prefixWord, tailWord_2059162, baseEnd_2059162] using wordTrace_append hprefix tailTrace_2059162
  have hstable : (prefixWord ++ tailWord_2059162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059162).length < 2 ^ (prefixWord ++ tailWord_2059162).sum := by decide
  have hdescent : baseEnd_2059162 < baseStart_2059162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059215 : List Nat := [1, 1, 2, 1, 1, 7, 8]
def baseStart_2059215 : Nat := 118140960795 + 2059215 * 2 ^ 59
def prefixEnd_2059215 : Nat := 4983230072969 + 3 ^ 40 * 2059215 * 2
def baseEnd_2059215 : Nat := 52215657577692150397153

theorem tailTrace_2059215 : CollatzResearch.WordTrace tailWord_2059215 prefixEnd_2059215 52215657577692150397153 := by
  unfold tailWord_2059215
  simp only [CollatzResearch.WordTrace]
  refine ⟨75105741234823215767963099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50070494156548810511975399 75105741234823215767963099)
  ·
    refine ⟨112658611852234823651944649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75105741234823215767963099 112658611852234823651944649)
    ·
      refine ⟨84493958889176117738958487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112658611852234823651944649 84493958889176117738958487)
      ·
        refine ⟨126740938333764176608437731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84493958889176117738958487 126740938333764176608437731)
        ·
          refine ⟨190111407500646264912656597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126740938333764176608437731 190111407500646264912656597)
          ·
            refine ⟨4455736113296396833890389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 190111407500646264912656597 4455736113296396833890389)
            ·
              refine ⟨52215657577692150397153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4455736113296396833890389 52215657577692150397153)
              ·
                rfl

theorem cell21_2059215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 8].length) (baseStart_2059215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059215 prefixEnd_2059215 := by exact prefixLift 2059215
  have htrace : WordTrace (prefixWord ++ tailWord_2059215) baseStart_2059215 baseEnd_2059215 := by
    simpa [prefixWord, tailWord_2059215, baseEnd_2059215] using wordTrace_append hprefix tailTrace_2059215
  have hstable : (prefixWord ++ tailWord_2059215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059215).length < 2 ^ (prefixWord ++ tailWord_2059215).sum := by decide
  have hdescent : baseEnd_2059215 < baseStart_2059215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059218 : List Nat := [3, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_2059218 : Nat := 118140960795 + 2059218 * 2 ^ 59
def prefixEnd_2059218 : Nat := 4983230072969 + 3 ^ 40 * 2059218 * 2
def baseEnd_2059218 : Nat := 469941602840102015024371

theorem tailTrace_2059218 : CollatzResearch.WordTrace tailWord_2059218 prefixEnd_2059218 469941602840102015024371 := by
  unfold tailWord_2059218
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776462663453086820080577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50070567102541564853548205 18776462663453086820080577)
  ·
    refine ⟨14082346997589815115060433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18776462663453086820080577 14082346997589815115060433)
    ·
      refine ⟨10561760248192361336295325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14082346997589815115060433 10561760248192361336295325)
      ·
        refine ⟨3960660093072135501110747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10561760248192361336295325 3960660093072135501110747)
        ·
          refine ⟨5940990139608203251666121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3960660093072135501110747 5940990139608203251666121)
          ·
            refine ⟨4455742604706152438749591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5940990139608203251666121 4455742604706152438749591)
            ·
              refine ⟨6683613907059228658124387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4455742604706152438749591 6683613907059228658124387)
              ·
                refine ⟨10025420860588842987186581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6683613907059228658124387 10025420860588842987186581)
                ·
                  refine ⟨469941602840102015024371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10025420860588842987186581 469941602840102015024371)
                  ·
                    rfl

theorem cell21_2059218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_2059218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059218 prefixEnd_2059218 := by exact prefixLift 2059218
  have htrace : WordTrace (prefixWord ++ tailWord_2059218) baseStart_2059218 baseEnd_2059218 := by
    simpa [prefixWord, tailWord_2059218, baseEnd_2059218] using wordTrace_append hprefix tailTrace_2059218
  have hstable : (prefixWord ++ tailWord_2059218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059218).length < 2 ^ (prefixWord ++ tailWord_2059218).sum := by decide
  have hdescent : baseEnd_2059218 < baseStart_2059218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059249 : List Nat := [1, 2, 2, 2, 4, 3, 2, 5]
def baseStart_2059249 : Nat := 118140960795 + 2059249 * 2 ^ 59
def prefixEnd_2059249 : Nat := 4983230072969 + 3 ^ 40 * 2059249 * 2
def baseEnd_2059249 : Nat := 156649559154150950002547

theorem tailTrace_2059249 : CollatzResearch.WordTrace tailWord_2059249 prefixEnd_2059249 156649559154150950002547 := by
  unfold tailWord_2059249
  simp only [CollatzResearch.WordTrace]
  refine ⟨75106981316700039574700801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50071320877800026383133867 75106981316700039574700801)
  ·
    refine ⟨56330235987525029681025601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75106981316700039574700801 56330235987525029681025601)
    ·
      refine ⟨42247676990643772260769201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56330235987525029681025601 42247676990643772260769201)
      ·
        refine ⟨31685757742982829195576901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42247676990643772260769201 31685757742982829195576901)
        ·
          refine ⟨5941079576809280474170669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31685757742982829195576901 5941079576809280474170669)
          ·
            refine ⟨2227904841303480177814001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5941079576809280474170669 2227904841303480177814001)
            ·
              refine ⟨1670928630977610133360501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2227904841303480177814001 1670928630977610133360501)
              ·
                refine ⟨156649559154150950002547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1670928630977610133360501 156649559154150950002547)
                ·
                  rfl

theorem cell21_2059249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 5].length) (baseStart_2059249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059249 prefixEnd_2059249 := by exact prefixLift 2059249
  have htrace : WordTrace (prefixWord ++ tailWord_2059249) baseStart_2059249 baseEnd_2059249 := by
    simpa [prefixWord, tailWord_2059249, baseEnd_2059249] using wordTrace_append hprefix tailTrace_2059249
  have hstable : (prefixWord ++ tailWord_2059249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059249).length < 2 ^ (prefixWord ++ tailWord_2059249).sum := by decide
  have hdescent : baseEnd_2059249 < baseStart_2059249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059266 : List Nat := [3, 4, 1, 3, 1, 2, 7]
def baseStart_2059266 : Nat := 118140960795 + 2059266 * 2 ^ 59
def prefixEnd_2059266 : Nat := 4983230072969 + 3 ^ 40 * 2059266 * 2
def baseEnd_2059266 : Nat := 52216950788229399802697

theorem tailTrace_2059266 : CollatzResearch.WordTrace tailWord_2059266 prefixEnd_2059266 52216950788229399802697 := by
  unfold tailWord_2059266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18776900339409612869517413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50071734238425634318713101 18776900339409612869517413)
  ·
    refine ⟨3520668813639302413034515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18776900339409612869517413 3520668813639302413034515)
    ·
      refine ⟨5281003220458953619551773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3520668813639302413034515 5281003220458953619551773)
      ·
        refine ⟨1980376207672107607331915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5281003220458953619551773 1980376207672107607331915)
        ·
          refine ⟨2970564311508161410997873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980376207672107607331915 2970564311508161410997873)
          ·
            refine ⟨2227923233631121058248405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2970564311508161410997873 2227923233631121058248405)
            ·
              refine ⟨52216950788229399802697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2227923233631121058248405 52216950788229399802697)
              ·
                rfl

theorem cell21_2059266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 7].length) (baseStart_2059266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059266 prefixEnd_2059266 := by exact prefixLift 2059266
  have htrace : WordTrace (prefixWord ++ tailWord_2059266) baseStart_2059266 baseEnd_2059266 := by
    simpa [prefixWord, tailWord_2059266, baseEnd_2059266] using wordTrace_append hprefix tailTrace_2059266
  have hstable : (prefixWord ++ tailWord_2059266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059266).length < 2 ^ (prefixWord ++ tailWord_2059266).sum := by decide
  have hdescent : baseEnd_2059266 < baseStart_2059266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059390 : List Nat := [4, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2059390 : Nat := 118140960795 + 2059390 * 2 ^ 59
def prefixEnd_2059390 : Nat := 4983230072969 + 3 ^ 40 * 2059390 * 2
def baseEnd_2059390 : Nat := 469980855583467938157353

theorem tailTrace_2059390 : CollatzResearch.WordTrace tailWord_2059390 prefixEnd_2059390 469980855583467938157353 := by
  unfold tailWord_2059390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9389015501148652581947953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50074749339459480437055749 9389015501148652581947953)
  ·
    refine ⟨7041761625861489436460965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9389015501148652581947953 7041761625861489436460965)
    ·
      refine ⟨1320330304849029269336431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7041761625861489436460965 1320330304849029269336431)
      ·
        refine ⟨1980495457273543904004647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1320330304849029269336431 1980495457273543904004647)
        ·
          refine ⟨2970743185910315856006971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980495457273543904004647 2970743185910315856006971)
          ·
            refine ⟨4456114778865473784010457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970743185910315856006971 4456114778865473784010457)
            ·
              refine ⟨3342086084149105338007843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4456114778865473784010457 3342086084149105338007843)
              ·
                refine ⟨5013129126223658007011765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3342086084149105338007843 5013129126223658007011765)
                ·
                  refine ⟨469980855583467938157353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5013129126223658007011765 469980855583467938157353)
                  ·
                    rfl

theorem cell21_2059390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2059390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059390 prefixEnd_2059390 := by exact prefixLift 2059390
  have htrace : WordTrace (prefixWord ++ tailWord_2059390) baseStart_2059390 baseEnd_2059390 := by
    simpa [prefixWord, tailWord_2059390, baseEnd_2059390] using wordTrace_append hprefix tailTrace_2059390
  have hstable : (prefixWord ++ tailWord_2059390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059390).length < 2 ^ (prefixWord ++ tailWord_2059390).sum := by decide
  have hdescent : baseEnd_2059390 < baseStart_2059390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059474 : List Nat := [3, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_2059474 : Nat := 118140960795 + 2059474 * 2 ^ 59
def prefixEnd_2059474 : Nat := 4983230072969 + 3 ^ 40 * 2059474 * 2
def baseEnd_2059474 : Nat := 470000025527902458757181

theorem tailTrace_2059474 : CollatzResearch.WordTrace tailWord_2059474 prefixEnd_2059474 470000025527902458757181 := by
  unfold tailWord_2059474
  simp only [CollatzResearch.WordTrace]
  refine ⟨18778796935221225750410369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50076791827256602001094317 18778796935221225750410369)
  ·
    refine ⟨14084097701415919312807777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18778796935221225750410369 14084097701415919312807777)
    ·
      refine ⟨10563073276061939484605833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14084097701415919312807777 10563073276061939484605833)
      ·
        refine ⟨7922304957046454613454375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10563073276061939484605833 7922304957046454613454375)
        ·
          refine ⟨11883457435569681920181563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7922304957046454613454375 11883457435569681920181563)
          ·
            refine ⟨17825186153354522880272345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11883457435569681920181563 17825186153354522880272345)
            ·
              refine ⟨13368889615015892160204259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17825186153354522880272345 13368889615015892160204259)
              ·
                refine ⟨20053334422523838240306389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13368889615015892160204259 20053334422523838240306389)
                ·
                  refine ⟨470000025527902458757181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20053334422523838240306389 470000025527902458757181)
                  ·
                    rfl

theorem cell21_2059474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_2059474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059474 prefixEnd_2059474 := by exact prefixLift 2059474
  have htrace : WordTrace (prefixWord ++ tailWord_2059474) baseStart_2059474 baseEnd_2059474 := by
    simpa [prefixWord, tailWord_2059474, baseEnd_2059474] using wordTrace_append hprefix tailTrace_2059474
  have hstable : (prefixWord ++ tailWord_2059474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059474).length < 2 ^ (prefixWord ++ tailWord_2059474).sum := by decide
  have hdescent : baseEnd_2059474 < baseStart_2059474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059519 : List Nat := [1, 1, 2, 2, 1, 5, 3, 6]
def baseStart_2059519 : Nat := 118140960795 + 2059519 * 2 ^ 59
def prefixEnd_2059519 : Nat := 4983230072969 + 3 ^ 40 * 2059519 * 2
def baseEnd_2059519 : Nat := 156670098380330793502363

theorem tailTrace_2059519 : CollatzResearch.WordTrace tailWord_2059519 prefixEnd_2059519 156670098380330793502363 := by
  unfold tailWord_2059519
  simp only [CollatzResearch.WordTrace]
  refine ⟨75116829025721875687029611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50077886017147917124686407 75116829025721875687029611)
  ·
    refine ⟨112675243538582813530544417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75116829025721875687029611 112675243538582813530544417)
    ·
      refine ⟨84506432653937110147908313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112675243538582813530544417 84506432653937110147908313)
      ·
        refine ⟨63379824490452832610931235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84506432653937110147908313 63379824490452832610931235)
        ·
          refine ⟨95069736735679248916396853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63379824490452832610931235 95069736735679248916396853)
          ·
            refine ⟨8912787818969929585912205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95069736735679248916396853 8912787818969929585912205)
            ·
              refine ⟨3342295432113723594717077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8912787818969929585912205 3342295432113723594717077)
              ·
                refine ⟨156670098380330793502363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3342295432113723594717077 156670098380330793502363)
                ·
                  rfl

theorem cell21_2059519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_2059519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059519 prefixEnd_2059519 := by exact prefixLift 2059519
  have htrace : WordTrace (prefixWord ++ tailWord_2059519) baseStart_2059519 baseEnd_2059519 := by
    simpa [prefixWord, tailWord_2059519, baseEnd_2059519] using wordTrace_append hprefix tailTrace_2059519
  have hstable : (prefixWord ++ tailWord_2059519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059519).length < 2 ^ (prefixWord ++ tailWord_2059519).sum := by decide
  have hdescent : baseEnd_2059519 < baseStart_2059519 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059609 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 7]
def baseStart_2059609 : Nat := 118140960795 + 2059609 * 2 ^ 59
def prefixEnd_2059609 : Nat := 4983230072969 + 3 ^ 40 * 2059609 * 2
def baseEnd_2059609 : Nat := 470030834367172224006905

theorem tailTrace_2059609 : CollatzResearch.WordTrace tailWord_2059609 prefixEnd_2059609 470030834367172224006905 := by
  unfold tailWord_2059609
  simp only [CollatzResearch.WordTrace]
  refine ⟨75120111595395821057805881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50080074396930547371870587 75120111595395821057805881)
  ·
    refine ⟨56340083696546865793354411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75120111595395821057805881 56340083696546865793354411)
    ·
      refine ⟨84510125544820298690031617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56340083696546865793354411 84510125544820298690031617)
      ·
        refine ⟨63382594158615224017523713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84510125544820298690031617 63382594158615224017523713)
        ·
          refine ⟨47536945618961418013142785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63382594158615224017523713 47536945618961418013142785)
          ·
            refine ⟨35652709214221063509857089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47536945618961418013142785 35652709214221063509857089)
            ·
              refine ⟨26739531910665797632392817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35652709214221063509857089 26739531910665797632392817)
              ·
                refine ⟨20054648932999348224294613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26739531910665797632392817 20054648932999348224294613)
                ·
                  refine ⟨470030834367172224006905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20054648932999348224294613 470030834367172224006905)
                  ·
                    rfl

theorem cell21_2059609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 7].length) (baseStart_2059609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059609 prefixEnd_2059609 := by exact prefixLift 2059609
  have htrace : WordTrace (prefixWord ++ tailWord_2059609) baseStart_2059609 baseEnd_2059609 := by
    simpa [prefixWord, tailWord_2059609, baseEnd_2059609] using wordTrace_append hprefix tailTrace_2059609
  have hstable : (prefixWord ++ tailWord_2059609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059609).length < 2 ^ (prefixWord ++ tailWord_2059609).sum := by decide
  have hdescent : baseEnd_2059609 < baseStart_2059609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059677 : List Nat := [1, 4, 2, 1, 3, 3, 2, 2, 3]
def baseStart_2059677 : Nat := 118140960795 + 2059677 * 2 ^ 59
def prefixEnd_2059677 : Nat := 4983230072969 + 3 ^ 40 * 2059677 * 2
def baseEnd_2059677 : Nat := 470046352893619216873433

theorem tailTrace_2059677 : CollatzResearch.WordTrace tailWord_2059677 prefixEnd_2059677 470046352893619216873433 := by
  unfold tailWord_2059677
  simp only [CollatzResearch.WordTrace]
  refine ⟨75122591759149468671281285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50081727839432979114187523 75122591759149468671281285)
  ·
    refine ⟨14085485954840525375865241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75122591759149468671281285 14085485954840525375865241)
    ·
      refine ⟨10564114466130394031898931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14085485954840525375865241 10564114466130394031898931)
      ·
        refine ⟨15846171699195591047848397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10564114466130394031898931 15846171699195591047848397)
        ·
          refine ⟨5942314387198346642943149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15846171699195591047848397 5942314387198346642943149)
          ·
            refine ⟨2228367895199379991103681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5942314387198346642943149 2228367895199379991103681)
            ·
              refine ⟨1671275921399534993327761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228367895199379991103681 1671275921399534993327761)
              ·
                refine ⟨1253456941049651244995821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671275921399534993327761 1253456941049651244995821)
                ·
                  refine ⟨470046352893619216873433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253456941049651244995821 470046352893619216873433)
                  ·
                    rfl

theorem cell21_2059677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_2059677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059677 prefixEnd_2059677 := by exact prefixLift 2059677
  have htrace : WordTrace (prefixWord ++ tailWord_2059677) baseStart_2059677 baseEnd_2059677 := by
    simpa [prefixWord, tailWord_2059677, baseEnd_2059677] using wordTrace_append hprefix tailTrace_2059677
  have hstable : (prefixWord ++ tailWord_2059677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059677).length < 2 ^ (prefixWord ++ tailWord_2059677).sum := by decide
  have hdescent : baseEnd_2059677 < baseStart_2059677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059719 : List Nat := [1, 1, 4, 1, 1, 3, 4, 3, 3]
def baseStart_2059719 : Nat := 118140960795 + 2059719 * 2 ^ 59
def prefixEnd_2059719 : Nat := 4983230072969 + 3 ^ 40 * 2059719 * 2
def baseEnd_2059719 : Nat := 470055937865836477173347

theorem tailTrace_2059719 : CollatzResearch.WordTrace tailWord_2059719 prefixEnd_2059719 470055937865836477173347 := by
  unfold tailWord_2059719
  simp only [CollatzResearch.WordTrace]
  refine ⟨75124123624997309844310211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50082749083331539896206807 75124123624997309844310211)
  ·
    refine ⟨112686185437495964766465317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75124123624997309844310211 112686185437495964766465317)
    ·
      refine ⟨21128659769530493393712247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112686185437495964766465317 21128659769530493393712247)
      ·
        refine ⟨31692989654295740090568371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21128659769530493393712247 31692989654295740090568371)
        ·
          refine ⟨47539484481443610135852557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31692989654295740090568371 47539484481443610135852557)
          ·
            refine ⟨17827306680541353800944709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47539484481443610135852557 17827306680541353800944709)
            ·
              refine ⟨3342620002601503837677133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17827306680541353800944709 3342620002601503837677133)
              ·
                refine ⟨1253482500975563939128925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3342620002601503837677133 1253482500975563939128925)
                ·
                  refine ⟨470055937865836477173347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253482500975563939128925 470055937865836477173347)
                  ·
                    rfl

theorem cell21_2059719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 3, 3].length) (baseStart_2059719 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059719 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059719 prefixEnd_2059719 := by exact prefixLift 2059719
  have htrace : WordTrace (prefixWord ++ tailWord_2059719) baseStart_2059719 baseEnd_2059719 := by
    simpa [prefixWord, tailWord_2059719, baseEnd_2059719] using wordTrace_append hprefix tailTrace_2059719
  have hstable : (prefixWord ++ tailWord_2059719).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059719).length < 2 ^ (prefixWord ++ tailWord_2059719).sum := by decide
  have hdescent : baseEnd_2059719 < baseStart_2059719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059809 : List Nat := [1, 2, 3, 2, 2, 3, 1, 3, 4]
def baseStart_2059809 : Nat := 118140960795 + 2059809 * 2 ^ 59
def prefixEnd_2059809 : Nat := 4983230072969 + 3 ^ 40 * 2059809 * 2
def baseEnd_2059809 : Nat := 470076477092016320673163

theorem tailTrace_2059809 : CollatzResearch.WordTrace tailWord_2059809 prefixEnd_2059809 470076477092016320673163 := by
  unfold tailWord_2059809
  simp only [CollatzResearch.WordTrace]
  refine ⟨75127406194671255215086481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50084937463114170143390987 75127406194671255215086481)
  ·
    refine ⟨56345554646003441411314861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75127406194671255215086481 56345554646003441411314861)
    ·
      refine ⟨21129582992251290529243073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56345554646003441411314861 21129582992251290529243073)
      ·
        refine ⟨15847187244188467896932305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21129582992251290529243073 15847187244188467896932305)
        ·
          refine ⟨11885390433141350922699229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15847187244188467896932305 11885390433141350922699229)
          ·
            refine ⟨4457021412428006596012211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11885390433141350922699229 4457021412428006596012211)
            ·
              refine ⟨6685532118642009894018317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4457021412428006596012211 6685532118642009894018317)
              ·
                refine ⟨2507074544490753710256869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6685532118642009894018317 2507074544490753710256869)
                ·
                  refine ⟨470076477092016320673163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507074544490753710256869 470076477092016320673163)
                  ·
                    rfl

theorem cell21_2059809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 3, 4].length) (baseStart_2059809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059809 prefixEnd_2059809 := by exact prefixLift 2059809
  have htrace : WordTrace (prefixWord ++ tailWord_2059809) baseStart_2059809 baseEnd_2059809 := by
    simpa [prefixWord, tailWord_2059809, baseEnd_2059809] using wordTrace_append hprefix tailTrace_2059809
  have hstable : (prefixWord ++ tailWord_2059809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059809).length < 2 ^ (prefixWord ++ tailWord_2059809).sum := by decide
  have hdescent : baseEnd_2059809 < baseStart_2059809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059913 : List Nat := [1, 2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_2059913 : Nat := 118140960795 + 2059913 * 2 ^ 59
def prefixEnd_2059913 : Nat := 4983230072969 + 3 ^ 40 * 2059913 * 2
def baseEnd_2059913 : Nat := 470100211308935250939617

theorem tailTrace_2059913 : CollatzResearch.WordTrace tailWord_2059913 prefixEnd_2059913 470100211308935250939617 := by
  unfold tailWord_2059913
  simp only [CollatzResearch.WordTrace]
  refine ⟨75131199386294480976872393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50087466257529653984581595 75131199386294480976872393)
  ·
    refine ⟨56348399539720860732654295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75131199386294480976872393 56348399539720860732654295)
    ·
      refine ⟨84522599309581291098981443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56348399539720860732654295 84522599309581291098981443)
      ·
        refine ⟨126783898964371936648472165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84522599309581291098981443 126783898964371936648472165)
        ·
          refine ⟨23771981055819738121588531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 126783898964371936648472165 23771981055819738121588531)
          ·
            refine ⟨35657971583729607182382797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23771981055819738121588531 35657971583729607182382797)
            ·
              refine ⟨13371739343898602693393549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35657971583729607182382797 13371739343898602693393549)
              ·
                refine ⟨5014402253961976010022581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13371739343898602693393549 5014402253961976010022581)
                ·
                  refine ⟨470100211308935250939617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014402253961976010022581 470100211308935250939617)
                  ·
                    rfl

theorem cell21_2059913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_2059913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059913 prefixEnd_2059913 := by exact prefixLift 2059913
  have htrace : WordTrace (prefixWord ++ tailWord_2059913) baseStart_2059913 baseEnd_2059913 := by
    simpa [prefixWord, tailWord_2059913, baseEnd_2059913] using wordTrace_append hprefix tailTrace_2059913
  have hstable : (prefixWord ++ tailWord_2059913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059913).length < 2 ^ (prefixWord ++ tailWord_2059913).sum := by decide
  have hdescent : baseEnd_2059913 < baseStart_2059913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059964 : List Nat := [2, 2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_2059964 : Nat := 118140960795 + 2059964 * 2 ^ 59
def prefixEnd_2059964 : Nat := 4983230072969 + 3 ^ 40 * 2059964 * 2
def baseEnd_2059964 : Nat := 470111850203770495589513

theorem tailTrace_2059964 : CollatzResearch.WordTrace tailWord_2059964 prefixEnd_2059964 470111850203770495589513 := by
  unfold tailWord_2059964
  simp only [CollatzResearch.WordTrace]
  refine ⟨37566529754554858343489473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50088706339406477791319297 37566529754554858343489473)
  ·
    refine ⟨28174897315916143757617105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37566529754554858343489473 28174897315916143757617105)
    ·
      refine ⟨21131172986937107818212829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28174897315916143757617105 21131172986937107818212829)
      ·
        refine ⟨7924189870101415431829811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21131172986937107818212829 7924189870101415431829811)
        ·
          refine ⟨11886284805152123147744717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7924189870101415431829811 11886284805152123147744717)
          ·
            refine ⟨4457356801932046180404269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11886284805152123147744717 4457356801932046180404269)
            ·
              refine ⟨1671508800724517317651601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4457356801932046180404269 1671508800724517317651601)
              ·
                refine ⟨1253631600543387988238701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671508800724517317651601 1253631600543387988238701)
                ·
                  refine ⟨470111850203770495589513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253631600543387988238701 470111850203770495589513)
                  ·
                    rfl

theorem cell21_2059964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_2059964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059964 prefixEnd_2059964 := by exact prefixLift 2059964
  have htrace : WordTrace (prefixWord ++ tailWord_2059964) baseStart_2059964 baseEnd_2059964 := by
    simpa [prefixWord, tailWord_2059964, baseEnd_2059964] using wordTrace_append hprefix tailTrace_2059964
  have hstable : (prefixWord ++ tailWord_2059964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059964).length < 2 ^ (prefixWord ++ tailWord_2059964).sum := by decide
  have hdescent : baseEnd_2059964 < baseStart_2059964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2059970 : List Nat := [3, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_2059970 : Nat := 118140960795 + 2059970 * 2 ^ 59
def prefixEnd_2059970 : Nat := 4983230072969 + 3 ^ 40 * 2059970 * 2
def baseEnd_2059970 : Nat := 470113219485515818489501

theorem tailTrace_2059970 : CollatzResearch.WordTrace tailWord_2059970 prefixEnd_2059970 470113219485515818489501 := by
  unfold tailWord_2059970
  simp only [CollatzResearch.WordTrace]
  refine ⟨18783319586771994927924341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50088852231391986474464909 18783319586771994927924341)
  ·
    refine ⟨1760936211259874524492907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18783319586771994927924341 1760936211259874524492907)
    ·
      refine ⟨2641404316889811786739361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760936211259874524492907 2641404316889811786739361)
      ·
        refine ⟨1981053237667358840054521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2641404316889811786739361 1981053237667358840054521)
        ·
          refine ⟨1485789928250519130040891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1981053237667358840054521 1485789928250519130040891)
          ·
            refine ⟨2228684892375778695061337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1485789928250519130040891 2228684892375778695061337)
            ·
              refine ⟨1671513669281834021296003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228684892375778695061337 1671513669281834021296003)
              ·
                refine ⟨2507270503922751031944005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671513669281834021296003 2507270503922751031944005)
                ·
                  refine ⟨470113219485515818489501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507270503922751031944005 470113219485515818489501)
                  ·
                    rfl

theorem cell21_2059970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_2059970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2059970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2059970 prefixEnd_2059970 := by exact prefixLift 2059970
  have htrace : WordTrace (prefixWord ++ tailWord_2059970) baseStart_2059970 baseEnd_2059970 := by
    simpa [prefixWord, tailWord_2059970, baseEnd_2059970] using wordTrace_append hprefix tailTrace_2059970
  have hstable : (prefixWord ++ tailWord_2059970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2059970).length < 2 ^ (prefixWord ++ tailWord_2059970).sum := by decide
  have hdescent : baseEnd_2059970 < baseStart_2059970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2059970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060023 : List Nat := [1, 1, 3, 1, 1, 1, 8, 2, 3]
def baseStart_2060023 : Nat := 118140960795 + 2060023 * 2 ^ 59
def prefixEnd_2060023 : Nat := 4983230072969 + 3 ^ 40 * 2060023 * 2
def baseEnd_2060023 : Nat := 470125314807599504106059

theorem tailTrace_2060023 : CollatzResearch.WordTrace tailWord_2060023 prefixEnd_2060023 470125314807599504106059 := by
  unfold tailWord_2060023
  simp only [CollatzResearch.WordTrace]
  refine ⟨75135211415895969763376723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50090140943930646508917815 75135211415895969763376723)
  ·
    refine ⟨112702817123843954645065085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75135211415895969763376723 112702817123843954645065085)
    ·
      refine ⟨42263556421441482991899407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112702817123843954645065085 42263556421441482991899407)
      ·
        refine ⟨63395334632162224487849111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42263556421441482991899407 63395334632162224487849111)
        ·
          refine ⟨95093001948243336731773667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63395334632162224487849111 95093001948243336731773667)
          ·
            refine ⟨142639502922365005097660501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95093001948243336731773667 142639502922365005097660501)
            ·
              refine ⟨1671556674871464903488209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 142639502922365005097660501 1671556674871464903488209)
              ·
                refine ⟨1253667506153598677616157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1671556674871464903488209 1253667506153598677616157)
                ·
                  refine ⟨470125314807599504106059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253667506153598677616157 470125314807599504106059)
                  ·
                    rfl

theorem cell21_2060023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 8, 2, 3].length) (baseStart_2060023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060023 prefixEnd_2060023 := by exact prefixLift 2060023
  have htrace : WordTrace (prefixWord ++ tailWord_2060023) baseStart_2060023 baseEnd_2060023 := by
    simpa [prefixWord, tailWord_2060023, baseEnd_2060023] using wordTrace_append hprefix tailTrace_2060023
  have hstable : (prefixWord ++ tailWord_2060023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060023).length < 2 ^ (prefixWord ++ tailWord_2060023).sum := by decide
  have hdescent : baseEnd_2060023 < baseStart_2060023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060079 : List Nat := [1, 1, 2, 1, 2, 1, 2, 5, 6]
def baseStart_2060079 : Nat := 118140960795 + 2060079 * 2 ^ 59
def prefixEnd_2060079 : Nat := 4983230072969 + 3 ^ 40 * 2060079 * 2
def baseEnd_2060079 : Nat := 470138094770555851172611

theorem tailTrace_2060079 : CollatzResearch.WordTrace tailWord_2060079 prefixEnd_2060079 470138094770555851172611 := by
  unfold tailWord_2060079
  simp only [CollatzResearch.WordTrace]
  refine ⟨75137253903693091327415291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50091502602462060884943527 75137253903693091327415291)
  ·
    refine ⟨112705880855539636991122937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75137253903693091327415291 112705880855539636991122937)
    ·
      refine ⟨84529410641654727743342203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112705880855539636991122937 84529410641654727743342203)
      ·
        refine ⟨126794115962482091615013305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84529410641654727743342203 126794115962482091615013305)
        ·
          refine ⟨95095586971861568711259979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126794115962482091615013305 95095586971861568711259979)
          ·
            refine ⟨142643380457792353066889969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95095586971861568711259979 142643380457792353066889969)
            ·
              refine ⟨106982535343344264800167477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142643380457792353066889969 106982535343344264800167477)
              ·
                refine ⟨10029612688438524825015701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106982535343344264800167477 10029612688438524825015701)
                ·
                  refine ⟨470138094770555851172611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10029612688438524825015701 470138094770555851172611)
                  ·
                    rfl

theorem cell21_2060079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_2060079 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060079 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060079 prefixEnd_2060079 := by exact prefixLift 2060079
  have htrace : WordTrace (prefixWord ++ tailWord_2060079) baseStart_2060079 baseEnd_2060079 := by
    simpa [prefixWord, tailWord_2060079, baseEnd_2060079] using wordTrace_append hprefix tailTrace_2060079
  have hstable : (prefixWord ++ tailWord_2060079).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060079).length < 2 ^ (prefixWord ++ tailWord_2060079).sum := by decide
  have hdescent : baseEnd_2060079 < baseStart_2060079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060082 : List Nat := [3, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_2060082 : Nat := 118140960795 + 2060082 * 2 ^ 59
def prefixEnd_2060082 : Nat := 4983230072969 + 3 ^ 40 * 2060082 * 2
def baseEnd_2060082 : Nat := 470138779411428512622605

theorem tailTrace_2060082 : CollatzResearch.WordTrace tailWord_2060082 prefixEnd_2060082 470138779411428512622605 := by
  unfold tailWord_2060082
  simp only [CollatzResearch.WordTrace]
  refine ⟨18784340830670555709943625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50091575548454815226516333 18784340830670555709943625)
  ·
    refine ⟨14088255623002916782457719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18784340830670555709943625 14088255623002916782457719)
    ·
      refine ⟨21132383434504375173686579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14088255623002916782457719 21132383434504375173686579)
      ·
        refine ⟨31698575151756562760529869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21132383434504375173686579 31698575151756562760529869)
        ·
          refine ⟨11886965681908711035198701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31698575151756562760529869 11886965681908711035198701)
          ·
            refine ⟨4457612130715766638199513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11886965681908711035198701 4457612130715766638199513)
            ·
              refine ⟨3343209098036824978649635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457612130715766638199513 3343209098036824978649635)
              ·
                refine ⟨5014813647055237467974453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3343209098036824978649635 5014813647055237467974453)
                ·
                  refine ⟨470138779411428512622605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5014813647055237467974453 470138779411428512622605)
                  ·
                    rfl

theorem cell21_2060082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_2060082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060082 prefixEnd_2060082 := by exact prefixLift 2060082
  have htrace : WordTrace (prefixWord ++ tailWord_2060082) baseStart_2060082 baseEnd_2060082 := by
    simpa [prefixWord, tailWord_2060082, baseEnd_2060082] using wordTrace_append hprefix tailTrace_2060082
  have hstable : (prefixWord ++ tailWord_2060082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060082).length < 2 ^ (prefixWord ++ tailWord_2060082).sum := by decide
  have hdescent : baseEnd_2060082 < baseStart_2060082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060102 : List Nat := [6, 1, 1, 2, 1, 3, 2, 5]
def baseStart_2060102 : Nat := 118140960795 + 2060102 * 2 ^ 59
def prefixEnd_2060102 : Nat := 4983230072969 + 3 ^ 40 * 2060102 * 2
def baseEnd_2060102 : Nat := 156714447894637640763077

theorem tailTrace_2060102 : CollatzResearch.WordTrace tailWord_2060102 prefixEnd_2060102 156714447894637640763077 := by
  unfold tailWord_2060102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348065399456555195484455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50092061855073177503668373 2348065399456555195484455)
  ·
    refine ⟨3522098099184832793226683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2348065399456555195484455 3522098099184832793226683)
    ·
      refine ⟨5283147148777249189840025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522098099184832793226683 5283147148777249189840025)
      ·
        refine ⟨3962360361582936892380019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5283147148777249189840025 3962360361582936892380019)
        ·
          refine ⟨5943540542374405338570029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3962360361582936892380019 5943540542374405338570029)
          ·
            refine ⟨2228827703390402001963761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5943540542374405338570029 2228827703390402001963761)
            ·
              refine ⟨1671620777542801501472821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2228827703390402001963761 1671620777542801501472821)
              ·
                refine ⟨156714447894637640763077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1671620777542801501472821 156714447894637640763077)
                ·
                  rfl

theorem cell21_2060102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_2060102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060102 prefixEnd_2060102 := by exact prefixLift 2060102
  have htrace : WordTrace (prefixWord ++ tailWord_2060102) baseStart_2060102 baseEnd_2060102 := by
    simpa [prefixWord, tailWord_2060102, baseEnd_2060102] using wordTrace_append hprefix tailTrace_2060102
  have hstable : (prefixWord ++ tailWord_2060102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060102).length < 2 ^ (prefixWord ++ tailWord_2060102).sum := by decide
  have hdescent : baseEnd_2060102 < baseStart_2060102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060116 : List Nat := [2, 4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_2060116 : Nat := 118140960795 + 2060116 * 2 ^ 59
def prefixEnd_2060116 : Nat := 4983230072969 + 3 ^ 40 * 2060116 * 2
def baseEnd_2060116 : Nat := 470146538674652009055869

theorem tailTrace_2060116 : CollatzResearch.WordTrace tailWord_2060116 prefixEnd_2060116 470146538674652009055869 := by
  unfold tailWord_2060116
  simp only [CollatzResearch.WordTrace]
  refine ⟨37569301702279523323256101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50092402269706031097674801 37569301702279523323256101)
  ·
    refine ⟨7044244069177410623110519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37569301702279523323256101 7044244069177410623110519)
    ·
      refine ⟨10566366103766115934665779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7044244069177410623110519 10566366103766115934665779)
      ·
        refine ⟨15849549155649173901998669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566366103766115934665779 15849549155649173901998669)
        ·
          refine ⟨5943580933368440213249501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15849549155649173901998669 5943580933368440213249501)
          ·
            refine ⟨2228842850013165079968563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5943580933368440213249501 2228842850013165079968563)
            ·
              refine ⟨3343264275019747619952845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2228842850013165079968563 3343264275019747619952845)
              ·
                refine ⟨1253724103132405357482317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3343264275019747619952845 1253724103132405357482317)
                ·
                  refine ⟨470146538674652009055869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253724103132405357482317 470146538674652009055869)
                  ·
                    rfl

theorem cell21_2060116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_2060116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060116 prefixEnd_2060116 := by exact prefixLift 2060116
  have htrace : WordTrace (prefixWord ++ tailWord_2060116) baseStart_2060116 baseEnd_2060116 := by
    simpa [prefixWord, tailWord_2060116, baseEnd_2060116] using wordTrace_append hprefix tailTrace_2060116
  have hstable : (prefixWord ++ tailWord_2060116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060116).length < 2 ^ (prefixWord ++ tailWord_2060116).sum := by decide
  have hdescent : baseEnd_2060116 < baseStart_2060116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060186 : List Nat := [3, 1, 1, 4, 2, 10]
def baseStart_2060186 : Nat := 118140960795 + 2060186 * 2 ^ 59
def prefixEnd_2060186 : Nat := 4983230072969 + 3 ^ 40 * 2060186 * 2
def baseEnd_2060186 : Nat := 17413426430679534921817

theorem tailTrace_2060186 : CollatzResearch.WordTrace tailWord_2060186 prefixEnd_2060186 17413426430679534921817 := by
  unfold tailWord_2060186
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785289128576362150390103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50094104342870299067706941 18785289128576362150390103)
  ·
    refine ⟨28177933692864543225585155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18785289128576362150390103 28177933692864543225585155)
    ·
      refine ⟨42266900539296814838377733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28177933692864543225585155 42266900539296814838377733)
      ·
        refine ⟨7925043851118152782195825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42266900539296814838377733 7925043851118152782195825)
        ·
          refine ⟨5943782888338614586646869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7925043851118152782195825 5943782888338614586646869)
          ·
            refine ⟨17413426430679534921817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5943782888338614586646869 17413426430679534921817)
            ·
              rfl

theorem cell21_2060186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 10].length) (baseStart_2060186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060186 prefixEnd_2060186 := by exact prefixLift 2060186
  have htrace : WordTrace (prefixWord ++ tailWord_2060186) baseStart_2060186 baseEnd_2060186 := by
    simpa [prefixWord, tailWord_2060186, baseEnd_2060186] using wordTrace_append hprefix tailTrace_2060186
  have hstable : (prefixWord ++ tailWord_2060186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060186).length < 2 ^ (prefixWord ++ tailWord_2060186).sum := by decide
  have hdescent : baseEnd_2060186 < baseStart_2060186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060189 : List Nat := [1, 4, 2, 1, 2, 3, 2, 2, 4]
def baseStart_2060189 : Nat := 118140960795 + 2060189 * 2 ^ 59
def prefixEnd_2060189 : Nat := 4983230072969 + 3 ^ 40 * 2060189 * 2
def baseEnd_2060189 : Nat := 470163198269220104339053

theorem tailTrace_2060189 : CollatzResearch.WordTrace tailWord_2060189 prefixEnd_2060189 470163198269220104339053 := by
  unfold tailWord_2060189
  simp only [CollatzResearch.WordTrace]
  refine ⟨75141265933294580113919621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50094177288863053409279747 75141265933294580113919621)
  ·
    refine ⟨14088987362492733771359929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75141265933294580113919621 14088987362492733771359929)
    ·
      refine ⟨10566740521869550328519947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14088987362492733771359929 10566740521869550328519947)
      ·
        refine ⟨15850110782804325492779921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566740521869550328519947 15850110782804325492779921)
        ·
          refine ⟨11887583087103244119584941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15850110782804325492779921 11887583087103244119584941)
          ·
            refine ⟨4457843657663716544844353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11887583087103244119584941 4457843657663716544844353)
            ·
              refine ⟨3343382743247787408633265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457843657663716544844353 3343382743247787408633265)
              ·
                refine ⟨2507537057435840556474949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343382743247787408633265 2507537057435840556474949)
                ·
                  refine ⟨470163198269220104339053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507537057435840556474949 470163198269220104339053)
                  ·
                    rfl

theorem cell21_2060189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_2060189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060189 prefixEnd_2060189 := by exact prefixLift 2060189
  have htrace : WordTrace (prefixWord ++ tailWord_2060189) baseStart_2060189 baseEnd_2060189 := by
    simpa [prefixWord, tailWord_2060189, baseEnd_2060189] using wordTrace_append hprefix tailTrace_2060189
  have hstable : (prefixWord ++ tailWord_2060189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060189).length < 2 ^ (prefixWord ++ tailWord_2060189).sum := by decide
  have hdescent : baseEnd_2060189 < baseStart_2060189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060217 : List Nat := [1, 2, 1, 4, 2, 1, 3, 2, 5]
def baseStart_2060217 : Nat := 118140960795 + 2060217 * 2 ^ 59
def prefixEnd_2060217 : Nat := 4983230072969 + 3 ^ 40 * 2060217 * 2
def baseEnd_2060217 : Nat := 470169588250698277872329

theorem tailTrace_2060217 : CollatzResearch.WordTrace tailWord_2060217 prefixEnd_2060217 470169588250698277872329 := by
  unfold tailWord_2060217
  simp only [CollatzResearch.WordTrace]
  refine ⟨75142287177193140895938905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50094858118128760597292603 75142287177193140895938905)
  ·
    refine ⟨56356715382894855671954179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75142287177193140895938905 56356715382894855671954179)
    ·
      refine ⟨84535073074342283507931269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56356715382894855671954179 84535073074342283507931269)
      ·
        refine ⟨15850326201439178157737113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84535073074342283507931269 15850326201439178157737113)
        ·
          refine ⟨11887744651079383618302835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15850326201439178157737113 11887744651079383618302835)
          ·
            refine ⟨17831616976619075427454253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11887744651079383618302835 17831616976619075427454253)
            ·
              refine ⟨6686856366232153285295345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17831616976619075427454253 6686856366232153285295345)
              ·
                refine ⟨5015142274674114963971509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6686856366232153285295345 5015142274674114963971509)
                ·
                  refine ⟨470169588250698277872329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5015142274674114963971509 470169588250698277872329)
                  ·
                    rfl

theorem cell21_2060217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 2, 5].length) (baseStart_2060217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060217 prefixEnd_2060217 := by exact prefixLift 2060217
  have htrace : WordTrace (prefixWord ++ tailWord_2060217) baseStart_2060217 baseEnd_2060217 := by
    simpa [prefixWord, tailWord_2060217, baseEnd_2060217] using wordTrace_append hprefix tailTrace_2060217
  have hstable : (prefixWord ++ tailWord_2060217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060217).length < 2 ^ (prefixWord ++ tailWord_2060217).sum := by decide
  have hdescent : baseEnd_2060217 < baseStart_2060217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060231 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_2060231 : Nat := 118140960795 + 2060231 * 2 ^ 59
def prefixEnd_2060231 : Nat := 4983230072969 + 3 ^ 40 * 2060231 * 2
def baseEnd_2060231 : Nat := 470172783241437364638967

theorem tailTrace_2060231 : CollatzResearch.WordTrace tailWord_2060231 prefixEnd_2060231 470172783241437364638967 := by
  unfold tailWord_2060231
  simp only [CollatzResearch.WordTrace]
  refine ⟨75142797799142421286948547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50095198532761614191299031 75142797799142421286948547)
  ·
    refine ⟨112714196698713631930422821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75142797799142421286948547 112714196698713631930422821)
    ·
      refine ⟨21133911881008805986954279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 112714196698713631930422821 21133911881008805986954279)
      ·
        refine ⟨31700867821513208980431419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21133911881008805986954279 31700867821513208980431419)
        ·
          refine ⟨47551301732269813470647129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31700867821513208980431419 47551301732269813470647129)
          ·
            refine ⟨35663476299202360102985347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47551301732269813470647129 35663476299202360102985347)
            ·
              refine ⟨53495214448803540154478021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35663476299202360102985347 53495214448803540154478021)
              ·
                refine ⟨10030352709150663778964629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53495214448803540154478021 10030352709150663778964629)
                ·
                  refine ⟨470172783241437364638967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10030352709150663778964629 470172783241437364638967)
                  ·
                    rfl

theorem cell21_2060231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_2060231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060231 prefixEnd_2060231 := by exact prefixLift 2060231
  have htrace : WordTrace (prefixWord ++ tailWord_2060231) baseStart_2060231 baseEnd_2060231 := by
    simpa [prefixWord, tailWord_2060231, baseEnd_2060231] using wordTrace_append hprefix tailTrace_2060231
  have hstable : (prefixWord ++ tailWord_2060231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060231).length < 2 ^ (prefixWord ++ tailWord_2060231).sum := by decide
  have hdescent : baseEnd_2060231 < baseStart_2060231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060234 : List Nat := [3, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_2060234 : Nat := 118140960795 + 2060234 * 2 ^ 59
def prefixEnd_2060234 : Nat := 4983230072969 + 3 ^ 40 * 2060234 * 2
def baseEnd_2060234 : Nat := 470173467882310026088961

theorem tailTrace_2060234 : CollatzResearch.WordTrace tailWord_2060234 prefixEnd_2060234 470173467882310026088961 := by
  unfold tailWord_2060234
  simp only [CollatzResearch.WordTrace]
  refine ⟨18785726804532888199826939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50095271478754368532871837 18785726804532888199826939)
  ·
    refine ⟨28178590206799332299740409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18785726804532888199826939 28178590206799332299740409)
    ·
      refine ⟨21133942655099499224805307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28178590206799332299740409 21133942655099499224805307)
      ·
        refine ⟨31700913982649248837207961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21133942655099499224805307 31700913982649248837207961)
        ·
          refine ⟨23775685486986936627905971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31700913982649248837207961 23775685486986936627905971)
          ·
            refine ⟨35663528230480404941858957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23775685486986936627905971 35663528230480404941858957)
            ·
              refine ⟨13373823086430151853197109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35663528230480404941858957 13373823086430151853197109)
              ·
                refine ⟨1253795914352826736237229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13373823086430151853197109 1253795914352826736237229)
                ·
                  refine ⟨470173467882310026088961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253795914352826736237229 470173467882310026088961)
                  ·
                    rfl

theorem cell21_2060234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_2060234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060234 prefixEnd_2060234 := by exact prefixLift 2060234
  have htrace : WordTrace (prefixWord ++ tailWord_2060234) baseStart_2060234 baseEnd_2060234 := by
    simpa [prefixWord, tailWord_2060234, baseEnd_2060234] using wordTrace_append hprefix tailTrace_2060234
  have hstable : (prefixWord ++ tailWord_2060234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060234).length < 2 ^ (prefixWord ++ tailWord_2060234).sum := by decide
  have hdescent : baseEnd_2060234 < baseStart_2060234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060307 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 6]
def baseStart_2060307 : Nat := 118140960795 + 2060307 * 2 ^ 59
def prefixEnd_2060307 : Nat := 4983230072969 + 3 ^ 40 * 2060307 * 2
def baseEnd_2060307 : Nat := 470190127476878121372145

theorem tailTrace_2060307 : CollatzResearch.WordTrace tailWord_2060307 prefixEnd_2060307 470190127476878121372145 := by
  unfold tailWord_2060307
  simp only [CollatzResearch.WordTrace]
  refine ⟨75145569746867086266715175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50097046497911390844476783 75145569746867086266715175)
  ·
    refine ⟨112718354620300629400072763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75145569746867086266715175 112718354620300629400072763)
    ·
      refine ⟨169077531930450944100109145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112718354620300629400072763 169077531930450944100109145)
      ·
        refine ⟨126808148947838208075081859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169077531930450944100109145 126808148947838208075081859)
        ·
          refine ⟨190212223421757312112622789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126808148947838208075081859 190212223421757312112622789)
          ·
            refine ⟨35664791891579496021116773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190212223421757312112622789 35664791891579496021116773)
            ·
              refine ⟨6687148479671155503959395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35664791891579496021116773 6687148479671155503959395)
              ·
                refine ⟨10030722719506733255939093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6687148479671155503959395 10030722719506733255939093)
                ·
                  refine ⟨470190127476878121372145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10030722719506733255939093 470190127476878121372145)
                  ·
                    rfl

theorem cell21_2060307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_2060307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060307 prefixEnd_2060307 := by exact prefixLift 2060307
  have htrace : WordTrace (prefixWord ++ tailWord_2060307) baseStart_2060307 baseEnd_2060307 := by
    simpa [prefixWord, tailWord_2060307, baseEnd_2060307] using wordTrace_append hprefix tailTrace_2060307
  have hstable : (prefixWord ++ tailWord_2060307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060307).length < 2 ^ (prefixWord ++ tailWord_2060307).sum := by decide
  have hdescent : baseEnd_2060307 < baseStart_2060307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060338 : List Nat := [3, 2, 1, 1, 2, 3, 2, 7]
def baseStart_2060338 : Nat := 118140960795 + 2060338 * 2 ^ 59
def prefixEnd_2060338 : Nat := 4983230072969 + 3 ^ 40 * 2060338 * 2
def baseEnd_2060338 : Nat := 156732400699742985451805

theorem tailTrace_2060338 : CollatzResearch.WordTrace tailWord_2060338 prefixEnd_2060338 156732400699742985451805 := by
  unfold tailWord_2060338
  simp only [CollatzResearch.WordTrace]
  refine ⟨18786675102438694640273417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50097800273169852374062445 18786675102438694640273417)
  ·
    refine ⟨14090006326829020980205063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18786675102438694640273417 14090006326829020980205063)
    ·
      refine ⟨21135009490243531470307595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14090006326829020980205063 21135009490243531470307595)
      ·
        refine ⟨31702514235365297205461393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21135009490243531470307595 31702514235365297205461393)
        ·
          refine ⟨23776885676523972904096045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31702514235365297205461393 23776885676523972904096045)
          ·
            refine ⟨8916332128696489839036017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23776885676523972904096045 8916332128696489839036017)
            ·
              refine ⟨6687249096522367379277013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8916332128696489839036017 6687249096522367379277013)
              ·
                refine ⟨156732400699742985451805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6687249096522367379277013 156732400699742985451805)
                ·
                  rfl

theorem cell21_2060338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_2060338 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060338 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060338 prefixEnd_2060338 := by exact prefixLift 2060338
  have htrace : WordTrace (prefixWord ++ tailWord_2060338) baseStart_2060338 baseEnd_2060338 := by
    simpa [prefixWord, tailWord_2060338, baseEnd_2060338] using wordTrace_append hprefix tailTrace_2060338
  have hstable : (prefixWord ++ tailWord_2060338).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060338).length < 2 ^ (prefixWord ++ tailWord_2060338).sum := by decide
  have hdescent : baseEnd_2060338 < baseStart_2060338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060358 : List Nat := [6, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2060358 : Nat := 118140960795 + 2060358 * 2 ^ 59
def prefixEnd_2060358 : Nat := 4983230072969 + 3 ^ 40 * 2060358 * 2
def baseEnd_2060358 : Nat := 470201766371713366022041

theorem tailTrace_2060358 : CollatzResearch.WordTrace tailWord_2060358 prefixEnd_2060358 470201766371713366022041 := by
  unfold tailWord_2060358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348357183427572561775679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50098286579788214651214485 2348357183427572561775679)
  ·
    refine ⟨3522535775141358842663519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2348357183427572561775679 3522535775141358842663519)
    ·
      refine ⟨5283803662712038263995279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3522535775141358842663519 5283803662712038263995279)
      ·
        refine ⟨7925705494068057395992919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5283803662712038263995279 7925705494068057395992919)
        ·
          refine ⟨11888558241102086093989379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7925705494068057395992919 11888558241102086093989379)
          ·
            refine ⟨17832837361653129140984069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11888558241102086093989379 17832837361653129140984069)
            ·
              refine ⟨3343657005309961713934513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17832837361653129140984069 3343657005309961713934513)
              ·
                refine ⟨2507742753982471285450885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343657005309961713934513 2507742753982471285450885)
                ·
                  refine ⟨470201766371713366022041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507742753982471285450885 470201766371713366022041)
                  ·
                    rfl

theorem cell21_2060358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2060358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060358 prefixEnd_2060358 := by exact prefixLift 2060358
  have htrace : WordTrace (prefixWord ++ tailWord_2060358) baseStart_2060358 baseEnd_2060358 := by
    simpa [prefixWord, tailWord_2060358, baseEnd_2060358] using wordTrace_append hprefix tailTrace_2060358
  have hstable : (prefixWord ++ tailWord_2060358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060358).length < 2 ^ (prefixWord ++ tailWord_2060358).sum := by decide
  have hdescent : baseEnd_2060358 < baseStart_2060358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060445 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 5]
def baseStart_2060445 : Nat := 118140960795 + 2060445 * 2 ^ 59
def prefixEnd_2060445 : Nat := 4983230072969 + 3 ^ 40 * 2060445 * 2
def baseEnd_2060445 : Nat := 470221620957020548071863

theorem tailTrace_2060445 : CollatzResearch.WordTrace tailWord_2060445 prefixEnd_2060445 470221620957020548071863 := by
  unfold tailWord_2060445
  simp only [CollatzResearch.WordTrace]
  refine ⟨75150603020367135835238789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50100402013578090556825859 75150603020367135835238789)
  ·
    refine ⟨14090738066318837969107273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75150603020367135835238789 14090738066318837969107273)
    ·
      refine ⟨10568053549739128476830455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14090738066318837969107273 10568053549739128476830455)
      ·
        refine ⟨15852080324608692715245683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10568053549739128476830455 15852080324608692715245683)
        ·
          refine ⟨23778120486913039072868525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15852080324608692715245683 23778120486913039072868525)
          ·
            refine ⟨8916795182592389652325697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23778120486913039072868525 8916795182592389652325697)
            ·
              refine ⟨6687596386944292239244273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8916795182592389652325697 6687596386944292239244273)
              ·
                refine ⟨5015697290208219179433205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6687596386944292239244273 5015697290208219179433205)
                ·
                  refine ⟨470221620957020548071863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5015697290208219179433205 470221620957020548071863)
                  ·
                    rfl

theorem cell21_2060445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_2060445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060445 prefixEnd_2060445 := by exact prefixLift 2060445
  have htrace : WordTrace (prefixWord ++ tailWord_2060445) baseStart_2060445 baseEnd_2060445 := by
    simpa [prefixWord, tailWord_2060445, baseEnd_2060445] using wordTrace_append hprefix tailTrace_2060445
  have hstable : (prefixWord ++ tailWord_2060445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060445).length < 2 ^ (prefixWord ++ tailWord_2060445).sum := by decide
  have hdescent : baseEnd_2060445 < baseStart_2060445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060490 : List Nat := [3, 1, 2, 1, 3, 1, 4, 6]
def baseStart_2060490 : Nat := 118140960795 + 2060490 * 2 ^ 59
def prefixEnd_2060490 : Nat := 4983230072969 + 3 ^ 40 * 2060490 * 2
def baseEnd_2060490 : Nat := 156743963523370156607257

theorem tailTrace_2060490 : CollatzResearch.WordTrace tailWord_2060490 prefixEnd_2060490 156743963523370156607257 := by
  unfold tailWord_2060490
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788061076301027130156731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50101496203469405680417949 18788061076301027130156731)
  ·
    refine ⟨28182091614451540695235097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18788061076301027130156731 28182091614451540695235097)
    ·
      refine ⟨21136568710838655521426323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28182091614451540695235097 21136568710838655521426323)
      ·
        refine ⟨31704853066257983282139485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21136568710838655521426323 31704853066257983282139485)
        ·
          refine ⟨11889319899846743730802307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31704853066257983282139485 11889319899846743730802307)
          ·
            refine ⟨17833979849770115596203461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889319899846743730802307 17833979849770115596203461)
            ·
              refine ⟨3343871221831896674288149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17833979849770115596203461 3343871221831896674288149)
              ·
                refine ⟨156743963523370156607257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3343871221831896674288149 156743963523370156607257)
                ·
                  rfl

theorem cell21_2060490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_2060490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060490 prefixEnd_2060490 := by exact prefixLift 2060490
  have htrace : WordTrace (prefixWord ++ tailWord_2060490) baseStart_2060490 baseEnd_2060490 := by
    simpa [prefixWord, tailWord_2060490, baseEnd_2060490] using wordTrace_append hprefix tailTrace_2060490
  have hstable : (prefixWord ++ tailWord_2060490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060490).length < 2 ^ (prefixWord ++ tailWord_2060490).sum := by decide
  have hdescent : baseEnd_2060490 < baseStart_2060490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060538 : List Nat := [3, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_2060538 : Nat := 118140960795 + 2060538 * 2 ^ 59
def prefixEnd_2060538 : Nat := 4983230072969 + 3 ^ 40 * 2060538 * 2
def baseEnd_2060538 : Nat := 470242844824073053021673

theorem tailTrace_2060538 : CollatzResearch.WordTrace tailWord_2060538 prefixEnd_2060538 470242844824073053021673 := by
  unfold tailWord_2060538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788498752257553179593567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50102663339353475145582845 18788498752257553179593567)
  ·
    refine ⟨28182748128386329769390351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18788498752257553179593567 28182748128386329769390351)
    ·
      refine ⟨42274122192579494654085527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28182748128386329769390351 42274122192579494654085527)
      ·
        refine ⟨63411183288869241981128291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42274122192579494654085527 63411183288869241981128291)
        ·
          refine ⟨95116774933303862971692437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63411183288869241981128291 95116774933303862971692437)
          ·
            refine ⟨4458598824998618576798083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 95116774933303862971692437 4458598824998618576798083)
            ·
              refine ⟨6687898237497927865197125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458598824998618576798083 6687898237497927865197125)
              ·
                refine ⟨1253980919530861474724461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6687898237497927865197125 1253980919530861474724461)
                ·
                  refine ⟨470242844824073053021673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1253980919530861474724461 470242844824073053021673)
                  ·
                    rfl

theorem cell21_2060538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_2060538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060538 prefixEnd_2060538 := by exact prefixLift 2060538
  have htrace : WordTrace (prefixWord ++ tailWord_2060538) baseStart_2060538 baseEnd_2060538 := by
    simpa [prefixWord, tailWord_2060538, baseEnd_2060538] using wordTrace_append hprefix tailTrace_2060538
  have hstable : (prefixWord ++ tailWord_2060538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060538).length < 2 ^ (prefixWord ++ tailWord_2060538).sum := by decide
  have hdescent : baseEnd_2060538 < baseStart_2060538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060549 : List Nat := [1, 3, 1, 1, 2, 1, 2, 10]
def baseStart_2060549 : Nat := 118140960795 + 2060549 * 2 ^ 59
def prefixEnd_2060549 : Nat := 4983230072969 + 3 ^ 40 * 2060549 * 2
def baseEnd_2060549 : Nat := 156748451724646492779439

theorem tailTrace_2060549 : CollatzResearch.WordTrace tailWord_2060549 prefixEnd_2060549 156748451724646492779439 := by
  unfold tailWord_2060549
  simp only [CollatzResearch.WordTrace]
  refine ⟨75154396211990361597024701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50102930807993574398016467 75154396211990361597024701)
  ·
    refine ⟨28182898579496385598884263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75154396211990361597024701 28182898579496385598884263)
    ·
      refine ⟨42274347869244578398326395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28182898579496385598884263 42274347869244578398326395)
      ·
        refine ⟨63411521803866867597489593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42274347869244578398326395 63411521803866867597489593)
        ·
          refine ⟨47558641352900150698117195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63411521803866867597489593 47558641352900150698117195)
          ·
            refine ⟨71337962029350226047175793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47558641352900150698117195 71337962029350226047175793)
            ·
              refine ⟨53503471522012669535381845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71337962029350226047175793 53503471522012669535381845)
              ·
                refine ⟨156748451724646492779439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 53503471522012669535381845 156748451724646492779439)
                ·
                  rfl

theorem cell21_2060549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_2060549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060549 prefixEnd_2060549 := by exact prefixLift 2060549
  have htrace : WordTrace (prefixWord ++ tailWord_2060549) baseStart_2060549 baseEnd_2060549 := by
    simpa [prefixWord, tailWord_2060549, baseEnd_2060549] using wordTrace_append hprefix tailTrace_2060549
  have hstable : (prefixWord ++ tailWord_2060549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060549).length < 2 ^ (prefixWord ++ tailWord_2060549).sum := by decide
  have hdescent : baseEnd_2060549 < baseStart_2060549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060552 : List Nat := [2, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_2060552 : Nat := 118140960795 + 2060552 * 2 ^ 59
def prefixEnd_2060552 : Nat := 4983230072969 + 3 ^ 40 * 2060552 * 2
def baseEnd_2060552 : Nat := 470246039814812139788311

theorem tailTrace_2060552 : CollatzResearch.WordTrace tailWord_2060552 prefixEnd_2060552 470246039814812139788311 := by
  unfold tailWord_2060552
  simp only [CollatzResearch.WordTrace]
  refine ⟨37577252815489746554691955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50103003753986328739589273 37577252815489746554691955)
  ·
    refine ⟨56365879223234619832037933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37577252815489746554691955 56365879223234619832037933)
    ·
      refine ⟨21137204708712982437014225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56365879223234619832037933 21137204708712982437014225)
      ·
        refine ⟨15852903531534736827760669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21137204708712982437014225 15852903531534736827760669)
        ·
          refine ⟨5944838824325526310410251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15852903531534736827760669 5944838824325526310410251)
          ·
            refine ⟨8917258236488289465615377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5944838824325526310410251 8917258236488289465615377)
            ·
              refine ⟨6687943677366217099211533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8917258236488289465615377 6687943677366217099211533)
              ·
                refine ⟨2507978879012331412204325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6687943677366217099211533 2507978879012331412204325)
                ·
                  refine ⟨470246039814812139788311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2507978879012331412204325 470246039814812139788311)
                  ·
                    rfl

theorem cell21_2060552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_2060552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060552 prefixEnd_2060552 := by exact prefixLift 2060552
  have htrace : WordTrace (prefixWord ++ tailWord_2060552) baseStart_2060552 baseEnd_2060552 := by
    simpa [prefixWord, tailWord_2060552, baseEnd_2060552] using wordTrace_append hprefix tailTrace_2060552
  have hstable : (prefixWord ++ tailWord_2060552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060552).length < 2 ^ (prefixWord ++ tailWord_2060552).sum := by decide
  have hdescent : baseEnd_2060552 < baseStart_2060552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060586 : List Nat := [3, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_2060586 : Nat := 118140960795 + 2060586 * 2 ^ 59
def prefixEnd_2060586 : Nat := 4983230072969 + 3 ^ 40 * 2060586 * 2
def baseEnd_2060586 : Nat := 470253799078035636221575

theorem tailTrace_2060586 : CollatzResearch.WordTrace tailWord_2060586 prefixEnd_2060586 470253799078035636221575 := by
  unfold tailWord_2060586
  simp only [CollatzResearch.WordTrace]
  refine ⟨18788936428214079229030403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50103830475237544610747741 18788936428214079229030403)
  ·
    refine ⟨28183404642321118843545605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18788936428214079229030403 28183404642321118843545605)
    ·
      refine ⟨5284388370435209783164801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28183404642321118843545605 5284388370435209783164801)
      ·
        refine ⟨3963291277826407337373601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5284388370435209783164801 3963291277826407337373601)
        ·
          refine ⟨2972468458369805503030201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3963291277826407337373601 2972468458369805503030201)
          ·
            refine ⟨2229351343777354127272651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2972468458369805503030201 2229351343777354127272651)
            ·
              refine ⟨3344027015666031190908977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229351343777354127272651 3344027015666031190908977)
              ·
                refine ⟨2508020261749523393181733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344027015666031190908977 2508020261749523393181733)
                ·
                  refine ⟨470253799078035636221575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508020261749523393181733 470253799078035636221575)
                  ·
                    rfl

theorem cell21_2060586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_2060586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060586 prefixEnd_2060586 := by exact prefixLift 2060586
  have htrace : WordTrace (prefixWord ++ tailWord_2060586) baseStart_2060586 baseEnd_2060586 := by
    simpa [prefixWord, tailWord_2060586, baseEnd_2060586] using wordTrace_append hprefix tailTrace_2060586
  have hstable : (prefixWord ++ tailWord_2060586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060586).length < 2 ^ (prefixWord ++ tailWord_2060586).sum := by decide
  have hdescent : baseEnd_2060586 < baseStart_2060586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060597 : List Nat := [1, 3, 3, 1, 2, 1, 4, 1, 5]
def baseStart_2060597 : Nat := 118140960795 + 2060597 * 2 ^ 59
def prefixEnd_2060597 : Nat := 4983230072969 + 3 ^ 40 * 2060597 * 2
def baseEnd_2060597 : Nat := 470256309427902061538219

theorem tailTrace_2060597 : CollatzResearch.WordTrace tailWord_2060597 prefixEnd_2060597 470256309427902061538219 := by
  unfold tailWord_2060597
  simp only [CollatzResearch.WordTrace]
  refine ⟨75156146915816465794772045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50104097943877643863181363 75156146915816465794772045)
  ·
    refine ⟨28183555093431174673039517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75156146915816465794772045 28183555093431174673039517)
    ·
      refine ⟨10568833160036690502389819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28183555093431174673039517 10568833160036690502389819)
      ·
        refine ⟨15853249740055035753584729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10568833160036690502389819 15853249740055035753584729)
        ·
          refine ⟨11889937305041276815188547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15853249740055035753584729 11889937305041276815188547)
          ·
            refine ⟨17834905957561915222782821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11889937305041276815188547 17834905957561915222782821)
            ·
              refine ⟨3344044867042859104271779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17834905957561915222782821 3344044867042859104271779)
              ·
                refine ⟨5016067300564288656407669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344044867042859104271779 5016067300564288656407669)
                ·
                  refine ⟨470256309427902061538219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5016067300564288656407669 470256309427902061538219)
                  ·
                    rfl

theorem cell21_2060597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_2060597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060597 prefixEnd_2060597 := by exact prefixLift 2060597
  have htrace : WordTrace (prefixWord ++ tailWord_2060597) baseStart_2060597 baseEnd_2060597 := by
    simpa [prefixWord, tailWord_2060597, baseEnd_2060597] using wordTrace_append hprefix tailTrace_2060597
  have hstable : (prefixWord ++ tailWord_2060597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060597).length < 2 ^ (prefixWord ++ tailWord_2060597).sum := by decide
  have hdescent : baseEnd_2060597 < baseStart_2060597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060611 : List Nat := [1, 1, 1, 3, 1, 3, 2, 5, 4]
def baseStart_2060611 : Nat := 118140960795 + 2060611 * 2 ^ 59
def prefixEnd_2060611 : Nat := 4983230072969 + 3 ^ 40 * 2060611 * 2
def baseEnd_2060611 : Nat := 470259504418641148304857

theorem tailTrace_2060611 : CollatzResearch.WordTrace tailWord_2060611 prefixEnd_2060611 470259504418641148304857 := by
  unfold tailWord_2060611
  simp only [CollatzResearch.WordTrace]
  refine ⟨75156657537765746185781687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50104438358510497457187791 75156657537765746185781687)
  ·
    refine ⟨112734986306648619278672531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75156657537765746185781687 112734986306648619278672531)
    ·
      refine ⟨169102479459972928918008797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112734986306648619278672531 169102479459972928918008797)
      ·
        refine ⟨63413429797489848344253299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169102479459972928918008797 63413429797489848344253299)
        ·
          refine ⟨95120144696234772516379949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63413429797489848344253299 95120144696234772516379949)
          ·
            refine ⟨35670054261088039693642481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95120144696234772516379949 35670054261088039693642481)
            ·
              refine ⟨26752540695816029770231861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35670054261088039693642481 26752540695816029770231861)
              ·
                refine ⟨2508050690232752790959237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26752540695816029770231861 2508050690232752790959237)
                ·
                  refine ⟨470259504418641148304857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508050690232752790959237 470259504418641148304857)
                  ·
                    rfl

theorem cell21_2060611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_2060611 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060611 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060611 prefixEnd_2060611 := by exact prefixLift 2060611
  have htrace : WordTrace (prefixWord ++ tailWord_2060611) baseStart_2060611 baseEnd_2060611 := by
    simpa [prefixWord, tailWord_2060611, baseEnd_2060611] using wordTrace_append hprefix tailTrace_2060611
  have hstable : (prefixWord ++ tailWord_2060611).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060611).length < 2 ^ (prefixWord ++ tailWord_2060611).sum := by decide
  have hdescent : baseEnd_2060611 < baseStart_2060611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060642 : List Nat := [3, 3, 2, 1, 1, 2, 9]
def baseStart_2060642 : Nat := 118140960795 + 2060642 * 2 ^ 59
def prefixEnd_2060642 : Nat := 4983230072969 + 3 ^ 40 * 2060642 * 2
def baseEnd_2060642 : Nat := 52251842115665775920903

theorem tailTrace_2060642 : CollatzResearch.WordTrace tailWord_2060642 prefixEnd_2060642 52251842115665775920903 := by
  unfold tailWord_2060642
  simp only [CollatzResearch.WordTrace]
  refine ⟨18789447050163359620040045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50105192133768958986773453 18789447050163359620040045)
  ·
    refine ⟨7046042643811259857515017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18789447050163359620040045 7046042643811259857515017)
    ·
      refine ⟨5284531982858444893136263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7046042643811259857515017 5284531982858444893136263)
      ·
        refine ⟨7926797974287667339704395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284531982858444893136263 7926797974287667339704395)
        ·
          refine ⟨11890196961431501009556593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7926797974287667339704395 11890196961431501009556593)
          ·
            refine ⟨8917647721073625757167445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11890196961431501009556593 8917647721073625757167445)
            ·
              refine ⟨52251842115665775920903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8917647721073625757167445 52251842115665775920903)
              ·
                rfl

theorem cell21_2060642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 9].length) (baseStart_2060642 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060642 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060642 prefixEnd_2060642 := by exact prefixLift 2060642
  have htrace : WordTrace (prefixWord ++ tailWord_2060642) baseStart_2060642 baseEnd_2060642 := by
    simpa [prefixWord, tailWord_2060642, baseEnd_2060642] using wordTrace_append hprefix tailTrace_2060642
  have hstable : (prefixWord ++ tailWord_2060642).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060642).length < 2 ^ (prefixWord ++ tailWord_2060642).sum := by decide
  have hdescent : baseEnd_2060642 < baseStart_2060642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060662 : List Nat := [5, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2060662 : Nat := 118140960795 + 2060662 * 2 ^ 59
def prefixEnd_2060662 : Nat := 4983230072969 + 3 ^ 40 * 2060662 * 2
def baseEnd_2060662 : Nat := 470271143313476392954753

theorem tailTrace_2060662 : CollatzResearch.WordTrace tailWord_2060662 prefixEnd_2060662 470271143313476392954753 := by
  unfold tailWord_2060662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4697407353786311368493015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50105678440387321263925493 4697407353786311368493015)
  ·
    refine ⟨7046111030679467052739523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4697407353786311368493015 7046111030679467052739523)
    ·
      refine ⟨10569166546019200579109285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7046111030679467052739523 10569166546019200579109285)
      ·
        refine ⟨1981718727378600108582991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10569166546019200579109285 1981718727378600108582991)
        ·
          refine ⟨2972578091067900162874487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1981718727378600108582991 2972578091067900162874487)
          ·
            refine ⟨4458867136601850244311731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972578091067900162874487 4458867136601850244311731)
            ·
              refine ⟨6688300704902775366467597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4458867136601850244311731 6688300704902775366467597)
              ·
                refine ⟨2508112764338540762425349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6688300704902775366467597 2508112764338540762425349)
                ·
                  refine ⟨470271143313476392954753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508112764338540762425349 470271143313476392954753)
                  ·
                    rfl

theorem cell21_2060662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2060662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060662 prefixEnd_2060662 := by exact prefixLift 2060662
  have htrace : WordTrace (prefixWord ++ tailWord_2060662) baseStart_2060662 baseEnd_2060662 := by
    simpa [prefixWord, tailWord_2060662, baseEnd_2060662] using wordTrace_append hprefix tailTrace_2060662
  have hstable : (prefixWord ++ tailWord_2060662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060662).length < 2 ^ (prefixWord ++ tailWord_2060662).sum := by decide
  have hdescent : baseEnd_2060662 < baseStart_2060662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060701 : List Nat := [1, 4, 2, 1, 13]
def baseStart_2060701 : Nat := 118140960795 + 2060701 * 2 ^ 59
def prefixEnd_2060701 : Nat := 4983230072969 + 3 ^ 40 * 2060701 * 2
def baseEnd_2060701 : Nat := 5805926464750876442033

theorem tailTrace_2060701 : CollatzResearch.WordTrace tailWord_2060701 prefixEnd_2060701 5805926464750876442033 := by
  unfold tailWord_2060701
  simp only [CollatzResearch.WordTrace]
  refine ⟨75159940107439691556557957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50106626738293127704371971 75159940107439691556557957)
  ·
    refine ⟨14092488770144942166854617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75159940107439691556557957 14092488770144942166854617)
    ·
      refine ⟨10569366577608706625140963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14092488770144942166854617 10569366577608706625140963)
      ·
        refine ⟨15854049866413059937711445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10569366577608706625140963 15854049866413059937711445)
        ·
          refine ⟨5805926464750876442033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 15854049866413059937711445 5805926464750876442033)
          ·
            rfl

theorem cell21_2060701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 13].length) (baseStart_2060701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060701 prefixEnd_2060701 := by exact prefixLift 2060701
  have htrace : WordTrace (prefixWord ++ tailWord_2060701) baseStart_2060701 baseEnd_2060701 := by
    simpa [prefixWord, tailWord_2060701, baseEnd_2060701] using wordTrace_append hprefix tailTrace_2060701
  have hstable : (prefixWord ++ tailWord_2060701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060701).length < 2 ^ (prefixWord ++ tailWord_2060701).sum := by decide
  have hdescent : baseEnd_2060701 < baseStart_2060701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060704 : List Nat := [2, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_2060704 : Nat := 118140960795 + 2060704 * 2 ^ 59
def prefixEnd_2060704 : Nat := 4983230072969 + 3 ^ 40 * 2060704 * 2
def baseEnd_2060704 : Nat := 470280728285693653254667

theorem tailTrace_2060704 : CollatzResearch.WordTrace tailWord_2060704 prefixEnd_2060704 470280728285693653254667 := by
  unfold tailWord_2060704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37580024763214411534458583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50106699684285882045944777 37580024763214411534458583)
  ·
    refine ⟨56370037144821617301687875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37580024763214411534458583 56370037144821617301687875)
    ·
      refine ⟨84555055717232425952531813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56370037144821617301687875 84555055717232425952531813)
      ·
        refine ⟨15854072946981079866099715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84555055717232425952531813 15854072946981079866099715)
        ·
          refine ⟨23781109420471619799149573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15854072946981079866099715 23781109420471619799149573)
          ·
            refine ⟨4458958016338428712340545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23781109420471619799149573 4458958016338428712340545)
            ·
              refine ⟨3344218512253821534255409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4458958016338428712340545 3344218512253821534255409)
              ·
                refine ⟨2508163884190366150691557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344218512253821534255409 2508163884190366150691557)
                ·
                  refine ⟨470280728285693653254667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508163884190366150691557 470280728285693653254667)
                  ·
                    rfl

theorem cell21_2060704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_2060704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060704 prefixEnd_2060704 := by exact prefixLift 2060704
  have htrace : WordTrace (prefixWord ++ tailWord_2060704) baseStart_2060704 baseEnd_2060704 := by
    simpa [prefixWord, tailWord_2060704, baseEnd_2060704] using wordTrace_append hprefix tailTrace_2060704
  have hstable : (prefixWord ++ tailWord_2060704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060704).length < 2 ^ (prefixWord ++ tailWord_2060704).sum := by decide
  have hdescent : baseEnd_2060704 < baseStart_2060704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060707 : List Nat := [1, 1, 1, 4, 1, 6, 2, 2, 3]
def baseStart_2060707 : Nat := 118140960795 + 2060707 * 2 ^ 59
def prefixEnd_2060707 : Nat := 4983230072969 + 3 ^ 40 * 2060707 * 2
def baseEnd_2060707 : Nat := 470281412926566314704661

theorem tailTrace_2060707 : CollatzResearch.WordTrace tailWord_2060707 prefixEnd_2060707 470281412926566314704661 := by
  unfold tailWord_2060707
  simp only [CollatzResearch.WordTrace]
  refine ⟨75160158945417954581276375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50106772630278636387517583 75160158945417954581276375)
  ·
    refine ⟨112740238418126931871914563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75160158945417954581276375 112740238418126931871914563)
    ·
      refine ⟨169110357627190397807871845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112740238418126931871914563 169110357627190397807871845)
      ·
        refine ⟨31708192055098199588975971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169110357627190397807871845 31708192055098199588975971)
        ·
          refine ⟨47562288082647299383463957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31708192055098199588975971 47562288082647299383463957)
          ·
            refine ⟨2229482253874092158599873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47562288082647299383463957 2229482253874092158599873)
            ·
              refine ⟨1672111690405569118949905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229482253874092158599873 1672111690405569118949905)
              ·
                refine ⟨1254083767804176839212429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1672111690405569118949905 1254083767804176839212429)
                ·
                  refine ⟨470281412926566314704661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254083767804176839212429 470281412926566314704661)
                  ·
                    rfl

theorem cell21_2060707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2, 3].length) (baseStart_2060707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060707 prefixEnd_2060707 := by exact prefixLift 2060707
  have htrace : WordTrace (prefixWord ++ tailWord_2060707) baseStart_2060707 baseEnd_2060707 := by
    simpa [prefixWord, tailWord_2060707, baseEnd_2060707] using wordTrace_append hprefix tailTrace_2060707
  have hstable : (prefixWord ++ tailWord_2060707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060707).length < 2 ^ (prefixWord ++ tailWord_2060707).sum := by decide
  have hdescent : baseEnd_2060707 < baseStart_2060707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060780 : List Nat := [2, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_2060780 : Nat := 118140960795 + 2060780 * 2 ^ 59
def prefixEnd_2060780 : Nat := 4983230072969 + 3 ^ 40 * 2060780 * 2
def baseEnd_2060780 : Nat := 470298072521134409987845

theorem tailTrace_2060780 : CollatzResearch.WordTrace tailWord_2060780 prefixEnd_2060780 470298072521134409987845 := by
  unfold tailWord_2060780
  simp only [CollatzResearch.WordTrace]
  refine ⟨37581410737076744024341897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50108547649435658699122529 37581410737076744024341897)
  ·
    refine ⟨28186058052807558018256423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37581410737076744024341897 28186058052807558018256423)
    ·
      refine ⟨42279087079211337027384635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28186058052807558018256423 42279087079211337027384635)
      ·
        refine ⟨63418630618817005541076953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42279087079211337027384635 63418630618817005541076953)
        ·
          refine ⟨47563972964112754155807715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63418630618817005541076953 47563972964112754155807715)
          ·
            refine ⟨71345959446169131233711573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47563972964112754155807715 71345959446169131233711573)
            ·
              refine ⟨1672170924519589013290115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71345959446169131233711573 1672170924519589013290115)
              ·
                refine ⟨2508256386779383519935173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672170924519589013290115 2508256386779383519935173)
                ·
                  refine ⟨470298072521134409987845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508256386779383519935173 470298072521134409987845)
                  ·
                    rfl

theorem cell21_2060780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_2060780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060780 prefixEnd_2060780 := by exact prefixLift 2060780
  have htrace : WordTrace (prefixWord ++ tailWord_2060780) baseStart_2060780 baseEnd_2060780 := by
    simpa [prefixWord, tailWord_2060780, baseEnd_2060780] using wordTrace_append hprefix tailTrace_2060780
  have hstable : (prefixWord ++ tailWord_2060780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060780).length < 2 ^ (prefixWord ++ tailWord_2060780).sum := by decide
  have hdescent : baseEnd_2060780 < baseStart_2060780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060853 : List Nat := [1, 3, 3, 1, 1, 2, 1, 9]
def baseStart_2060853 : Nat := 118140960795 + 2060853 * 2 ^ 59
def prefixEnd_2060853 : Nat := 4983230072969 + 3 ^ 40 * 2060853 * 2
def baseEnd_2060853 : Nat := 156771577371900835090343

theorem tailTrace_2060853 : CollatzResearch.WordTrace tailWord_2060853 prefixEnd_2060853 156771577371900835090343 := by
  unfold tailWord_2060853
  simp only [CollatzResearch.WordTrace]
  refine ⟨75165484002889021516091213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50110322668592681010727475 75165484002889021516091213)
  ·
    refine ⟨28187056501083383068534205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75165484002889021516091213 28187056501083383068534205)
    ·
      refine ⟨10570146187906268650700327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28187056501083383068534205 10570146187906268650700327)
      ·
        refine ⟨15855219281859402976050491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10570146187906268650700327 15855219281859402976050491)
        ·
          refine ⟨23782828922789104464075737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15855219281859402976050491 23782828922789104464075737)
          ·
            refine ⟨17837121692091828348056803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23782828922789104464075737 17837121692091828348056803)
            ·
              refine ⟨26755682538137742522085205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17837121692091828348056803 26755682538137742522085205)
              ·
                refine ⟨156771577371900835090343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26755682538137742522085205 156771577371900835090343)
                ·
                  rfl

theorem cell21_2060853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 9].length) (baseStart_2060853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060853 prefixEnd_2060853 := by exact prefixLift 2060853
  have htrace : WordTrace (prefixWord ++ tailWord_2060853) baseStart_2060853 baseEnd_2060853 := by
    simpa [prefixWord, tailWord_2060853, baseEnd_2060853] using wordTrace_append hprefix tailTrace_2060853
  have hstable : (prefixWord ++ tailWord_2060853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060853).length < 2 ^ (prefixWord ++ tailWord_2060853).sum := by decide
  have hdescent : baseEnd_2060853 < baseStart_2060853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060901 : List Nat := [1, 3, 1, 3, 4, 1, 1, 2, 5]
def baseStart_2060901 : Nat := 118140960795 + 2060901 * 2 ^ 59
def prefixEnd_2060901 : Nat := 4983230072969 + 3 ^ 40 * 2060901 * 2
def baseEnd_2060901 : Nat := 470325686369665088470931

theorem tailTrace_2060901 : CollatzResearch.WordTrace tailWord_2060901 prefixEnd_2060901 470325686369665088470931 := by
  unfold tailWord_2060901
  simp only [CollatzResearch.WordTrace]
  refine ⟨75167234706715125713838557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50111489804476750475892371 75167234706715125713838557)
  ·
    refine ⟨28187713015018172142689459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75167234706715125713838557 28187713015018172142689459)
    ·
      refine ⟨42281569522527258214034189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28187713015018172142689459 42281569522527258214034189)
      ·
        refine ⟨15855588570947721830262821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42281569522527258214034189 15855588570947721830262821)
        ·
          refine ⟨2972922857052697843174279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15855588570947721830262821 2972922857052697843174279)
          ·
            refine ⟨4459384285579046764761419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2972922857052697843174279 4459384285579046764761419)
            ·
              refine ⟨6689076428368570147142129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459384285579046764761419 6689076428368570147142129)
              ·
                refine ⟨5016807321276427610356597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6689076428368570147142129 5016807321276427610356597)
                ·
                  refine ⟨470325686369665088470931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5016807321276427610356597 470325686369665088470931)
                  ·
                    rfl

theorem cell21_2060901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 2, 5].length) (baseStart_2060901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060901 prefixEnd_2060901 := by exact prefixLift 2060901
  have htrace : WordTrace (prefixWord ++ tailWord_2060901) baseStart_2060901 baseEnd_2060901 := by
    simpa [prefixWord, tailWord_2060901, baseEnd_2060901] using wordTrace_append hprefix tailTrace_2060901
  have hstable : (prefixWord ++ tailWord_2060901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060901).length < 2 ^ (prefixWord ++ tailWord_2060901).sum := by decide
  have hdescent : baseEnd_2060901 < baseStart_2060901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060929 : List Nat := [1, 2, 4, 2, 1, 1, 10]
def baseStart_2060929 : Nat := 118140960795 + 2060929 * 2 ^ 59
def prefixEnd_2060929 : Nat := 4983230072969 + 3 ^ 40 * 2060929 * 2
def baseEnd_2060929 : Nat := 52259119594571473556023

theorem tailTrace_2060929 : CollatzResearch.WordTrace tailWord_2060929 prefixEnd_2060929 52259119594571473556023 := by
  unfold tailWord_2060929
  simp only [CollatzResearch.WordTrace]
  refine ⟨75168255950613686495857841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50112170633742457663905227 75168255950613686495857841)
  ·
    refine ⟨56376191962960264871893381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75168255950613686495857841 56376191962960264871893381)
    ·
      refine ⟨10570535993055049663480009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56376191962960264871893381 10570535993055049663480009)
      ·
        refine ⟨7927901994791287247610007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10570535993055049663480009 7927901994791287247610007)
        ·
          refine ⟨11891852992186930871415011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7927901994791287247610007 11891852992186930871415011)
          ·
            refine ⟨17837779488280396307122517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11891852992186930871415011 17837779488280396307122517)
            ·
              refine ⟨52259119594571473556023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17837779488280396307122517 52259119594571473556023)
              ·
                rfl

theorem cell21_2060929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 10].length) (baseStart_2060929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060929 prefixEnd_2060929 := by exact prefixLift 2060929
  have htrace : WordTrace (prefixWord ++ tailWord_2060929) baseStart_2060929 baseEnd_2060929 := by
    simpa [prefixWord, tailWord_2060929, baseEnd_2060929] using wordTrace_append hprefix tailTrace_2060929
  have hstable : (prefixWord ++ tailWord_2060929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060929).length < 2 ^ (prefixWord ++ tailWord_2060929).sum := by decide
  have hdescent : baseEnd_2060929 < baseStart_2060929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060932 : List Nat := [2, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_2060932 : Nat := 118140960795 + 2060932 * 2 ^ 59
def prefixEnd_2060932 : Nat := 4983230072969 + 3 ^ 40 * 2060932 * 2
def baseEnd_2060932 : Nat := 470332760992015923454201

theorem tailTrace_2060932 : CollatzResearch.WordTrace tailWord_2060932 prefixEnd_2060932 470332760992015923454201 := by
  unfold tailWord_2060932
  simp only [CollatzResearch.WordTrace]
  refine ⟨37584182684801409004108525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50112243579735212005478033 37584182684801409004108525)
  ·
    refine ⟨14094068506800528376540697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37584182684801409004108525 14094068506800528376540697)
    ·
      refine ⟨10570551380100396282405523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14094068506800528376540697 10570551380100396282405523)
      ·
        refine ⟨15855827070150594423608285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10570551380100396282405523 15855827070150594423608285)
        ·
          refine ⟨5945935151306472908853107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15855827070150594423608285 5945935151306472908853107)
          ·
            refine ⟨8918902726959709363279661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5945935151306472908853107 8918902726959709363279661)
            ·
              refine ⟨3344588522609891011229873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8918902726959709363279661 3344588522609891011229873)
              ·
                refine ⟨2508441391957418258422405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3344588522609891011229873 2508441391957418258422405)
                ·
                  refine ⟨470332760992015923454201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2508441391957418258422405 470332760992015923454201)
                  ·
                    rfl

theorem cell21_2060932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_2060932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060932 prefixEnd_2060932 := by exact prefixLift 2060932
  have htrace : WordTrace (prefixWord ++ tailWord_2060932) baseStart_2060932 baseEnd_2060932 := by
    simpa [prefixWord, tailWord_2060932, baseEnd_2060932] using wordTrace_append hprefix tailTrace_2060932
  have hstable : (prefixWord ++ tailWord_2060932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060932).length < 2 ^ (prefixWord ++ tailWord_2060932).sum := by decide
  have hdescent : baseEnd_2060932 < baseStart_2060932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2060943 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 9]
def baseStart_2060943 : Nat := 118140960795 + 2060943 * 2 ^ 59
def prefixEnd_2060943 : Nat := 4983230072969 + 3 ^ 40 * 2060943 * 2
def baseEnd_2060943 : Nat := 470335271341882348770845

theorem tailTrace_2060943 : CollatzResearch.WordTrace tailWord_2060943 prefixEnd_2060943 470335271341882348770845 := by
  unfold tailWord_2060943
  simp only [CollatzResearch.WordTrace]
  refine ⟨75168766572562966886867483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50112511048375311257911655 75168766572562966886867483)
  ·
    refine ⟨112753149858844450330301225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75168766572562966886867483 112753149858844450330301225)
    ·
      refine ⟨84564862394133337747725919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112753149858844450330301225 84564862394133337747725919)
      ·
        refine ⟨126847293591200006621588879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84564862394133337747725919 126847293591200006621588879)
        ·
          refine ⟨190270940386800009932383319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126847293591200006621588879 190270940386800009932383319)
          ·
            refine ⟨285406410580200014898574979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190270940386800009932383319 285406410580200014898574979)
            ·
              refine ⟨428109615870300022347862469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285406410580200014898574979 428109615870300022347862469)
              ·
                refine ⟨80270552975681254190224213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 428109615870300022347862469 80270552975681254190224213)
                ·
                  refine ⟨470335271341882348770845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80270552975681254190224213 470335271341882348770845)
                  ·
                    rfl

theorem cell21_2060943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_2060943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2060943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2060943 prefixEnd_2060943 := by exact prefixLift 2060943
  have htrace : WordTrace (prefixWord ++ tailWord_2060943) baseStart_2060943 baseEnd_2060943 := by
    simpa [prefixWord, tailWord_2060943, baseEnd_2060943] using wordTrace_append hprefix tailTrace_2060943
  have hstable : (prefixWord ++ tailWord_2060943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2060943).length < 2 ^ (prefixWord ++ tailWord_2060943).sum := by decide
  have hdescent : baseEnd_2060943 < baseStart_2060943 := by decide
  rcases family_descends (prefixWord ++ tailWord_2060943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061050 : List Nat := [3, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_2061050 : Nat := 118140960795 + 2061050 * 2 ^ 59
def prefixEnd_2061050 : Nat := 4983230072969 + 3 ^ 40 * 2061050 * 2
def baseEnd_2061050 : Nat := 470359690199673940487293

theorem tailTrace_2061050 : CollatzResearch.WordTrace tailWord_2061050 prefixEnd_2061050 470359690199673940487293 := by
  unfold tailWord_2061050
  simp only [CollatzResearch.WordTrace]
  refine ⟨18793167295793831040253151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50115112788783549440675069 18793167295793831040253151)
  ·
    refine ⟨28189750943690746560379727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18793167295793831040253151 28189750943690746560379727)
    ·
      refine ⟨42284626415536119840569591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28189750943690746560379727 42284626415536119840569591)
      ·
        refine ⟨63426939623304179760854387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42284626415536119840569591 63426939623304179760854387)
        ·
          refine ⟨95140409434956269641281581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63426939623304179760854387 95140409434956269641281581)
          ·
            refine ⟨35677653538108601115480593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95140409434956269641281581 35677653538108601115480593)
            ·
              refine ⟨26758240153581450836610445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35677653538108601115480593 26758240153581450836610445)
              ·
                refine ⟨10034340057593044063728917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26758240153581450836610445 10034340057593044063728917)
                ·
                  refine ⟨470359690199673940487293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10034340057593044063728917 470359690199673940487293)
                  ·
                    rfl

theorem cell21_2061050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_2061050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061050 prefixEnd_2061050 := by exact prefixLift 2061050
  have htrace : WordTrace (prefixWord ++ tailWord_2061050) baseStart_2061050 baseEnd_2061050 := by
    simpa [prefixWord, tailWord_2061050, baseEnd_2061050] using wordTrace_append hprefix tailTrace_2061050
  have hstable : (prefixWord ++ tailWord_2061050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061050).length < 2 ^ (prefixWord ++ tailWord_2061050).sum := by decide
  have hdescent : baseEnd_2061050 < baseStart_2061050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061053 : List Nat := [1, 4, 1, 1, 1, 1, 5, 4, 3]
def baseStart_2061053 : Nat := 118140960795 + 2061053 * 2 ^ 59
def prefixEnd_2061053 : Nat := 4983230072969 + 3 ^ 40 * 2061053 * 2
def baseEnd_2061053 : Nat := 470360374840546601937287

theorem tailTrace_2061053 : CollatzResearch.WordTrace tailWord_2061053 prefixEnd_2061053 470360374840546601937287 := by
  unfold tailWord_2061053
  simp only [CollatzResearch.WordTrace]
  refine ⟨75172778602164455673371813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50115185734776303782247875 75172778602164455673371813)
  ·
    refine ⟨14094895987905835438757215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75172778602164455673371813 14094895987905835438757215)
    ·
      refine ⟨21142343981858753158135823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14094895987905835438757215 21142343981858753158135823)
      ·
        refine ⟨31713515972788129737203735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21142343981858753158135823 31713515972788129737203735)
        ·
          refine ⟨47570273959182194605805603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31713515972788129737203735 47570273959182194605805603)
          ·
            refine ⟨71355410938773291908708405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47570273959182194605805603 71355410938773291908708405)
            ·
              refine ⟨6689569775509996116441413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71355410938773291908708405 6689569775509996116441413)
              ·
                refine ⟨1254294332908124271832765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6689569775509996116441413 1254294332908124271832765)
                ·
                  refine ⟨470360374840546601937287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254294332908124271832765 470360374840546601937287)
                  ·
                    rfl

theorem cell21_2061053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_2061053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061053 prefixEnd_2061053 := by exact prefixLift 2061053
  have htrace : WordTrace (prefixWord ++ tailWord_2061053) baseStart_2061053 baseEnd_2061053 := by
    simpa [prefixWord, tailWord_2061053, baseEnd_2061053] using wordTrace_append hprefix tailTrace_2061053
  have hstable : (prefixWord ++ tailWord_2061053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061053).length < 2 ^ (prefixWord ++ tailWord_2061053).sum := by decide
  have hdescent : baseEnd_2061053 < baseStart_2061053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061101 : List Nat := [1, 5, 3, 2, 1, 1, 1, 1, 6]
def baseStart_2061101 : Nat := 118140960795 + 2061101 * 2 ^ 59
def prefixEnd_2061101 : Nat := 4983230072969 + 3 ^ 40 * 2061101 * 2
def baseEnd_2061101 : Nat := 470371329094509185137189

theorem tailTrace_2061101 : CollatzResearch.WordTrace tailWord_2061101 prefixEnd_2061101 470371329094509185137189 := by
  unfold tailWord_2061101
  simp only [CollatzResearch.WordTrace]
  refine ⟨75174529305990559871119157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50116352870660373247412771 75174529305990559871119157)
  ·
    refine ⟨7047612122436614987917421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75174529305990559871119157 7047612122436614987917421)
    ·
      refine ⟨2642854545913730620469033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7047612122436614987917421 2642854545913730620469033)
      ·
        refine ⟨1982140909435297965351775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2642854545913730620469033 1982140909435297965351775)
        ·
          refine ⟨2973211364152946948027663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982140909435297965351775 2973211364152946948027663)
          ·
            refine ⟨4459817046229420422041495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973211364152946948027663 4459817046229420422041495)
            ·
              refine ⟨6689725569344130633062243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4459817046229420422041495 6689725569344130633062243)
              ·
                refine ⟨10034588354016195949593365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6689725569344130633062243 10034588354016195949593365)
                ·
                  refine ⟨470371329094509185137189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10034588354016195949593365 470371329094509185137189)
                  ·
                    rfl

theorem cell21_2061101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_2061101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061101 prefixEnd_2061101 := by exact prefixLift 2061101
  have htrace : WordTrace (prefixWord ++ tailWord_2061101) baseStart_2061101 baseEnd_2061101 := by
    simpa [prefixWord, tailWord_2061101, baseEnd_2061101] using wordTrace_append hprefix tailTrace_2061101
  have hstable : (prefixWord ++ tailWord_2061101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061101).length < 2 ^ (prefixWord ++ tailWord_2061101).sum := by decide
  have hdescent : baseEnd_2061101 < baseStart_2061101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061112 : List Nat := [2, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_2061112 : Nat := 118140960795 + 2061112 * 2 ^ 59
def prefixEnd_2061112 : Nat := 4983230072969 + 3 ^ 40 * 2061112 * 2
def baseEnd_2061112 : Nat := 470373839444375610453833

theorem tailTrace_2061112 : CollatzResearch.WordTrace tailWord_2061112 prefixEnd_2061112 470373839444375610453833 := by
  unfold tailWord_2061112
  simp only [CollatzResearch.WordTrace]
  refine ⟨37587465254475354374884795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50116620339300472499846393 37587465254475354374884795)
  ·
    refine ⟨56381197881713031562327193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37587465254475354374884795 56381197881713031562327193)
    ·
      refine ⟨42285898411284773671745395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56381197881713031562327193 42285898411284773671745395)
      ·
        refine ⟨63428847616927160507618093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42285898411284773671745395 63428847616927160507618093)
        ·
          refine ⟨23785817856347685190356785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63428847616927160507618093 23785817856347685190356785)
          ·
            refine ⟨17839363392260763892767589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23785817856347685190356785 17839363392260763892767589)
            ·
              refine ⟨3344880636048893229893923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17839363392260763892767589 3344880636048893229893923)
              ·
                refine ⟨5017320954073339844840885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3344880636048893229893923 5017320954073339844840885)
                ·
                  refine ⟨470373839444375610453833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5017320954073339844840885 470373839444375610453833)
                  ·
                    rfl

theorem cell21_2061112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_2061112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061112 prefixEnd_2061112 := by exact prefixLift 2061112
  have htrace : WordTrace (prefixWord ++ tailWord_2061112) baseStart_2061112 baseEnd_2061112 := by
    simpa [prefixWord, tailWord_2061112, baseEnd_2061112] using wordTrace_append hprefix tailTrace_2061112
  have hstable : (prefixWord ++ tailWord_2061112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061112).length < 2 ^ (prefixWord ++ tailWord_2061112).sum := by decide
  have hdescent : baseEnd_2061112 < baseStart_2061112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061146 : List Nat := [3, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_2061146 : Nat := 118140960795 + 2061146 * 2 ^ 59
def prefixEnd_2061146 : Nat := 4983230072969 + 3 ^ 40 * 2061146 * 2
def baseEnd_2061146 : Nat := 470381598707599106887097

theorem tailTrace_2061146 : CollatzResearch.WordTrace tailWord_2061146 prefixEnd_2061146 470381598707599106887097 := by
  unfold tailWord_2061146
  simp only [CollatzResearch.WordTrace]
  refine ⟨18794042647706883139126823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50117447060551688371004861 18794042647706883139126823)
  ·
    refine ⟨28191063971560324708690235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18794042647706883139126823 28191063971560324708690235)
    ·
      refine ⟨42286595957340487063035353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28191063971560324708690235 42286595957340487063035353)
      ·
        refine ⟨31714946968005365297276515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42286595957340487063035353 31714946968005365297276515)
        ·
          refine ⟨47572420452008047945914773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31714946968005365297276515 47572420452008047945914773)
          ·
            refine ⟨2229957208687877247464755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47572420452008047945914773 2229957208687877247464755)
            ·
              refine ⟨3344935813031815871197133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2229957208687877247464755 3344935813031815871197133)
              ·
                refine ⟨1254350929886930951698925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3344935813031815871197133 1254350929886930951698925)
                ·
                  refine ⟨470381598707599106887097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254350929886930951698925 470381598707599106887097)
                  ·
                    rfl

theorem cell21_2061146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_2061146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061146 prefixEnd_2061146 := by exact prefixLift 2061146
  have htrace : WordTrace (prefixWord ++ tailWord_2061146) baseStart_2061146 baseEnd_2061146 := by
    simpa [prefixWord, tailWord_2061146, baseEnd_2061146] using wordTrace_append hprefix tailTrace_2061146
  have hstable : (prefixWord ++ tailWord_2061146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061146).length < 2 ^ (prefixWord ++ tailWord_2061146).sum := by decide
  have hdescent : baseEnd_2061146 < baseStart_2061146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061174 : List Nat := [5, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2061174 : Nat := 118140960795 + 2061174 * 2 ^ 59
def prefixEnd_2061174 : Nat := 4983230072969 + 3 ^ 40 * 2061174 * 2
def baseEnd_2061174 : Nat := 156795996229692426806791

theorem tailTrace_2061174 : CollatzResearch.WordTrace tailWord_2061174 prefixEnd_2061174 156795996229692426806791 := by
  unfold tailWord_2061174
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698574489670380833657911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50118127889817395559017717 4698574489670380833657911)
  ·
    refine ⟨7047861734505571250486867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4698574489670380833657911 7047861734505571250486867)
    ·
      refine ⟨10571792601758356875730301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7047861734505571250486867 10571792601758356875730301)
      ·
        refine ⟨3964422225659383828398863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10571792601758356875730301 3964422225659383828398863)
        ·
          refine ⟨5946633338489075742598295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3964422225659383828398863 5946633338489075742598295)
          ·
            refine ⟨8919950007733613613897443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5946633338489075742598295 8919950007733613613897443)
            ·
              refine ⟨13379925011600420420846165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8919950007733613613897443 13379925011600420420846165)
              ·
                refine ⟨156795996229692426806791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13379925011600420420846165 156795996229692426806791)
                ·
                  rfl

theorem cell21_2061174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2061174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061174 prefixEnd_2061174 := by exact prefixLift 2061174
  have htrace : WordTrace (prefixWord ++ tailWord_2061174) baseStart_2061174 baseEnd_2061174 := by
    simpa [prefixWord, tailWord_2061174, baseEnd_2061174] using wordTrace_append hprefix tailTrace_2061174
  have hstable : (prefixWord ++ tailWord_2061174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061174).length < 2 ^ (prefixWord ++ tailWord_2061174).sum := by decide
  have hdescent : baseEnd_2061174 < baseStart_2061174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061301 : List Nat := [1, 3, 5, 2, 2, 1, 2, 5]
def baseStart_2061301 : Nat := 118140960795 + 2061301 * 2 ^ 59
def prefixEnd_2061301 : Nat := 4983230072969 + 3 ^ 40 * 2061301 * 2
def baseEnd_2061301 : Nat := 156805657273117760601149

theorem tailTrace_2061301 : CollatzResearch.WordTrace tailWord_2061301 prefixEnd_2061301 156805657273117760601149 := by
  unfold tailWord_2061301
  simp only [CollatzResearch.WordTrace]
  refine ⟨75181823905265994028399757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50121215936843996018933171 75181823905265994028399757)
  ·
    refine ⟨28193183964474747760649909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75181823905265994028399757 28193183964474747760649909)
    ·
      refine ⟨2643110996669507602560929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28193183964474747760649909 2643110996669507602560929)
      ·
        refine ⟨1982333247502130701920697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2643110996669507602560929 1982333247502130701920697)
        ·
          refine ⟨1486749935626598026440523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1982333247502130701920697 1486749935626598026440523)
          ·
            refine ⟨2230124903439897039660785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1486749935626598026440523 2230124903439897039660785)
            ·
              refine ⟨1672593677579922779745589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230124903439897039660785 1672593677579922779745589)
              ·
                refine ⟨156805657273117760601149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1672593677579922779745589 156805657273117760601149)
                ·
                  rfl

theorem cell21_2061301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 2, 5].length) (baseStart_2061301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061301 prefixEnd_2061301 := by exact prefixLift 2061301
  have htrace : WordTrace (prefixWord ++ tailWord_2061301) baseStart_2061301 baseEnd_2061301 := by
    simpa [prefixWord, tailWord_2061301, baseEnd_2061301] using wordTrace_append hprefix tailTrace_2061301
  have hstable : (prefixWord ++ tailWord_2061301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061301).length < 2 ^ (prefixWord ++ tailWord_2061301).sum := by decide
  have hdescent : baseEnd_2061301 < baseStart_2061301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061399 : List Nat := [1, 1, 3, 2, 2, 1, 1, 5, 5]
def baseStart_2061399 : Nat := 118140960795 + 2061399 * 2 ^ 59
def prefixEnd_2061399 : Nat := 4983230072969 + 3 ^ 40 * 2061399 * 2
def baseEnd_2061399 : Nat := 470439336754526889169913

theorem tailTrace_2061399 : CollatzResearch.WordTrace tailWord_2061399 prefixEnd_2061399 470439336754526889169913 := by
  unfold tailWord_2061399
  simp only [CollatzResearch.WordTrace]
  refine ⟨75185398258910956765467251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50123598839273971176978167 75185398258910956765467251)
  ·
    refine ⟨112778097388366435148200877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75185398258910956765467251 112778097388366435148200877)
    ·
      refine ⟨42291786520637413180575329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112778097388366435148200877 42291786520637413180575329)
      ·
        refine ⟨31718839890478059885431497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42291786520637413180575329 31718839890478059885431497)
        ·
          refine ⟨23789129917858544914073623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31718839890478059885431497 23789129917858544914073623)
          ·
            refine ⟨35683694876787817371110435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23789129917858544914073623 35683694876787817371110435)
            ·
              refine ⟨53525542315181726056665653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35683694876787817371110435 53525542315181726056665653)
              ·
                refine ⟨5018019592048286817812405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53525542315181726056665653 5018019592048286817812405)
                ·
                  refine ⟨470439336754526889169913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5018019592048286817812405 470439336754526889169913)
                  ·
                    rfl

theorem cell21_2061399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_2061399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061399 prefixEnd_2061399 := by exact prefixLift 2061399
  have htrace : WordTrace (prefixWord ++ tailWord_2061399) baseStart_2061399 baseEnd_2061399 := by
    simpa [prefixWord, tailWord_2061399, baseEnd_2061399] using wordTrace_append hprefix tailTrace_2061399
  have hstable : (prefixWord ++ tailWord_2061399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061399).length < 2 ^ (prefixWord ++ tailWord_2061399).sum := by decide
  have hdescent : baseEnd_2061399 < baseStart_2061399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061464 : List Nat := [2, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_2061464 : Nat := 118140960795 + 2061464 * 2 ^ 59
def prefixEnd_2061464 : Nat := 4983230072969 + 3 ^ 40 * 2061464 * 2
def baseEnd_2061464 : Nat := 470454170640101220586447

theorem tailTrace_2061464 : CollatzResearch.WordTrace tailWord_2061464 prefixEnd_2061464 470454170640101220586447 := by
  unfold tailWord_2061464
  simp only [CollatzResearch.WordTrace]
  refine ⟨37593884501837736433291723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50125179335783648577722297 37593884501837736433291723)
  ·
    refine ⟨56390826752756604649937585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37593884501837736433291723 56390826752756604649937585)
    ·
      refine ⟨42293120064567453487453189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56390826752756604649937585 42293120064567453487453189)
      ·
        refine ⟨7929960012106397528897473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42293120064567453487453189 7929960012106397528897473)
        ·
          refine ⟨5947470009079798146673105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7929960012106397528897473 5947470009079798146673105)
          ·
            refine ⟨4460602506809848610004829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5947470009079798146673105 4460602506809848610004829)
            ·
              refine ⟨1672725940053693228751811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4460602506809848610004829 1672725940053693228751811)
              ·
                refine ⟨2509088910080539843127717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1672725940053693228751811 2509088910080539843127717)
                ·
                  refine ⟨470454170640101220586447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509088910080539843127717 470454170640101220586447)
                  ·
                    rfl

theorem cell21_2061464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_2061464 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061464 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061464 prefixEnd_2061464 := by exact prefixLift 2061464
  have htrace : WordTrace (prefixWord ++ tailWord_2061464) baseStart_2061464 baseEnd_2061464 := by
    simpa [prefixWord, tailWord_2061464, baseEnd_2061464] using wordTrace_append hprefix tailTrace_2061464
  have hstable : (prefixWord ++ tailWord_2061464).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061464).length < 2 ^ (prefixWord ++ tailWord_2061464).sum := by decide
  have hdescent : baseEnd_2061464 < baseStart_2061464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061596 : List Nat := [2, 2, 3, 1, 1, 1, 2, 9]
def baseStart_2061596 : Nat := 118140960795 + 2061596 * 2 ^ 59
def prefixEnd_2061596 : Nat := 4983230072969 + 3 ^ 40 * 2061596 * 2
def baseEnd_2061596 : Nat := 156828098279499441462059

theorem tailTrace_2061596 : CollatzResearch.WordTrace tailWord_2061596 prefixEnd_2061596 156828098279499441462059 := by
  unfold tailWord_2061596
  simp only [CollatzResearch.WordTrace]
  refine ⟨37596291719598629705194321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50128388959464839606925761 37596291719598629705194321)
  ·
    refine ⟨28197218789698972278895741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37596291719598629705194321 28197218789698972278895741)
    ·
      refine ⟨10573957046137114604585903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28197218789698972278895741 10573957046137114604585903)
      ·
        refine ⟨15860935569205671906878855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10573957046137114604585903 15860935569205671906878855)
        ·
          refine ⟨23791403353808507860318283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15860935569205671906878855 23791403353808507860318283)
          ·
            refine ⟨35687105030712761790477425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23791403353808507860318283 35687105030712761790477425)
            ·
              refine ⟨26765328773034571342858069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35687105030712761790477425 26765328773034571342858069)
              ·
                refine ⟨156828098279499441462059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26765328773034571342858069 156828098279499441462059)
                ·
                  rfl

theorem cell21_2061596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_2061596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061596 prefixEnd_2061596 := by exact prefixLift 2061596
  have htrace : WordTrace (prefixWord ++ tailWord_2061596) baseStart_2061596 baseEnd_2061596 := by
    simpa [prefixWord, tailWord_2061596, baseEnd_2061596] using wordTrace_append hprefix tailTrace_2061596
  have hstable : (prefixWord ++ tailWord_2061596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061596).length < 2 ^ (prefixWord ++ tailWord_2061596).sum := by decide
  have hdescent : baseEnd_2061596 < baseStart_2061596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061602 : List Nat := [3, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_2061602 : Nat := 118140960795 + 2061602 * 2 ^ 59
def prefixEnd_2061602 : Nat := 4983230072969 + 3 ^ 40 * 2061602 * 2
def baseEnd_2061602 : Nat := 470485664120243647286165

theorem tailTrace_2061602 : CollatzResearch.WordTrace tailWord_2061602 prefixEnd_2061602 470485664120243647286165 := by
  unfold tailWord_2061602
  simp only [CollatzResearch.WordTrace]
  refine ⟨18798200569293880608776765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50128534851450348290071373 18798200569293880608776765)
  ·
    refine ⟨7049325213485205228291287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18798200569293880608776765 7049325213485205228291287)
    ·
      refine ⟨10573987820227807842436931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7049325213485205228291287 10573987820227807842436931)
      ·
        refine ⟨15860981730341711763655397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10573987820227807842436931 15860981730341711763655397)
        ·
          refine ⟨2973934074439070955685387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15860981730341711763655397 2973934074439070955685387)
          ·
            refine ⟨4460901111658606433528081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2973934074439070955685387 4460901111658606433528081)
            ·
              refine ⟨3345675833743954825146061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4460901111658606433528081 3345675833743954825146061)
              ·
                refine ⟨1254628437653983059429773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3345675833743954825146061 1254628437653983059429773)
                ·
                  refine ⟨470485664120243647286165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254628437653983059429773 470485664120243647286165)
                  ·
                    rfl

theorem cell21_2061602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_2061602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061602 prefixEnd_2061602 := by exact prefixLift 2061602
  have htrace : WordTrace (prefixWord ++ tailWord_2061602) baseStart_2061602 baseEnd_2061602 := by
    simpa [prefixWord, tailWord_2061602, baseEnd_2061602] using wordTrace_append hprefix tailTrace_2061602
  have hstable : (prefixWord ++ tailWord_2061602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061602).length < 2 ^ (prefixWord ++ tailWord_2061602).sum := by decide
  have hdescent : baseEnd_2061602 < baseStart_2061602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061678 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_2061678 : Nat := 118140960795 + 2061678 * 2 ^ 59
def prefixEnd_2061678 : Nat := 4983230072969 + 3 ^ 40 * 2061678 * 2
def baseEnd_2061678 : Nat := 470503008355684404019343

theorem tailTrace_2061678 : CollatzResearch.WordTrace tailWord_2061678 prefixEnd_2061678 470503008355684404019343 := by
  unfold tailWord_2061678
  simp only [CollatzResearch.WordTrace]
  refine ⟨9399446778112523426859211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50130382816600124943249125 9399446778112523426859211)
  ·
    refine ⟨14099170167168785140288817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9399446778112523426859211 14099170167168785140288817)
    ·
      refine ⟨10574377625376588855216613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14099170167168785140288817 10574377625376588855216613)
      ·
        refine ⟨1982695804758110410353115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10574377625376588855216613 1982695804758110410353115)
        ·
          refine ⟨2974043707137165615529673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1982695804758110410353115 2974043707137165615529673)
          ·
            refine ⟨2230532780352874211647255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974043707137165615529673 2230532780352874211647255)
            ·
              refine ⟨3345799170529311317470883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2230532780352874211647255 3345799170529311317470883)
              ·
                refine ⟨5018698755793966976206325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3345799170529311317470883 5018698755793966976206325)
                ·
                  refine ⟨470503008355684404019343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5018698755793966976206325 470503008355684404019343)
                  ·
                    rfl

theorem cell21_2061678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_2061678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061678 prefixEnd_2061678 := by exact prefixLift 2061678
  have htrace : WordTrace (prefixWord ++ tailWord_2061678) baseStart_2061678 baseEnd_2061678 := by
    simpa [prefixWord, tailWord_2061678, baseEnd_2061678] using wordTrace_append hprefix tailTrace_2061678
  have hstable : (prefixWord ++ tailWord_2061678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061678).length < 2 ^ (prefixWord ++ tailWord_2061678).sum := by decide
  have hdescent : baseEnd_2061678 < baseStart_2061678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061717 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 8]
def baseStart_2061717 : Nat := 118140960795 + 2061717 * 2 ^ 59
def prefixEnd_2061717 : Nat := 4983230072969 + 3 ^ 40 * 2061717 * 2
def baseEnd_2061717 : Nat := 470511908687029002869263

theorem tailTrace_2061717 : CollatzResearch.WordTrace tailWord_2061717 prefixEnd_2061717 470511908687029002869263 := by
  unfold tailWord_2061717
  simp only [CollatzResearch.WordTrace]
  refine ⟨75196996671758897075543405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50131331114505931383695603 75196996671758897075543405)
  ·
    refine ⟨28198873751909586403328777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75196996671758897075543405 28198873751909586403328777)
    ·
      refine ⟨21149155313932189802496583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28198873751909586403328777 21149155313932189802496583)
      ·
        refine ⟨31723732970898284703744875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21149155313932189802496583 31723732970898284703744875)
        ·
          refine ⟨47585599456347427055617313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31723732970898284703744875 47585599456347427055617313)
          ·
            refine ⟨35689199592260570291712985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47585599456347427055617313 35689199592260570291712985)
            ·
              refine ⟨26766899694195427718784739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35689199592260570291712985 26766899694195427718784739)
              ·
                refine ⟨40150349541293141578177109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26766899694195427718784739 40150349541293141578177109)
                ·
                  refine ⟨470511908687029002869263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40150349541293141578177109 470511908687029002869263)
                  ·
                    rfl

theorem cell21_2061717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 8].length) (baseStart_2061717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061717 prefixEnd_2061717 := by exact prefixLift 2061717
  have htrace : WordTrace (prefixWord ++ tailWord_2061717) baseStart_2061717 baseEnd_2061717 := by
    simpa [prefixWord, tailWord_2061717, baseEnd_2061717] using wordTrace_append hprefix tailTrace_2061717
  have hstable : (prefixWord ++ tailWord_2061717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061717).length < 2 ^ (prefixWord ++ tailWord_2061717).sum := by decide
  have hdescent : baseEnd_2061717 < baseStart_2061717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061855 : List Nat := [1, 1, 2, 4, 1, 1, 5, 1, 5]
def baseStart_2061855 : Nat := 118140960795 + 2061855 * 2 ^ 59
def prefixEnd_2061855 : Nat := 4983230072969 + 3 ^ 40 * 2061855 * 2
def baseEnd_2061855 : Nat := 470543402167171429568981

theorem tailTrace_2061855 : CollatzResearch.WordTrace tailWord_2061855 prefixEnd_2061855 470543402167171429568981 := by
  unfold tailWord_2061855
  simp only [CollatzResearch.WordTrace]
  refine ⟨75202029945258946644067019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50134686630172631096044679 75202029945258946644067019)
  ·
    refine ⟨112803044917888419966100529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75202029945258946644067019 112803044917888419966100529)
    ·
      refine ⟨84602283688416314974575397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112803044917888419966100529 84602283688416314974575397)
      ·
        refine ⟨15862928191578059057732887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84602283688416314974575397 15862928191578059057732887)
        ·
          refine ⟨23794392287367088586599331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15862928191578059057732887 23794392287367088586599331)
          ·
            refine ⟨35691588431050632879898997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23794392287367088586599331 35691588431050632879898997)
            ·
              refine ⟨3346086415410996832490531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35691588431050632879898997 3346086415410996832490531)
              ·
                refine ⟨5019129623116495248735797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3346086415410996832490531 5019129623116495248735797)
                ·
                  refine ⟨470543402167171429568981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5019129623116495248735797 470543402167171429568981)
                  ·
                    rfl

theorem cell21_2061855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_2061855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061855 prefixEnd_2061855 := by exact prefixLift 2061855
  have htrace : WordTrace (prefixWord ++ tailWord_2061855) baseStart_2061855 baseEnd_2061855 := by
    simpa [prefixWord, tailWord_2061855, baseEnd_2061855] using wordTrace_append hprefix tailTrace_2061855
  have hstable : (prefixWord ++ tailWord_2061855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061855).length < 2 ^ (prefixWord ++ tailWord_2061855).sum := by decide
  have hdescent : baseEnd_2061855 < baseStart_2061855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061906 : List Nat := [3, 2, 2, 1, 2, 4, 2, 2, 3]
def baseStart_2061906 : Nat := 118140960795 + 2061906 * 2 ^ 59
def prefixEnd_2061906 : Nat := 4983230072969 + 3 ^ 40 * 2061906 * 2
def baseEnd_2061906 : Nat := 470555041062006674218877

theorem tailTrace_2061906 : CollatzResearch.WordTrace tailWord_2061906 prefixEnd_2061906 470555041062006674218877 := by
  unfold tailWord_2061906
  simp only [CollatzResearch.WordTrace]
  refine ⟨18800972517018545588543393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50135926712049454902782381 18800972517018545588543393)
  ·
    refine ⟨14100729387763909191407545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18800972517018545588543393 14100729387763909191407545)
    ·
      refine ⟨10575547040822931893555659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14100729387763909191407545 10575547040822931893555659)
      ·
        refine ⟨15863320561234397840333489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10575547040822931893555659 15863320561234397840333489)
        ·
          refine ⟨11897490420925798380250117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15863320561234397840333489 11897490420925798380250117)
          ·
            refine ⟨2230779453923587196296897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11897490420925798380250117 2230779453923587196296897)
            ·
              refine ⟨1673084590442690397222673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2230779453923587196296897 1673084590442690397222673)
              ·
                refine ⟨1254813442832017797917005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673084590442690397222673 1254813442832017797917005)
                ·
                  refine ⟨470555041062006674218877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254813442832017797917005 470555041062006674218877)
                  ·
                    rfl

theorem cell21_2061906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_2061906 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061906 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061906 prefixEnd_2061906 := by exact prefixLift 2061906
  have htrace : WordTrace (prefixWord ++ tailWord_2061906) baseStart_2061906 baseEnd_2061906 := by
    simpa [prefixWord, tailWord_2061906, baseEnd_2061906] using wordTrace_append hprefix tailTrace_2061906
  have hstable : (prefixWord ++ tailWord_2061906).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061906).length < 2 ^ (prefixWord ++ tailWord_2061906).sum := by decide
  have hdescent : baseEnd_2061906 < baseStart_2061906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061914 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_2061914 : Nat := 118140960795 + 2061914 * 2 ^ 59
def prefixEnd_2061914 : Nat := 4983230072969 + 3 ^ 40 * 2061914 * 2
def baseEnd_2061914 : Nat := 470556866771000438085527

theorem tailTrace_2061914 : CollatzResearch.WordTrace tailWord_2061914 prefixEnd_2061914 470556866771000438085527 := by
  unfold tailWord_2061914
  simp only [CollatzResearch.WordTrace]
  refine ⟨18801045463011299930116199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50136121234696799813643197 18801045463011299930116199)
  ·
    refine ⟨28201568194516949895174299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18801045463011299930116199 28201568194516949895174299)
    ·
      refine ⟨42302352291775424842761449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28201568194516949895174299 42302352291775424842761449)
      ·
        refine ⟨31726764218831568632071087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42302352291775424842761449 31726764218831568632071087)
        ·
          refine ⟨47590146328247352948106631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31726764218831568632071087 47590146328247352948106631)
          ·
            refine ⟨71385219492371029422159947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47590146328247352948106631 71385219492371029422159947)
            ·
              refine ⟨107077829238556544133239921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71385219492371029422159947 107077829238556544133239921)
              ·
                refine ⟨80308371928917408099929941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107077829238556544133239921 80308371928917408099929941)
                ·
                  refine ⟨470556866771000438085527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80308371928917408099929941 470556866771000438085527)
                  ·
                    rfl

theorem cell21_2061914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_2061914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061914 prefixEnd_2061914 := by exact prefixLift 2061914
  have htrace : WordTrace (prefixWord ++ tailWord_2061914) baseStart_2061914 baseEnd_2061914 := by
    simpa [prefixWord, tailWord_2061914, baseEnd_2061914] using wordTrace_append hprefix tailTrace_2061914
  have hstable : (prefixWord ++ tailWord_2061914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061914).length < 2 ^ (prefixWord ++ tailWord_2061914).sum := by decide
  have hdescent : baseEnd_2061914 < baseStart_2061914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061934 : List Nat := [4, 1, 2, 2, 3, 1, 3, 5]
def baseStart_2061934 : Nat := 118140960795 + 2061934 * 2 ^ 59
def prefixEnd_2061934 : Nat := 4983230072969 + 3 ^ 40 * 2061934 * 2
def baseEnd_2061934 : Nat := 156853810347828282584051

theorem tailTrace_2061934 : CollatzResearch.WordTrace tailWord_2061934 prefixEnd_2061934 156853810347828282584051 := by
  unfold tailWord_2061934
  simp only [CollatzResearch.WordTrace]
  refine ⟨9400613913996592892024107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50136607541315162090795237 9400613913996592892024107)
  ·
    refine ⟨14100920870994889338036161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9400613913996592892024107 14100920870994889338036161)
    ·
      refine ⟨10575690653246167003527121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14100920870994889338036161 10575690653246167003527121)
      ·
        refine ⟨7931767989934625252645341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10575690653246167003527121 7931767989934625252645341)
        ·
          refine ⟨2974412996225484469742003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7931767989934625252645341 2974412996225484469742003)
          ·
            refine ⟨4461619494338226704613005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974412996225484469742003 4461619494338226704613005)
            ·
              refine ⟨1673107310376835014229877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4461619494338226704613005 1673107310376835014229877)
              ·
                refine ⟨156853810347828282584051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673107310376835014229877 156853810347828282584051)
                ·
                  rfl

theorem cell21_2061934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_2061934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061934 prefixEnd_2061934 := by exact prefixLift 2061934
  have htrace : WordTrace (prefixWord ++ tailWord_2061934) baseStart_2061934 baseEnd_2061934 := by
    simpa [prefixWord, tailWord_2061934, baseEnd_2061934] using wordTrace_append hprefix tailTrace_2061934
  have hstable : (prefixWord ++ tailWord_2061934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061934).length < 2 ^ (prefixWord ++ tailWord_2061934).sum := by decide
  have hdescent : baseEnd_2061934 < baseStart_2061934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061945 : List Nat := [1, 2, 1, 3, 3, 1, 2, 2, 6]
def baseStart_2061945 : Nat := 118140960795 + 2061945 * 2 ^ 59
def prefixEnd_2061945 : Nat := 4983230072969 + 3 ^ 40 * 2061945 * 2
def baseEnd_2061945 : Nat := 470563941393351273068797

theorem tailTrace_2061945 : CollatzResearch.WordTrace tailWord_2061945 prefixEnd_2061945 470563941393351273068797 := by
  unfold tailWord_2061945
  simp only [CollatzResearch.WordTrace]
  refine ⟨75205312514932892014843289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50136875009955261343228859 75205312514932892014843289)
  ·
    refine ⟨56403984386199669011132467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75205312514932892014843289 56403984386199669011132467)
    ·
      refine ⟨84605976579299503516698701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56403984386199669011132467 84605976579299503516698701)
      ·
        refine ⟨31727241217237313818762013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84605976579299503516698701 31727241217237313818762013)
        ·
          refine ⟨11897715456463992682035755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31727241217237313818762013 11897715456463992682035755)
          ·
            refine ⟨17846573184695989023053633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11897715456463992682035755 17846573184695989023053633)
            ·
              refine ⟨13384929888521991767290225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17846573184695989023053633 13384929888521991767290225)
              ·
                refine ⟨10038697416391493825467669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13384929888521991767290225 10038697416391493825467669)
                ·
                  refine ⟨470563941393351273068797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10038697416391493825467669 470563941393351273068797)
                  ·
                    rfl

theorem cell21_2061945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 2, 6].length) (baseStart_2061945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061945 prefixEnd_2061945 := by exact prefixLift 2061945
  have htrace : WordTrace (prefixWord ++ tailWord_2061945) baseStart_2061945 baseEnd_2061945 := by
    simpa [prefixWord, tailWord_2061945, baseEnd_2061945] using wordTrace_append hprefix tailTrace_2061945
  have hstable : (prefixWord ++ tailWord_2061945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061945).length < 2 ^ (prefixWord ++ tailWord_2061945).sum := by decide
  have hdescent : baseEnd_2061945 < baseStart_2061945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2061962 : List Nat := [3, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_2061962 : Nat := 118140960795 + 2061962 * 2 ^ 59
def prefixEnd_2061962 : Nat := 4983230072969 + 3 ^ 40 * 2061962 * 2
def baseEnd_2061962 : Nat := 470567821024963021285429

theorem tailTrace_2061962 : CollatzResearch.WordTrace tailWord_2061962 prefixEnd_2061962 470567821024963021285429 := by
  unfold tailWord_2061962
  simp only [CollatzResearch.WordTrace]
  refine ⟨18801483138967825979553035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50137288370580869278808093 18801483138967825979553035)
  ·
    refine ⟨28202224708451738969329553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18801483138967825979553035 28202224708451738969329553)
    ·
      refine ⟨21151668531338804226997165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28202224708451738969329553 21151668531338804226997165)
      ·
        refine ⟨7931875699252051585123937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21151668531338804226997165 7931875699252051585123937)
        ·
          refine ⟨5948906774439038688842953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7931875699252051585123937 5948906774439038688842953)
          ·
            refine ⟨4461680080829279016632215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5948906774439038688842953 4461680080829279016632215)
            ·
              refine ⟨6692520121243918524948323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4461680080829279016632215 6692520121243918524948323)
              ·
                refine ⟨10038780181865877787422485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6692520121243918524948323 10038780181865877787422485)
                ·
                  refine ⟨470567821024963021285429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10038780181865877787422485 470567821024963021285429)
                  ·
                    rfl

theorem cell21_2061962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_2061962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2061962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2061962 prefixEnd_2061962 := by exact prefixLift 2061962
  have htrace : WordTrace (prefixWord ++ tailWord_2061962) baseStart_2061962 baseEnd_2061962 := by
    simpa [prefixWord, tailWord_2061962, baseEnd_2061962] using wordTrace_append hprefix tailTrace_2061962
  have hstable : (prefixWord ++ tailWord_2061962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2061962).length < 2 ^ (prefixWord ++ tailWord_2061962).sum := by decide
  have hdescent : baseEnd_2061962 < baseStart_2061962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2061962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062131 : List Nat := [1, 1, 1, 2, 7, 2, 1, 2, 4]
def baseStart_2062131 : Nat := 118140960795 + 2062131 * 2 ^ 59
def prefixEnd_2062131 : Nat := 4983230072969 + 3 ^ 40 * 2062131 * 2
def baseEnd_2062131 : Nat := 470606389127456282968417

theorem tailTrace_2062131 : CollatzResearch.WordTrace tailWord_2062131 prefixEnd_2062131 470606389127456282968417 := by
  unfold tailWord_2062131
  simp only [CollatzResearch.WordTrace]
  refine ⟨75212096492259045781114247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50141397661506030520742831 75212096492259045781114247)
  ·
    refine ⟨112818144738388568671671371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75212096492259045781114247 112818144738388568671671371)
    ·
      refine ⟨169227217107582853007507057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112818144738388568671671371 169227217107582853007507057)
      ·
        refine ⟨126920412830687139755630293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 169227217107582853007507057 126920412830687139755630293)
        ·
          refine ⟨2974697175719229838022585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 126920412830687139755630293 2974697175719229838022585)
          ·
            refine ⟨2231022881789422378516939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2974697175719229838022585 2231022881789422378516939)
            ·
              refine ⟨3346534322684133567775409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231022881789422378516939 3346534322684133567775409)
              ·
                refine ⟨2509900742013100175831557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3346534322684133567775409 2509900742013100175831557)
                ·
                  refine ⟨470606389127456282968417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2509900742013100175831557 470606389127456282968417)
                  ·
                    rfl

theorem cell21_2062131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 1, 2, 4].length) (baseStart_2062131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062131 prefixEnd_2062131 := by exact prefixLift 2062131
  have htrace : WordTrace (prefixWord ++ tailWord_2062131) baseStart_2062131 baseEnd_2062131 := by
    simpa [prefixWord, tailWord_2062131, baseEnd_2062131] using wordTrace_append hprefix tailTrace_2062131
  have hstable : (prefixWord ++ tailWord_2062131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062131).length < 2 ^ (prefixWord ++ tailWord_2062131).sum := by decide
  have hdescent : baseEnd_2062131 < baseStart_2062131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062176 : List Nat := [2, 1, 1, 3, 3, 2, 3, 3, 3]
def baseStart_2062176 : Nat := 118140960795 + 2062176 * 2 ^ 59
def prefixEnd_2062176 : Nat := 4983230072969 + 3 ^ 40 * 2062176 * 2
def baseEnd_2062176 : Nat := 470616658740546204718325

theorem tailTrace_2062176 : CollatzResearch.WordTrace tailWord_2062176 prefixEnd_2062176 470616658740546204718325 := by
  unfold tailWord_2062176
  simp only [CollatzResearch.WordTrace]
  refine ⟨37606868888548009233251191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50142491851397345644334921 37606868888548009233251191)
  ·
    refine ⟨56410303332822013849876787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37606868888548009233251191 56410303332822013849876787)
    ·
      refine ⟨84615454999233020774815181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56410303332822013849876787 84615454999233020774815181)
      ·
        refine ⟨31730795624712382790555693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84615454999233020774815181 31730795624712382790555693)
        ·
          refine ⟨11899048359267143546458385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31730795624712382790555693 11899048359267143546458385)
          ·
            refine ⟨8924286269450357659843789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11899048359267143546458385 8924286269450357659843789)
            ·
              refine ⟨3346607351043884122441421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8924286269450357659843789 3346607351043884122441421)
              ·
                refine ⟨1254977756641456545915533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3346607351043884122441421 1254977756641456545915533)
                ·
                  refine ⟨470616658740546204718325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1254977756641456545915533 470616658740546204718325)
                  ·
                    rfl

theorem cell21_2062176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 3, 3].length) (baseStart_2062176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062176 prefixEnd_2062176 := by exact prefixLift 2062176
  have htrace : WordTrace (prefixWord ++ tailWord_2062176) baseStart_2062176 baseEnd_2062176 := by
    simpa [prefixWord, tailWord_2062176, baseEnd_2062176] using wordTrace_append hprefix tailTrace_2062176
  have hstable : (prefixWord ++ tailWord_2062176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062176).length < 2 ^ (prefixWord ++ tailWord_2062176).sum := by decide
  have hdescent : baseEnd_2062176 < baseStart_2062176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062190 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_2062190 : Nat := 118140960795 + 2062190 * 2 ^ 59
def prefixEnd_2062190 : Nat := 4983230072969 + 3 ^ 40 * 2062190 * 2
def baseEnd_2062190 : Nat := 470619853731285291484963

theorem tailTrace_2062190 : CollatzResearch.WordTrace tailWord_2062190 prefixEnd_2062190 470619853731285291484963 := by
  unfold tailWord_2062190
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401781049880662357189003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50142832266030199238341349 9401781049880662357189003)
  ·
    refine ⟨14102671574820993535783505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9401781049880662357189003 14102671574820993535783505)
    ·
      refine ⟨10577003681115745151837629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14102671574820993535783505 10577003681115745151837629)
      ·
        refine ⟨3966376380418404431939111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10577003681115745151837629 3966376380418404431939111)
        ·
          refine ⟨5949564570627606647908667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3966376380418404431939111 5949564570627606647908667)
          ·
            refine ⟨8924346855941409971863001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5949564570627606647908667 8924346855941409971863001)
            ·
              refine ⟨6693260141956057478897251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8924346855941409971863001 6693260141956057478897251)
              ·
                refine ⟨10039890212934086218345877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693260141956057478897251 10039890212934086218345877)
                ·
                  refine ⟨470619853731285291484963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10039890212934086218345877 470619853731285291484963)
                  ·
                    rfl

theorem cell21_2062190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_2062190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062190 prefixEnd_2062190 := by exact prefixLift 2062190
  have htrace : WordTrace (prefixWord ++ tailWord_2062190) baseStart_2062190 baseEnd_2062190 := by
    simpa [prefixWord, tailWord_2062190, baseEnd_2062190] using wordTrace_append hprefix tailTrace_2062190
  have hstable : (prefixWord ++ tailWord_2062190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062190).length < 2 ^ (prefixWord ++ tailWord_2062190).sum := by decide
  have hdescent : baseEnd_2062190 < baseStart_2062190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062238 : List Nat := [4, 3, 1, 3, 2, 8]
def baseStart_2062238 : Nat := 118140960795 + 2062238 * 2 ^ 59
def prefixEnd_2062238 : Nat := 4983230072969 + 3 ^ 40 * 2062238 * 2
def baseEnd_2062238 : Nat := 17430770666120291654995

theorem tailTrace_2062238 : CollatzResearch.WordTrace tailWord_2062238 prefixEnd_2062238 17430770666120291654995 := by
  unfold tailWord_2062238
  simp only [CollatzResearch.WordTrace]
  refine ⟨9401999887858925381907421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50143999401914268703506245 9401999887858925381907421)
  ·
    refine ⟨3525749957947097018215283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9401999887858925381907421 3525749957947097018215283)
    ·
      refine ⟨5288624936920645527322925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3525749957947097018215283 5288624936920645527322925)
      ·
        refine ⟨1983234351345242072746097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5288624936920645527322925 1983234351345242072746097)
        ·
          refine ⟨1487425763508931554559573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1983234351345242072746097 1487425763508931554559573)
          ·
            refine ⟨17430770666120291654995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1487425763508931554559573 17430770666120291654995)
            ·
              rfl

theorem cell21_2062238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 8].length) (baseStart_2062238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062238 prefixEnd_2062238 := by exact prefixLift 2062238
  have htrace : WordTrace (prefixWord ++ tailWord_2062238) baseStart_2062238 baseEnd_2062238 := by
    simpa [prefixWord, tailWord_2062238, baseEnd_2062238] using wordTrace_append hprefix tailTrace_2062238
  have hstable : (prefixWord ++ tailWord_2062238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062238).length < 2 ^ (prefixWord ++ tailWord_2062238).sum := by decide
  have hdescent : baseEnd_2062238 < baseStart_2062238 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062300 : List Nat := [2, 2, 6, 1, 1, 1, 1, 1, 6]
def baseStart_2062300 : Nat := 118140960795 + 2062300 * 2 ^ 59
def prefixEnd_2062300 : Nat := 4983230072969 + 3 ^ 40 * 2062300 * 2
def baseEnd_2062300 : Nat := 470644957229949544651405

theorem tailTrace_2062300 : CollatzResearch.WordTrace tailWord_2062300 prefixEnd_2062300 470644957229949544651405 := by
  unfold tailWord_2062300
  simp only [CollatzResearch.WordTrace]
  refine ⟨37609130214323393822008177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50145506952431191762677569 37609130214323393822008177)
  ·
    refine ⟨28206847660742545366506133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37609130214323393822008177 28206847660742545366506133)
    ·
      refine ⟨1322195984097306814054975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 28206847660742545366506133 1322195984097306814054975)
      ·
        refine ⟨1983293976145960221082463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322195984097306814054975 1983293976145960221082463)
        ·
          refine ⟨2974940964218940331623695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983293976145960221082463 2974940964218940331623695)
          ·
            refine ⟨4462411446328410497435543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2974940964218940331623695 4462411446328410497435543)
            ·
              refine ⟨6693617169492615746153315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4462411446328410497435543 6693617169492615746153315)
              ·
                refine ⟨10040425754238923619229973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6693617169492615746153315 10040425754238923619229973)
                ·
                  refine ⟨470644957229949544651405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10040425754238923619229973 470644957229949544651405)
                  ·
                    rfl

theorem cell21_2062300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 1, 6].length) (baseStart_2062300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062300 prefixEnd_2062300 := by exact prefixLift 2062300
  have htrace : WordTrace (prefixWord ++ tailWord_2062300) baseStart_2062300 baseEnd_2062300 := by
    simpa [prefixWord, tailWord_2062300, baseEnd_2062300] using wordTrace_append hprefix tailTrace_2062300
  have hstable : (prefixWord ++ tailWord_2062300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062300).length < 2 ^ (prefixWord ++ tailWord_2062300).sum := by decide
  have hdescent : baseEnd_2062300 < baseStart_2062300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062421 : List Nat := [1, 3, 2, 2, 1, 5, 2, 2, 3]
def baseStart_2062421 : Nat := 118140960795 + 2062421 * 2 ^ 59
def prefixEnd_2062421 : Nat := 4983230072969 + 3 ^ 40 * 2062421 * 2
def baseEnd_2062421 : Nat := 470672571078480223134491

theorem tailTrace_2062421 : CollatzResearch.WordTrace tailWord_2062421 prefixEnd_2062421 470672571078480223134491 := by
  unfold tailWord_2062421
  simp only [CollatzResearch.WordTrace]
  refine ⟨75222673661208425309171117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50148449107472283539447411 75222673661208425309171117)
  ·
    refine ⟨28208502622953159490939169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75222673661208425309171117 28208502622953159490939169)
    ·
      refine ⟨21156376967214869618204377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28208502622953159490939169 21156376967214869618204377)
      ·
        refine ⟨15867282725411152213653283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21156376967214869618204377 15867282725411152213653283)
        ·
          refine ⟨23800924088116728320479925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15867282725411152213653283 23800924088116728320479925)
          ·
            refine ⟨2231336633260943280044993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23800924088116728320479925 2231336633260943280044993)
            ·
              refine ⟨1673502474945707460033745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231336633260943280044993 1673502474945707460033745)
              ·
                refine ⟨1255126856209280595025309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673502474945707460033745 1255126856209280595025309)
                ·
                  refine ⟨470672571078480223134491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255126856209280595025309 470672571078480223134491)
                  ·
                    rfl

theorem cell21_2062421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_2062421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062421 prefixEnd_2062421 := by exact prefixLift 2062421
  have htrace : WordTrace (prefixWord ++ tailWord_2062421) baseStart_2062421 baseEnd_2062421 := by
    simpa [prefixWord, tailWord_2062421, baseEnd_2062421] using wordTrace_append hprefix tailTrace_2062421
  have hstable : (prefixWord ++ tailWord_2062421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062421).length < 2 ^ (prefixWord ++ tailWord_2062421).sum := by decide
  have hdescent : baseEnd_2062421 < baseStart_2062421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062432 : List Nat := [2, 1, 1, 3, 2, 5, 1, 6]
def baseStart_2062432 : Nat := 118140960795 + 2062432 * 2 ^ 59
def prefixEnd_2062432 : Nat := 4983230072969 + 3 ^ 40 * 2062432 * 2
def baseEnd_2062432 : Nat := 156891693809448882817045

theorem tailTrace_2062432 : CollatzResearch.WordTrace tailWord_2062432 prefixEnd_2062432 156891693809448882817045 := by
  unfold tailWord_2062432
  simp only [CollatzResearch.WordTrace]
  refine ⟨37611537432084287093910775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50148716576112382791881033 37611537432084287093910775)
  ·
    refine ⟨56417306148126430640866163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37611537432084287093910775 56417306148126430640866163)
    ·
      refine ⟨84625959222189645961299245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56417306148126430640866163 84625959222189645961299245)
      ·
        refine ⟨31734734708321117235487217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84625959222189645961299245 31734734708321117235487217)
        ·
          refine ⟨23801051031240837926615413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31734734708321117235487217 23801051031240837926615413)
          ·
            refine ⟨2231348534178828555620195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23801051031240837926615413 2231348534178828555620195)
            ·
              refine ⟨3347022801268242833430293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231348534178828555620195 3347022801268242833430293)
              ·
                refine ⟨156891693809448882817045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3347022801268242833430293 156891693809448882817045)
                ·
                  rfl

theorem cell21_2062432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_2062432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062432 prefixEnd_2062432 := by exact prefixLift 2062432
  have htrace : WordTrace (prefixWord ++ tailWord_2062432) baseStart_2062432 baseEnd_2062432 := by
    simpa [prefixWord, tailWord_2062432, baseEnd_2062432] using wordTrace_append hprefix tailTrace_2062432
  have hstable : (prefixWord ++ tailWord_2062432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062432).length < 2 ^ (prefixWord ++ tailWord_2062432).sum := by decide
  have hdescent : baseEnd_2062432 < baseStart_2062432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062674 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 5]
def baseStart_2062674 : Nat := 118140960795 + 2062674 * 2 ^ 59
def prefixEnd_2062674 : Nat := 4983230072969 + 3 ^ 40 * 2062674 * 2
def baseEnd_2062674 : Nat := 470730309125408005417307

theorem tailTrace_2062674 : CollatzResearch.WordTrace tailWord_2062674 prefixEnd_2062674 470730309125408005417307 := by
  unfold tailWord_2062674
  simp only [CollatzResearch.WordTrace]
  refine ⟨18807975332322962379532769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50154600886194566345420717 18807975332322962379532769)
  ·
    refine ⟨14105981499242221784649577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18807975332322962379532769 14105981499242221784649577)
    ·
      refine ⟨10579486124431666338487183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14105981499242221784649577 10579486124431666338487183)
      ·
        refine ⟨15869229186647499507730775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10579486124431666338487183 15869229186647499507730775)
        ·
          refine ⟨23803843779971249261596163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15869229186647499507730775 23803843779971249261596163)
          ·
            refine ⟨35705765669956873892394245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23803843779971249261596163 35705765669956873892394245)
            ·
              refine ⟨6694831063116913854823921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35705765669956873892394245 6694831063116913854823921)
              ·
                refine ⟨5021123297337685391117941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6694831063116913854823921 5021123297337685391117941)
                ·
                  refine ⟨470730309125408005417307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5021123297337685391117941 470730309125408005417307)
                  ·
                    rfl

theorem cell21_2062674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_2062674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062674 prefixEnd_2062674 := by exact prefixLift 2062674
  have htrace : WordTrace (prefixWord ++ tailWord_2062674) baseStart_2062674 baseEnd_2062674 := by
    simpa [prefixWord, tailWord_2062674, baseEnd_2062674] using wordTrace_append hprefix tailTrace_2062674
  have hstable : (prefixWord ++ tailWord_2062674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062674).length < 2 ^ (prefixWord ++ tailWord_2062674).sum := by decide
  have hdescent : baseEnd_2062674 < baseStart_2062674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062677 : List Nat := [1, 3, 2, 2, 4, 2, 2, 5]
def baseStart_2062677 : Nat := 118140960795 + 2062677 * 2 ^ 59
def prefixEnd_2062677 : Nat := 4983230072969 + 3 ^ 40 * 2062677 * 2
def baseEnd_2062677 : Nat := 156910331255426888955767

theorem tailTrace_2062677 : CollatzResearch.WordTrace tailWord_2062677 prefixEnd_2062677 156910331255426888955767 := by
  unfold tailWord_2062677
  simp only [CollatzResearch.WordTrace]
  refine ⟨75232010748280981030490285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50154673832187320686993523 75232010748280981030490285)
  ·
    refine ⟨28212004030605367886433857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75232010748280981030490285 28212004030605367886433857)
    ·
      refine ⟨21159003022954025914825393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28212004030605367886433857 21159003022954025914825393)
      ·
        refine ⟨15869252267215519436119045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21159003022954025914825393 15869252267215519436119045)
        ·
          refine ⟨2975484800102909894272321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15869252267215519436119045 2975484800102909894272321)
          ·
            refine ⟨2231613600077182420704241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2975484800102909894272321 2231613600077182420704241)
            ·
              refine ⟨1673710200057886815528181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2231613600077182420704241 1673710200057886815528181)
              ·
                refine ⟨156910331255426888955767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673710200057886815528181 156910331255426888955767)
                ·
                  rfl

theorem cell21_2062677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 5].length) (baseStart_2062677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062677 prefixEnd_2062677 := by exact prefixLift 2062677
  have htrace : WordTrace (prefixWord ++ tailWord_2062677) baseStart_2062677 baseEnd_2062677 := by
    simpa [prefixWord, tailWord_2062677, baseEnd_2062677] using wordTrace_append hprefix tailTrace_2062677
  have hstable : (prefixWord ++ tailWord_2062677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062677).length < 2 ^ (prefixWord ++ tailWord_2062677).sum := by decide
  have hdescent : baseEnd_2062677 < baseStart_2062677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062781 : List Nat := [1, 4, 1, 2, 2, 2, 2, 3, 4]
def baseStart_2062781 : Nat := 118140960795 + 2062781 * 2 ^ 59
def prefixEnd_2062781 : Nat := 4983230072969 + 3 ^ 40 * 2062781 * 2
def baseEnd_2062781 : Nat := 470754727983199597133755

theorem tailTrace_2062781 : CollatzResearch.WordTrace tailWord_2062781 prefixEnd_2062781 470754727983199597133755 := by
  unfold tailWord_2062781
  simp only [CollatzResearch.WordTrace]
  refine ⟨75235803939904206792276197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50157202626602804528184131 75235803939904206792276197)
  ·
    refine ⟨14106713238732038773551787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75235803939904206792276197 14106713238732038773551787)
    ·
      refine ⟨21160069858098058160327681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14106713238732038773551787 21160069858098058160327681)
      ·
        refine ⟨15870052393573543620245761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21160069858098058160327681 15870052393573543620245761)
        ·
          refine ⟨11902539295180157715184321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15870052393573543620245761 11902539295180157715184321)
          ·
            refine ⟨8926904471385118286388241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11902539295180157715184321 8926904471385118286388241)
            ·
              refine ⟨6695178353538838714791181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8926904471385118286388241 6695178353538838714791181)
              ·
                refine ⟨2510691882577064518046693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6695178353538838714791181 2510691882577064518046693)
                ·
                  refine ⟨470754727983199597133755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2510691882577064518046693 470754727983199597133755)
                  ·
                    rfl

theorem cell21_2062781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_2062781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062781 prefixEnd_2062781 := by exact prefixLift 2062781
  have htrace : WordTrace (prefixWord ++ tailWord_2062781) baseStart_2062781 baseEnd_2062781 := by
    simpa [prefixWord, tailWord_2062781, baseEnd_2062781] using wordTrace_append hprefix tailTrace_2062781
  have hstable : (prefixWord ++ tailWord_2062781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062781).length < 2 ^ (prefixWord ++ tailWord_2062781).sum := by decide
  have hdescent : baseEnd_2062781 < baseStart_2062781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062809 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 7]
def baseStart_2062809 : Nat := 118140960795 + 2062809 * 2 ^ 59
def prefixEnd_2062809 : Nat := 4983230072969 + 3 ^ 40 * 2062809 * 2
def baseEnd_2062809 : Nat := 470761117964677770667031

theorem tailTrace_2062809 : CollatzResearch.WordTrace tailWord_2062809 prefixEnd_2062809 470761117964677770667031 := by
  unfold tailWord_2062809
  simp only [CollatzResearch.WordTrace]
  refine ⟨75236825183802767574295481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50157883455868511716196987 75236825183802767574295481)
  ·
    refine ⟨56427618887852075680721611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75236825183802767574295481 56427618887852075680721611)
    ·
      refine ⟨84641428331778113521082417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56427618887852075680721611 84641428331778113521082417)
      ·
        refine ⟨63481071248833585140811813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84641428331778113521082417 63481071248833585140811813)
        ·
          refine ⟨11902700859156297213902215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63481071248833585140811813 11902700859156297213902215)
          ·
            refine ⟨17854051288734445820853323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11902700859156297213902215 17854051288734445820853323)
            ·
              refine ⟨26781076933101668731279985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17854051288734445820853323 26781076933101668731279985)
              ·
                refine ⟨20085807699826251548459989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26781076933101668731279985 20085807699826251548459989)
                ·
                  refine ⟨470761117964677770667031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20085807699826251548459989 470761117964677770667031)
                  ·
                    rfl

theorem cell21_2062809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 7].length) (baseStart_2062809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062809 prefixEnd_2062809 := by exact prefixLift 2062809
  have htrace : WordTrace (prefixWord ++ tailWord_2062809) baseStart_2062809 baseEnd_2062809 := by
    simpa [prefixWord, tailWord_2062809, baseEnd_2062809] using wordTrace_append hprefix tailTrace_2062809
  have hstable : (prefixWord ++ tailWord_2062809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062809).length < 2 ^ (prefixWord ++ tailWord_2062809).sum := by decide
  have hdescent : baseEnd_2062809 < baseStart_2062809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062826 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_2062826 : Nat := 118140960795 + 2062826 * 2 ^ 59
def prefixEnd_2062826 : Nat := 4983230072969 + 3 ^ 40 * 2062826 * 2
def baseEnd_2062826 : Nat := 470764997596289518883663

theorem tailTrace_2062826 : CollatzResearch.WordTrace tailWord_2062826 prefixEnd_2062826 470764997596289518883663 := by
  unfold tailWord_2062826
  simp only [CollatzResearch.WordTrace]
  refine ⟨18809361306185294869416083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50158296816494119651776221 18809361306185294869416083)
  ·
    refine ⟨28214041959277942304124125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18809361306185294869416083 28214041959277942304124125)
    ·
      refine ⟨10580265734729228364046547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28214041959277942304124125 10580265734729228364046547)
      ·
        refine ⟨15870398602093842546069821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10580265734729228364046547 15870398602093842546069821)
        ·
          refine ⟨5951399475785190954776183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15870398602093842546069821 5951399475785190954776183)
          ·
            refine ⟨8927099213677786432164275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5951399475785190954776183 8927099213677786432164275)
            ·
              refine ⟨13390648820516679648246413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8927099213677786432164275 13390648820516679648246413)
              ·
                refine ⟨5021493307693754868092405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13390648820516679648246413 5021493307693754868092405)
                ·
                  refine ⟨470764997596289518883663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5021493307693754868092405 470764997596289518883663)
                  ·
                    rfl

theorem cell21_2062826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_2062826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062826 prefixEnd_2062826 := by exact prefixLift 2062826
  have htrace : WordTrace (prefixWord ++ tailWord_2062826) baseStart_2062826 baseEnd_2062826 := by
    simpa [prefixWord, tailWord_2062826, baseEnd_2062826] using wordTrace_append hprefix tailTrace_2062826
  have hstable : (prefixWord ++ tailWord_2062826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062826).length < 2 ^ (prefixWord ++ tailWord_2062826).sum := by decide
  have hdescent : baseEnd_2062826 < baseStart_2062826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062860 : List Nat := [2, 2, 1, 2, 4, 3, 1, 3, 3]
def baseStart_2062860 : Nat := 118140960795 + 2062860 * 2 ^ 59
def prefixEnd_2062860 : Nat := 4983230072969 + 3 ^ 40 * 2062860 * 2
def baseEnd_2062860 : Nat := 470772756859513015316927

theorem tailTrace_2062860 : CollatzResearch.WordTrace tailWord_2062860 prefixEnd_2062860 470772756859513015316927 := by
  unfold tailWord_2062860
  simp only [CollatzResearch.WordTrace]
  refine ⟨37619342653309001642201017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50159123537745335522934689 37619342653309001642201017)
  ·
    refine ⟨28214506989981751231650763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37619342653309001642201017 28214506989981751231650763)
    ·
      refine ⟨42321760484972626847476145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28214506989981751231650763 42321760484972626847476145)
      ·
        refine ⟨31741320363729470135607109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42321760484972626847476145 31741320363729470135607109)
        ·
          refine ⟨5951497568199275650426333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31741320363729470135607109 5951497568199275650426333)
          ·
            refine ⟨2231811588074728368909875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5951497568199275650426333 2231811588074728368909875)
            ·
              refine ⟨3347717382112092553364813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2231811588074728368909875 3347717382112092553364813)
              ·
                refine ⟨1255394018292034707511805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3347717382112092553364813 1255394018292034707511805)
                ·
                  refine ⟨470772756859513015316927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255394018292034707511805 470772756859513015316927)
                  ·
                    rfl

theorem cell21_2062860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_2062860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062860 prefixEnd_2062860 := by exact prefixLift 2062860
  have htrace : WordTrace (prefixWord ++ tailWord_2062860) baseStart_2062860 baseEnd_2062860 := by
    simpa [prefixWord, tailWord_2062860, baseEnd_2062860] using wordTrace_append hprefix tailTrace_2062860
  have hstable : (prefixWord ++ tailWord_2062860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062860).length < 2 ^ (prefixWord ++ tailWord_2062860).sum := by decide
  have hdescent : baseEnd_2062860 < baseStart_2062860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2062888 : List Nat := [2, 1, 5, 2, 1, 2, 2, 6]
def baseStart_2062888 : Nat := 118140960795 + 2062888 * 2 ^ 59
def prefixEnd_2062888 : Nat := 4983230072969 + 3 ^ 40 * 2062888 * 2
def baseEnd_2062888 : Nat := 156926382280330396283401

theorem tailTrace_2062888 : CollatzResearch.WordTrace tailWord_2062888 prefixEnd_2062888 156926382280330396283401 := by
  unfold tailWord_2062888
  simp only [CollatzResearch.WordTrace]
  refine ⟨37619853275258282033210659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50159804367011042710947545 37619853275258282033210659)
  ·
    refine ⟨56429779912887423049815989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37619853275258282033210659 56429779912887423049815989)
    ·
      refine ⟨5290291866833195910920249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56429779912887423049815989 5290291866833195910920249)
      ·
        refine ⟨3967718900124896933190187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5290291866833195910920249 3967718900124896933190187)
        ·
          refine ⟨5951578350187345399785281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3967718900124896933190187 5951578350187345399785281)
          ·
            refine ⟨4463683762640509049838961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5951578350187345399785281 4463683762640509049838961)
            ·
              refine ⟨3347762821980381787379221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4463683762640509049838961 3347762821980381787379221)
              ·
                refine ⟨156926382280330396283401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3347762821980381787379221 156926382280330396283401)
                ·
                  rfl

theorem cell21_2062888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_2062888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2062888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2062888 prefixEnd_2062888 := by exact prefixLift 2062888
  have htrace : WordTrace (prefixWord ++ tailWord_2062888) baseStart_2062888 baseEnd_2062888 := by
    simpa [prefixWord, tailWord_2062888, baseEnd_2062888] using wordTrace_append hprefix tailTrace_2062888
  have hstable : (prefixWord ++ tailWord_2062888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2062888).length < 2 ^ (prefixWord ++ tailWord_2062888).sum := by decide
  have hdescent : baseEnd_2062888 < baseStart_2062888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2062888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063023 : List Nat := [1, 1, 2, 1, 2, 5, 4, 5]
def baseStart_2063023 : Nat := 118140960795 + 2063023 * 2 ^ 59
def prefixEnd_2063023 : Nat := 4983230072969 + 3 ^ 40 * 2063023 * 2
def baseEnd_2063023 : Nat := 156936651893420318033309

theorem tailTrace_2063023 : CollatzResearch.WordTrace tailWord_2063023 prefixEnd_2063023 156936651893420318033309 := by
  unfold tailWord_2063023
  simp only [CollatzResearch.WordTrace]
  refine ⟨75244630405027482122585723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50163086936684988081723815 75244630405027482122585723)
  ·
    refine ⟨112866945607541223183878585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75244630405027482122585723 112866945607541223183878585)
    ·
      refine ⟨84650209205655917387908939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112866945607541223183878585 84650209205655917387908939)
      ·
        refine ⟨126975313808483876081863409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84650209205655917387908939 126975313808483876081863409)
        ·
          refine ⟨95231485356362907061397557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 126975313808483876081863409 95231485356362907061397557)
          ·
            refine ⟨8927951752159022537006021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95231485356362907061397557 8927951752159022537006021)
            ·
              refine ⟨1673990953529816725688629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8927951752159022537006021 1673990953529816725688629)
              ·
                refine ⟨156936651893420318033309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1673990953529816725688629 156936651893420318033309)
                ·
                  rfl

theorem cell21_2063023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 4, 5].length) (baseStart_2063023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063023 prefixEnd_2063023 := by exact prefixLift 2063023
  have htrace : WordTrace (prefixWord ++ tailWord_2063023) baseStart_2063023 baseEnd_2063023 := by
    simpa [prefixWord, tailWord_2063023, baseEnd_2063023] using wordTrace_append hprefix tailTrace_2063023
  have hstable : (prefixWord ++ tailWord_2063023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063023).length < 2 ^ (prefixWord ++ tailWord_2063023).sum := by decide
  have hdescent : baseEnd_2063023 < baseStart_2063023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063046 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2063046 : Nat := 118140960795 + 2063046 * 2 ^ 59
def prefixEnd_2063046 : Nat := 4983230072969 + 3 ^ 40 * 2063046 * 2
def baseEnd_2063046 : Nat := 470815204593618025216547

theorem tailTrace_2063046 : CollatzResearch.WordTrace tailWord_2063046 prefixEnd_2063046 470815204593618025216547 := by
  unfold tailWord_2063046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351420915123254907833531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 50163646189296104700448661 2351420915123254907833531)
  ·
    refine ⟨3527131372684882361750297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2351420915123254907833531 3527131372684882361750297)
    ·
      refine ⟨2645348529513661771312723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3527131372684882361750297 2645348529513661771312723)
      ·
        refine ⟨3968022794270492656969085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645348529513661771312723 3968022794270492656969085)
        ·
          refine ⟨1488008547851434746363407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3968022794270492656969085 1488008547851434746363407)
          ·
            refine ⟨2232012821777152119545111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488008547851434746363407 2232012821777152119545111)
            ·
              refine ⟨3348019232665728179317667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232012821777152119545111 3348019232665728179317667)
              ·
                refine ⟨5022028848998592268976501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348019232665728179317667 5022028848998592268976501)
                ·
                  refine ⟨470815204593618025216547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022028848998592268976501 470815204593618025216547)
                  ·
                    rfl

theorem cell21_2063046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2063046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063046 prefixEnd_2063046 := by exact prefixLift 2063046
  have htrace : WordTrace (prefixWord ++ tailWord_2063046) baseStart_2063046 baseEnd_2063046 := by
    simpa [prefixWord, tailWord_2063046, baseEnd_2063046] using wordTrace_append hprefix tailTrace_2063046
  have hstable : (prefixWord ++ tailWord_2063046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063046).length < 2 ^ (prefixWord ++ tailWord_2063046).sum := by decide
  have hdescent : baseEnd_2063046 < baseStart_2063046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063054 : List Nat := [4, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_2063054 : Nat := 118140960795 + 2063054 * 2 ^ 59
def prefixEnd_2063054 : Nat := 4983230072969 + 3 ^ 40 * 2063054 * 2
def baseEnd_2063054 : Nat := 470817030302611789083197

theorem tailTrace_2063054 : CollatzResearch.WordTrace tailWord_2063054 prefixEnd_2063054 470817030302611789083197 := by
  unfold tailWord_2063054
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405720133489396802120527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50163840711943449611309477 9405720133489396802120527)
  ·
    refine ⟨14108580200234095203180791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9405720133489396802120527 14108580200234095203180791)
    ·
      refine ⟨21162870300351142804771187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14108580200234095203180791 21162870300351142804771187)
      ·
        refine ⟨31744305450526714207156781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21162870300351142804771187 31744305450526714207156781)
        ·
          refine ⟨11904114543947517827683793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31744305450526714207156781 11904114543947517827683793)
          ·
            refine ⟨8928085907960638370762845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11904114543947517827683793 8928085907960638370762845)
            ·
              refine ⟨3348032215485239389036067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8928085907960638370762845 3348032215485239389036067)
              ·
                refine ⟨5022048323227859083554101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348032215485239389036067 5022048323227859083554101)
                ·
                  refine ⟨470817030302611789083197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022048323227859083554101 470817030302611789083197)
                  ·
                    rfl

theorem cell21_2063054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_2063054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063054 prefixEnd_2063054 := by exact prefixLift 2063054
  have htrace : WordTrace (prefixWord ++ tailWord_2063054) baseStart_2063054 baseEnd_2063054 := by
    simpa [prefixWord, tailWord_2063054, baseEnd_2063054] using wordTrace_append hprefix tailTrace_2063054
  have hstable : (prefixWord ++ tailWord_2063054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063054).length < 2 ^ (prefixWord ++ tailWord_2063054).sum := by decide
  have hdescent : baseEnd_2063054 < baseStart_2063054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063060 : List Nat := [2, 4, 1, 3, 3, 1, 2, 1, 4]
def baseStart_2063060 : Nat := 118140960795 + 2063060 * 2 ^ 59
def prefixEnd_2063060 : Nat := 4983230072969 + 3 ^ 40 * 2063060 * 2
def baseEnd_2063060 : Nat := 470818399584357111983185

theorem tailTrace_2063060 : CollatzResearch.WordTrace tailWord_2063060 prefixEnd_2063060 470818399584357111983185 := by
  unfold tailWord_2063060
  simp only [CollatzResearch.WordTrace]
  refine ⟨37622989952946718720841317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50163986603928958294455089 37622989952946718720841317)
  ·
    refine ⟨7054310616177509760157747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37622989952946718720841317 7054310616177509760157747)
    ·
      refine ⟨10581465924266264640236621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7054310616177509760157747 10581465924266264640236621)
      ·
        refine ⟨3968049721599849240088733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10581465924266264640236621 3968049721599849240088733)
        ·
          refine ⟨1488018645599943465033275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3968049721599849240088733 1488018645599943465033275)
          ·
            refine ⟨2232027968399915197549913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488018645599943465033275 2232027968399915197549913)
            ·
              refine ⟨1674020976299936398162435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232027968399915197549913 1674020976299936398162435)
              ·
                refine ⟨2511031464449904597243653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674020976299936398162435 2511031464449904597243653)
                ·
                  refine ⟨470818399584357111983185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511031464449904597243653 470818399584357111983185)
                  ·
                    rfl

theorem cell21_2063060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_2063060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063060 prefixEnd_2063060 := by exact prefixLift 2063060
  have htrace : WordTrace (prefixWord ++ tailWord_2063060) baseStart_2063060 baseEnd_2063060 := by
    simpa [prefixWord, tailWord_2063060, baseEnd_2063060] using wordTrace_append hprefix tailTrace_2063060
  have hstable : (prefixWord ++ tailWord_2063060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063060).length < 2 ^ (prefixWord ++ tailWord_2063060).sum := by decide
  have hdescent : baseEnd_2063060 < baseStart_2063060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063102 : List Nat := [4, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2063102 : Nat := 118140960795 + 2063102 * 2 ^ 59
def prefixEnd_2063102 : Nat := 4983230072969 + 3 ^ 40 * 2063102 * 2
def baseEnd_2063102 : Nat := 470827984556574372283099

theorem tailTrace_2063102 : CollatzResearch.WordTrace tailWord_2063102 prefixEnd_2063102 470827984556574372283099 := by
  unfold tailWord_2063102
  simp only [CollatzResearch.WordTrace]
  refine ⟨9405938971467659826838945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50165007847827519076474373 9405938971467659826838945)
  ·
    refine ⟨7054454228600744870129209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9405938971467659826838945 7054454228600744870129209)
    ·
      refine ⟨5290840671450558652596907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7054454228600744870129209 5290840671450558652596907)
      ·
        refine ⟨7936261007175837978895361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290840671450558652596907 7936261007175837978895361)
        ·
          refine ⟨5952195755381878484171521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7936261007175837978895361 5952195755381878484171521)
          ·
            refine ⟨4464146816536408863128641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5952195755381878484171521 4464146816536408863128641)
            ·
              refine ⟨3348110112402306647346481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4464146816536408863128641 3348110112402306647346481)
              ·
                refine ⟨2511082584301729985509861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348110112402306647346481 2511082584301729985509861)
                ·
                  refine ⟨470827984556574372283099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511082584301729985509861 470827984556574372283099)
                  ·
                    rfl

theorem cell21_2063102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2063102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063102 prefixEnd_2063102 := by exact prefixLift 2063102
  have htrace : WordTrace (prefixWord ++ tailWord_2063102) baseStart_2063102 baseEnd_2063102 := by
    simpa [prefixWord, tailWord_2063102, baseEnd_2063102] using wordTrace_append hprefix tailTrace_2063102
  have hstable : (prefixWord ++ tailWord_2063102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063102).length < 2 ^ (prefixWord ++ tailWord_2063102).sum := by decide
  have hdescent : baseEnd_2063102 < baseStart_2063102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063133 : List Nat := [1, 4, 2, 4, 1, 1, 3, 5]
def baseStart_2063133 : Nat := 118140960795 + 2063133 * 2 ^ 59
def prefixEnd_2063133 : Nat := 4983230072969 + 3 ^ 40 * 2063133 * 2
def baseEnd_2063133 : Nat := 156945019726308402422123

theorem tailTrace_2063133 : CollatzResearch.WordTrace tailWord_2063133 prefixEnd_2063133 156945019726308402422123 := by
  unfold tailWord_2063133
  simp only [CollatzResearch.WordTrace]
  refine ⟨75248642434628970909090053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50165761623085980606060035 75248642434628970909090053)
  ·
    refine ⟨14109120456492932045454385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75248642434628970909090053 14109120456492932045454385)
    ·
      refine ⟨10581840342369699034090789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14109120456492932045454385 10581840342369699034090789)
      ·
        refine ⟨1984095064194318568892023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10581840342369699034090789 1984095064194318568892023)
        ·
          refine ⟨2976142596291477853338035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984095064194318568892023 2976142596291477853338035)
          ·
            refine ⟨4464213894437216780007053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976142596291477853338035 4464213894437216780007053)
            ·
              refine ⟨1674080210413956292502645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4464213894437216780007053 1674080210413956292502645)
              ·
                refine ⟨156945019726308402422123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1674080210413956292502645 156945019726308402422123)
                ·
                  rfl

theorem cell21_2063133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 5].length) (baseStart_2063133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063133 prefixEnd_2063133 := by exact prefixLift 2063133
  have htrace : WordTrace (prefixWord ++ tailWord_2063133) baseStart_2063133 baseEnd_2063133 := by
    simpa [prefixWord, tailWord_2063133, baseEnd_2063133] using wordTrace_append hprefix tailTrace_2063133
  have hstable : (prefixWord ++ tailWord_2063133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063133).length < 2 ^ (prefixWord ++ tailWord_2063133).sum := by decide
  have hdescent : baseEnd_2063133 < baseStart_2063133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063144 : List Nat := [2, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_2063144 : Nat := 118140960795 + 2063144 * 2 ^ 59
def prefixEnd_2063144 : Nat := 4983230072969 + 3 ^ 40 * 2063144 * 2
def baseEnd_2063144 : Nat := 470837569528791632583013

theorem tailTrace_2063144 : CollatzResearch.WordTrace tailWord_2063144 prefixEnd_2063144 470837569528791632583013 := by
  unfold tailWord_2063144
  simp only [CollatzResearch.WordTrace]
  refine ⟨37624521818794559893870243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50166029091726079858493657 37624521818794559893870243)
  ·
    refine ⟨56436782728191839840805365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37624521818794559893870243 56436782728191839840805365)
    ·
      refine ⟨5290948380767984985075503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56436782728191839840805365 5290948380767984985075503)
      ·
        refine ⟨7936422571151977477613255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5290948380767984985075503 7936422571151977477613255)
        ·
          refine ⟨11904633856727966216419883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7936422571151977477613255 11904633856727966216419883)
          ·
            refine ⟨17856950785091949324629825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11904633856727966216419883 17856950785091949324629825)
            ·
              refine ⟨13392713088818961993472369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17856950785091949324629825 13392713088818961993472369)
              ·
                refine ⟨10044534816614221495104277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13392713088818961993472369 10044534816614221495104277)
                ·
                  refine ⟨470837569528791632583013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10044534816614221495104277 470837569528791632583013)
                  ·
                    rfl

theorem cell21_2063144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_2063144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063144 prefixEnd_2063144 := by exact prefixLift 2063144
  have htrace : WordTrace (prefixWord ++ tailWord_2063144) baseStart_2063144 baseEnd_2063144 := by
    simpa [prefixWord, tailWord_2063144, baseEnd_2063144] using wordTrace_append hprefix tailTrace_2063144
  have hstable : (prefixWord ++ tailWord_2063144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063144).length < 2 ^ (prefixWord ++ tailWord_2063144).sum := by decide
  have hdescent : baseEnd_2063144 < baseStart_2063144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063189 : List Nat := [1, 3, 2, 2, 2, 1, 1, 4, 5]
def baseStart_2063189 : Nat := 118140960795 + 2063189 * 2 ^ 59
def prefixEnd_2063189 : Nat := 4983230072969 + 3 ^ 40 * 2063189 * 2
def baseEnd_2063189 : Nat := 470847839141881554332921

theorem tailTrace_2063189 : CollatzResearch.WordTrace tailWord_2063189 prefixEnd_2063189 470847839141881554332921 := by
  unfold tailWord_2063189
  simp only [CollatzResearch.WordTrace]
  refine ⟨75250684922426092473128621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50167123281617394982085747 75250684922426092473128621)
  ·
    refine ⟨28219006845909784677423233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75250684922426092473128621 28219006845909784677423233)
    ·
      refine ⟨21164255134432338508067425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28219006845909784677423233 21164255134432338508067425)
      ·
        refine ⟨15873191350824253881050569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21164255134432338508067425 15873191350824253881050569)
        ·
          refine ⟨11904893513118190410787927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15873191350824253881050569 11904893513118190410787927)
          ·
            refine ⟨17857340269677285616181891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11904893513118190410787927 17857340269677285616181891)
            ·
              refine ⟨26786010404515928424272837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17857340269677285616181891 26786010404515928424272837)
              ·
                refine ⟨5022376950846736579551157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26786010404515928424272837 5022376950846736579551157)
                ·
                  refine ⟨470847839141881554332921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022376950846736579551157 470847839141881554332921)
                  ·
                    rfl

theorem cell21_2063189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_2063189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063189 prefixEnd_2063189 := by exact prefixLift 2063189
  have htrace : WordTrace (prefixWord ++ tailWord_2063189) baseStart_2063189 baseEnd_2063189 := by
    simpa [prefixWord, tailWord_2063189, baseEnd_2063189] using wordTrace_append hprefix tailTrace_2063189
  have hstable : (prefixWord ++ tailWord_2063189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063189).length < 2 ^ (prefixWord ++ tailWord_2063189).sum := by decide
  have hdescent : baseEnd_2063189 < baseStart_2063189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063237 : List Nat := [1, 3, 1, 1, 3, 3, 4, 1, 4]
def baseStart_2063237 : Nat := 118140960795 + 2063237 * 2 ^ 59
def prefixEnd_2063237 : Nat := 4983230072969 + 3 ^ 40 * 2063237 * 2
def baseEnd_2063237 : Nat := 470858793395844137532823

theorem tailTrace_2063237 : CollatzResearch.WordTrace tailWord_2063237 prefixEnd_2063237 470858793395844137532823 := by
  unfold tailWord_2063237
  simp only [CollatzResearch.WordTrace]
  refine ⟨75252435626252196670875965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50168290417501464447250643 75252435626252196670875965)
  ·
    refine ⟨28219663359844573751578487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75252435626252196670875965 28219663359844573751578487)
    ·
      refine ⟨42329495039766860627367731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28219663359844573751578487 42329495039766860627367731)
      ·
        refine ⟨63494242559650290941051597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42329495039766860627367731 63494242559650290941051597)
        ·
          refine ⟨23810340959868859102894349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63494242559650290941051597 23810340959868859102894349)
          ·
            refine ⟨8928877859950822163585381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23810340959868859102894349 8928877859950822163585381)
            ·
              refine ⟨1674164598740779155672259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8928877859950822163585381 1674164598740779155672259)
              ·
                refine ⟨2511246898111168733508389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674164598740779155672259 2511246898111168733508389)
                ·
                  refine ⟨470858793395844137532823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511246898111168733508389 470858793395844137532823)
                  ·
                    rfl

theorem cell21_2063237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 4].length) (baseStart_2063237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063237 prefixEnd_2063237 := by exact prefixLift 2063237
  have htrace : WordTrace (prefixWord ++ tailWord_2063237) baseStart_2063237 baseEnd_2063237 := by
    simpa [prefixWord, tailWord_2063237, baseEnd_2063237] using wordTrace_append hprefix tailTrace_2063237
  have hstable : (prefixWord ++ tailWord_2063237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063237).length < 2 ^ (prefixWord ++ tailWord_2063237).sum := by decide
  have hdescent : baseEnd_2063237 < baseStart_2063237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063296 : List Nat := [2, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_2063296 : Nat := 118140960795 + 2063296 * 2 ^ 59
def prefixEnd_2063296 : Nat := 4983230072969 + 3 ^ 40 * 2063296 * 2
def baseEnd_2063296 : Nat := 470872257999673146049369

theorem tailTrace_2063296 : CollatzResearch.WordTrace tailWord_2063296 prefixEnd_2063296 470872257999673146049369 := by
  unfold tailWord_2063296
  simp only [CollatzResearch.WordTrace]
  refine ⟨37627293766519224873636871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50169725022025633164849161 37627293766519224873636871)
  ·
    refine ⟨56440940649778837310455307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37627293766519224873636871 56440940649778837310455307)
    ·
      refine ⟨84661410974668255965682961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56440940649778837310455307 84661410974668255965682961)
      ·
        refine ⟨63496058231001191974262221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84661410974668255965682961 63496058231001191974262221)
        ·
          refine ⟨23811021836625446990348333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63496058231001191974262221 23811021836625446990348333)
          ·
            refine ⟨8929133188734542621380625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23811021836625446990348333 8929133188734542621380625)
            ·
              refine ⟨6696849891550906966035469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8929133188734542621380625 6696849891550906966035469)
              ·
                refine ⟨2511318709331590112263301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6696849891550906966035469 2511318709331590112263301)
                ·
                  refine ⟨470872257999673146049369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511318709331590112263301 470872257999673146049369)
                  ·
                    rfl

theorem cell21_2063296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_2063296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063296 prefixEnd_2063296 := by exact prefixLift 2063296
  have htrace : WordTrace (prefixWord ++ tailWord_2063296) baseStart_2063296 baseEnd_2063296 := by
    simpa [prefixWord, tailWord_2063296, baseEnd_2063296] using wordTrace_append hprefix tailTrace_2063296
  have hstable : (prefixWord ++ tailWord_2063296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063296).length < 2 ^ (prefixWord ++ tailWord_2063296).sum := by decide
  have hdescent : baseEnd_2063296 < baseStart_2063296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063330 : List Nat := [3, 3, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2063330 : Nat := 118140960795 + 2063330 * 2 ^ 59
def prefixEnd_2063330 : Nat := 4983230072969 + 3 ^ 40 * 2063330 * 2
def baseEnd_2063330 : Nat := 470880017262896642482633

theorem tailTrace_2063330 : CollatzResearch.WordTrace tailWord_2063330 prefixEnd_2063330 470880017262896642482633 := by
  unfold tailWord_2063330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18813956903728818388502861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50170551743276849036007629 18813956903728818388502861)
  ·
    refine ⟨7055233838898306895688573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18813956903728818388502861 7055233838898306895688573)
    ·
      refine ⟨2645712689586865085883215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7055233838898306895688573 2645712689586865085883215)
      ·
        refine ⟨3968569034380297628824823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2645712689586865085883215 3968569034380297628824823)
        ·
          refine ⟨5952853551570446443237235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3968569034380297628824823 5952853551570446443237235)
          ·
            refine ⟨8929280327355669664855853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5952853551570446443237235 8929280327355669664855853)
            ·
              refine ⟨3348480122758376124320945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8929280327355669664855853 3348480122758376124320945)
              ·
                refine ⟨2511360092068782093240709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348480122758376124320945 2511360092068782093240709)
                ·
                  refine ⟨470880017262896642482633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511360092068782093240709 470880017262896642482633)
                  ·
                    rfl

theorem cell21_2063330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2063330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063330 prefixEnd_2063330 := by exact prefixLift 2063330
  have htrace : WordTrace (prefixWord ++ tailWord_2063330) baseStart_2063330 baseEnd_2063330 := by
    simpa [prefixWord, tailWord_2063330, baseEnd_2063330] using wordTrace_append hprefix tailTrace_2063330
  have hstable : (prefixWord ++ tailWord_2063330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063330).length < 2 ^ (prefixWord ++ tailWord_2063330).sum := by decide
  have hdescent : baseEnd_2063330 < baseStart_2063330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063378 : List Nat := [3, 2, 5, 1, 2, 1, 7]
def baseStart_2063378 : Nat := 118140960795 + 2063378 * 2 ^ 59
def prefixEnd_2063378 : Nat := 4983230072969 + 3 ^ 40 * 2063378 * 2
def baseEnd_2063378 : Nat := 52321219057428802853615

theorem tailTrace_2063378 : CollatzResearch.WordTrace tailWord_2063378 prefixEnd_2063378 52321219057428802853615 := by
  unfold tailWord_2063378
  simp only [CollatzResearch.WordTrace]
  refine ⟨18814394579685344437939697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50171718879160918501172525 18814394579685344437939697)
  ·
    refine ⟨14110795934764008328454773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18814394579685344437939697 14110795934764008328454773)
    ·
      refine ⟨1322887118884125780792635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14110795934764008328454773 1322887118884125780792635)
      ·
        refine ⟨1984330678326188671188953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322887118884125780792635 1984330678326188671188953)
        ·
          refine ⟨1488248008744641503391715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984330678326188671188953 1488248008744641503391715)
          ·
            refine ⟨2232372013116962255087573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488248008744641503391715 2232372013116962255087573)
            ·
              refine ⟨52321219057428802853615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2232372013116962255087573 52321219057428802853615)
              ·
                rfl

theorem cell21_2063378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 7].length) (baseStart_2063378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063378 prefixEnd_2063378 := by exact prefixLift 2063378
  have htrace : WordTrace (prefixWord ++ tailWord_2063378) baseStart_2063378 baseEnd_2063378 := by
    simpa [prefixWord, tailWord_2063378, baseEnd_2063378] using wordTrace_append hprefix tailTrace_2063378
  have hstable : (prefixWord ++ tailWord_2063378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063378).length < 2 ^ (prefixWord ++ tailWord_2063378).sum := by decide
  have hdescent : baseEnd_2063378 < baseStart_2063378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063392 : List Nat := [2, 1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_2063392 : Nat := 118140960795 + 2063392 * 2 ^ 59
def prefixEnd_2063392 : Nat := 4983230072969 + 3 ^ 40 * 2063392 * 2
def baseEnd_2063392 : Nat := 470894166507598312449173

theorem tailTrace_2063392 : CollatzResearch.WordTrace tailWord_2063392 prefixEnd_2063392 470894166507598312449173 := by
  unfold tailWord_2063392
  simp only [CollatzResearch.WordTrace]
  refine ⟨37629044470345329071384215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50172059293793772095178953 37629044470345329071384215)
  ·
    refine ⟨56443566705517993607076323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37629044470345329071384215 56443566705517993607076323)
    ·
      refine ⟨84665350058276990410614485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56443566705517993607076323 84665350058276990410614485)
      ·
        refine ⟨1984344141990866962748777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 84665350058276990410614485 1984344141990866962748777)
        ·
          refine ⟨1488258106493150222061583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1984344141990866962748777 1488258106493150222061583)
          ·
            refine ⟨2232387159739725333092375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488258106493150222061583 2232387159739725333092375)
            ·
              refine ⟨3348580739609587999638563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232387159739725333092375 3348580739609587999638563)
              ·
                refine ⟨5022871109414381999457845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3348580739609587999638563 5022871109414381999457845)
                ·
                  refine ⟨470894166507598312449173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5022871109414381999457845 470894166507598312449173)
                  ·
                    rfl

theorem cell21_2063392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_2063392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063392 prefixEnd_2063392 := by exact prefixLift 2063392
  have htrace : WordTrace (prefixWord ++ tailWord_2063392) baseStart_2063392 baseEnd_2063392 := by
    simpa [prefixWord, tailWord_2063392, baseEnd_2063392] using wordTrace_append hprefix tailTrace_2063392
  have hstable : (prefixWord ++ tailWord_2063392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063392).length < 2 ^ (prefixWord ++ tailWord_2063392).sum := by decide
  have hdescent : baseEnd_2063392 < baseStart_2063392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063448 : List Nat := [2, 1, 2, 2, 1, 3, 4, 2, 4]
def baseStart_2063448 : Nat := 118140960795 + 2063448 * 2 ^ 59
def prefixEnd_2063448 : Nat := 4983230072969 + 3 ^ 40 * 2063448 * 2
def baseEnd_2063448 : Nat := 470906946470554659515725

theorem tailTrace_2063448 : CollatzResearch.WordTrace tailWord_2063448 prefixEnd_2063448 470906946470554659515725 := by
  unfold tailWord_2063448
  simp only [CollatzResearch.WordTrace]
  refine ⟨37630065714243889853403499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50173420952325186471204665 37630065714243889853403499)
  ·
    refine ⟨56445098571365834780105249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37630065714243889853403499 56445098571365834780105249)
    ·
      refine ⟨42333823928524376085078937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56445098571365834780105249 42333823928524376085078937)
      ·
        refine ⟨31750367946393282063809203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42333823928524376085078937 31750367946393282063809203)
        ·
          refine ⟨47625551919589923095713805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31750367946393282063809203 47625551919589923095713805)
          ·
            refine ⟨17859581969846221160892677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47625551919589923095713805 17859581969846221160892677)
            ·
              refine ⟨3348671619346166467667377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17859581969846221160892677 3348671619346166467667377)
              ·
                refine ⟨2511503714509624850750533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3348671619346166467667377 2511503714509624850750533)
                ·
                  refine ⟨470906946470554659515725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511503714509624850750533 470906946470554659515725)
                  ·
                    rfl

theorem cell21_2063448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 2, 4].length) (baseStart_2063448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063448 prefixEnd_2063448 := by exact prefixLift 2063448
  have htrace : WordTrace (prefixWord ++ tailWord_2063448) baseStart_2063448 baseEnd_2063448 := by
    simpa [prefixWord, tailWord_2063448, baseEnd_2063448] using wordTrace_append hprefix tailTrace_2063448
  have hstable : (prefixWord ++ tailWord_2063448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063448).length < 2 ^ (prefixWord ++ tailWord_2063448).sum := by decide
  have hdescent : baseEnd_2063448 < baseStart_2063448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063538 : List Nat := [3, 2, 1, 1, 1, 5, 1, 7]
def baseStart_2063538 : Nat := 118140960795 + 2063538 * 2 ^ 59
def prefixEnd_2063538 : Nat := 4983230072969 + 3 ^ 40 * 2063538 * 2
def baseEnd_2063538 : Nat := 156975828565578167671847

theorem tailTrace_2063538 : CollatzResearch.WordTrace tailWord_2063538 prefixEnd_2063538 156975828565578167671847 := by
  unfold tailWord_2063538
  simp only [CollatzResearch.WordTrace]
  refine ⟨18815853499540431269395817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50175609332107816718388845 18815853499540431269395817)
  ·
    refine ⟨14111890124655323452046863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18815853499540431269395817 14111890124655323452046863)
    ·
      refine ⟨21167835186982985178070295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14111890124655323452046863 21167835186982985178070295)
      ·
        refine ⟨31751752780474477767105443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21167835186982985178070295 31751752780474477767105443)
        ·
          refine ⟨47627629170711716650658165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31751752780474477767105443 47627629170711716650658165)
          ·
            refine ⟨4465090234754223435999203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47627629170711716650658165 4465090234754223435999203)
            ·
              refine ⟨6697635352131335153998805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465090234754223435999203 6697635352131335153998805)
              ·
                refine ⟨156975828565578167671847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6697635352131335153998805 156975828565578167671847)
                ·
                  rfl

theorem cell21_2063538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_2063538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063538 prefixEnd_2063538 := by exact prefixLift 2063538
  have htrace : WordTrace (prefixWord ++ tailWord_2063538) baseStart_2063538 baseEnd_2063538 := by
    simpa [prefixWord, tailWord_2063538, baseEnd_2063538] using wordTrace_append hprefix tailTrace_2063538
  have hstable : (prefixWord ++ tailWord_2063538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063538).length < 2 ^ (prefixWord ++ tailWord_2063538).sum := by decide
  have hdescent : baseEnd_2063538 < baseStart_2063538 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063572 : List Nat := [2, 4, 1, 4, 1, 1, 2, 6]
def baseStart_2063572 : Nat := 118140960795 + 2063572 * 2 ^ 59
def prefixEnd_2063572 : Nat := 4983230072969 + 3 ^ 40 * 2063572 * 2
def baseEnd_2063572 : Nat := 156978414986652666482935

theorem tailTrace_2063572 : CollatzResearch.WordTrace tailWord_2063572 prefixEnd_2063572 156978414986652666482935 := by
  unfold tailWord_2063572
  simp only [CollatzResearch.WordTrace]
  refine ⟨37632327040019274442160485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50176436053359032589547313 37632327040019274442160485)
  ·
    refine ⟨7056061320003613957905091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37632327040019274442160485 7056061320003613957905091)
    ·
      refine ⟨10584091980005420936857637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7056061320003613957905091 10584091980005420936857637)
      ·
        refine ⟨1984517246251016425660807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10584091980005420936857637 1984517246251016425660807)
        ·
          refine ⟨2976775869376524638491211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984517246251016425660807 2976775869376524638491211)
          ·
            refine ⟨4465163804064786957736817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2976775869376524638491211 4465163804064786957736817)
            ·
              refine ⟨3348872853048590218302613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4465163804064786957736817 3348872853048590218302613)
              ·
                refine ⟨156978414986652666482935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3348872853048590218302613 156978414986652666482935)
                ·
                  rfl

theorem cell21_2063572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_2063572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063572 prefixEnd_2063572 := by exact prefixLift 2063572
  have htrace : WordTrace (prefixWord ++ tailWord_2063572) baseStart_2063572 baseEnd_2063572 := by
    simpa [prefixWord, tailWord_2063572, baseEnd_2063572] using wordTrace_append hprefix tailTrace_2063572
  have hstable : (prefixWord ++ tailWord_2063572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063572).length < 2 ^ (prefixWord ++ tailWord_2063572).sum := by decide
  have hdescent : baseEnd_2063572 < baseStart_2063572 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063614 : List Nat := [4, 2, 2, 1, 1, 11]
def baseStart_2063614 : Nat := 118140960795 + 2063614 * 2 ^ 59
def prefixEnd_2063614 : Nat := 4983230072969 + 3 ^ 40 * 2063614 * 2
def baseEnd_2063614 : Nat := 17442401108599083694397

theorem tailTrace_2063614 : CollatzResearch.WordTrace tailWord_2063614 prefixEnd_2063614 17442401108599083694397 := by
  unfold tailWord_2063614
  simp only [CollatzResearch.WordTrace]
  refine ⟨9408273243235798757168737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50177457297257593371566597 9408273243235798757168737)
  ·
    refine ⟨7056204932426849067876553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9408273243235798757168737 7056204932426849067876553)
    ·
      refine ⟨5292153699320136800907415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7056204932426849067876553 5292153699320136800907415)
      ·
        refine ⟨7938230548980205201361123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292153699320136800907415 7938230548980205201361123)
        ·
          refine ⟨11907345823470307802041685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938230548980205201361123 11907345823470307802041685)
          ·
            refine ⟨17442401108599083694397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11907345823470307802041685 17442401108599083694397)
            ·
              rfl

theorem cell21_2063614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 11].length) (baseStart_2063614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063614 prefixEnd_2063614 := by exact prefixLift 2063614
  have htrace : WordTrace (prefixWord ++ tailWord_2063614) baseStart_2063614 baseEnd_2063614 := by
    simpa [prefixWord, tailWord_2063614, baseEnd_2063614] using wordTrace_append hprefix tailTrace_2063614
  have hstable : (prefixWord ++ tailWord_2063614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063614).length < 2 ^ (prefixWord ++ tailWord_2063614).sum := by decide
  have hdescent : baseEnd_2063614 < baseStart_2063614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063620 : List Nat := [2, 3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_2063620 : Nat := 118140960795 + 2063620 * 2 ^ 59
def prefixEnd_2063620 : Nat := 4983230072969 + 3 ^ 40 * 2063620 * 2
def baseEnd_2063620 : Nat := 470946199213920582648707

theorem tailTrace_2063620 : CollatzResearch.WordTrace tailWord_2063620 prefixEnd_2063620 470946199213920582648707 := by
  unfold tailWord_2063620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37633202391932326541034157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50177603189243102054712209 37633202391932326541034157)
  ·
    refine ⟨14112450896974622452887809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37633202391932326541034157 14112450896974622452887809)
    ·
      refine ⟨10584338172730966839665857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14112450896974622452887809 10584338172730966839665857)
      ·
        refine ⟨7938253629548225129749393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10584338172730966839665857 7938253629548225129749393)
        ·
          refine ⟨5953690222161168847312045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7938253629548225129749393 5953690222161168847312045)
          ·
            refine ⟨2232633833310438317742017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5953690222161168847312045 2232633833310438317742017)
            ·
              refine ⟨1674475374982828738306513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232633833310438317742017 1674475374982828738306513)
              ·
                refine ⟨1255856531237121553729885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674475374982828738306513 1255856531237121553729885)
                ·
                  refine ⟨470946199213920582648707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255856531237121553729885 470946199213920582648707)
                  ·
                    rfl

theorem cell21_2063620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_2063620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063620 prefixEnd_2063620 := by exact prefixLift 2063620
  have htrace : WordTrace (prefixWord ++ tailWord_2063620) baseStart_2063620 baseEnd_2063620 := by
    simpa [prefixWord, tailWord_2063620, baseEnd_2063620] using wordTrace_append hprefix tailTrace_2063620
  have hstable : (prefixWord ++ tailWord_2063620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063620).length < 2 ^ (prefixWord ++ tailWord_2063620).sum := by decide
  have hdescent : baseEnd_2063620 < baseStart_2063620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063645 : List Nat := [1, 4, 2, 3, 1, 1, 1, 1, 7]
def baseStart_2063645 : Nat := 118140960795 + 2063645 * 2 ^ 59
def prefixEnd_2063645 : Nat := 4983230072969 + 3 ^ 40 * 2063645 * 2
def baseEnd_2063645 : Nat := 470951904554526094731989

theorem tailTrace_2063645 : CollatzResearch.WordTrace tailWord_2063645 prefixEnd_2063645 470951904554526094731989 := by
  unfold tailWord_2063645
  simp only [CollatzResearch.WordTrace]
  refine ⟨75267316608774082351728389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50178211072516054901152259 75267316608774082351728389)
  ·
    refine ⟨14112621864145140440949073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75267316608774082351728389 14112621864145140440949073)
    ·
      refine ⟨10584466398108855330711805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14112621864145140440949073 10584466398108855330711805)
      ·
        refine ⟨3969174899290820749016927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10584466398108855330711805 3969174899290820749016927)
        ·
          refine ⟨5953762348936231123525391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969174899290820749016927 5953762348936231123525391)
          ·
            refine ⟨8930643523404346685288087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5953762348936231123525391 8930643523404346685288087)
            ·
              refine ⟨13395965285106520027932131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8930643523404346685288087 13395965285106520027932131)
              ·
                refine ⟨20093947927659780041898197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13395965285106520027932131 20093947927659780041898197)
                ·
                  refine ⟨470951904554526094731989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20093947927659780041898197 470951904554526094731989)
                  ·
                    rfl

theorem cell21_2063645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_2063645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063645 prefixEnd_2063645 := by exact prefixLift 2063645
  have htrace : WordTrace (prefixWord ++ tailWord_2063645) baseStart_2063645 baseEnd_2063645 := by
    simpa [prefixWord, tailWord_2063645, baseEnd_2063645] using wordTrace_append hprefix tailTrace_2063645
  have hstable : (prefixWord ++ tailWord_2063645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063645).length < 2 ^ (prefixWord ++ tailWord_2063645).sum := by decide
  have hdescent : baseEnd_2063645 < baseStart_2063645 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063676 : List Nat := [2, 2, 2, 2, 1, 3, 3, 2, 4]
def baseStart_2063676 : Nat := 118140960795 + 2063676 * 2 ^ 59
def prefixEnd_2063676 : Nat := 4983230072969 + 3 ^ 40 * 2063676 * 2
def baseEnd_2063676 : Nat := 470958979176876929715259

theorem tailTrace_2063676 : CollatzResearch.WordTrace tailWord_2063676 prefixEnd_2063676 470958979176876929715259 := by
  unfold tailWord_2063676
  simp only [CollatzResearch.WordTrace]
  refine ⟨37634223635830887323053441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50178964847774516430737921 37634223635830887323053441)
  ·
    refine ⟨28225667726873165492290081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37634223635830887323053441 28225667726873165492290081)
    ·
      refine ⟨21169250795154874119217561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28225667726873165492290081 21169250795154874119217561)
      ·
        refine ⟨15876938096366155589413171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21169250795154874119217561 15876938096366155589413171)
        ·
          refine ⟨23815407144549233384119757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15876938096366155589413171 23815407144549233384119757)
          ·
            refine ⟨8930777679205962519044909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23815407144549233384119757 8930777679205962519044909)
            ·
              refine ⟨3349041629702235944641841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8930777679205962519044909 3349041629702235944641841)
              ·
                refine ⟨2511781222276676958481381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349041629702235944641841 2511781222276676958481381)
                ·
                  refine ⟨470958979176876929715259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511781222276676958481381 470958979176876929715259)
                  ·
                    rfl

theorem cell21_2063676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_2063676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063676 prefixEnd_2063676 := by exact prefixLift 2063676
  have htrace : WordTrace (prefixWord ++ tailWord_2063676) baseStart_2063676 baseEnd_2063676 := by
    simpa [prefixWord, tailWord_2063676, baseEnd_2063676] using wordTrace_append hprefix tailTrace_2063676
  have hstable : (prefixWord ++ tailWord_2063676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063676).length < 2 ^ (prefixWord ++ tailWord_2063676).sum := by decide
  have hdescent : baseEnd_2063676 < baseStart_2063676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063704 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 5]
def baseStart_2063704 : Nat := 118140960795 + 2063704 * 2 ^ 59
def prefixEnd_2063704 : Nat := 4983230072969 + 3 ^ 40 * 2063704 * 2
def baseEnd_2063704 : Nat := 470965369158355103248535

theorem tailTrace_2063704 : CollatzResearch.WordTrace tailWord_2063704 prefixEnd_2063704 470965369158355103248535 := by
  unfold tailWord_2063704
  simp only [CollatzResearch.WordTrace]
  refine ⟨37634734257780167714063083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50179645677040223618750777 37634734257780167714063083)
  ·
    refine ⟨56452101386670251571094625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37634734257780167714063083 56452101386670251571094625)
    ·
      refine ⟨42339076040002688678320969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56452101386670251571094625 42339076040002688678320969)
      ·
        refine ⟨31754307030002016508740727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42339076040002688678320969 31754307030002016508740727)
        ·
          refine ⟨47631460545003024763111091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31754307030002016508740727 47631460545003024763111091)
          ·
            refine ⟨71447190817504537144666637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47631460545003024763111091 71447190817504537144666637)
            ·
              refine ⟨26792696556564201429249989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71447190817504537144666637 26792696556564201429249989)
              ·
                refine ⟨5023630604355787767984373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26792696556564201429249989 5023630604355787767984373)
                ·
                  refine ⟨470965369158355103248535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5023630604355787767984373 470965369158355103248535)
                  ·
                    rfl

theorem cell21_2063704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 5].length) (baseStart_2063704 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063704 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063704 prefixEnd_2063704 := by exact prefixLift 2063704
  have htrace : WordTrace (prefixWord ++ tailWord_2063704) baseStart_2063704 baseEnd_2063704 := by
    simpa [prefixWord, tailWord_2063704, baseEnd_2063704] using wordTrace_append hprefix tailTrace_2063704
  have hstable : (prefixWord ++ tailWord_2063704).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063704).length < 2 ^ (prefixWord ++ tailWord_2063704).sum := by decide
  have hdescent : baseEnd_2063704 < baseStart_2063704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063721 : List Nat := [1, 2, 1, 1, 1, 3, 2, 7, 3]
def baseStart_2063721 : Nat := 118140960795 + 2063721 * 2 ^ 59
def prefixEnd_2063721 : Nat := 4983230072969 + 3 ^ 40 * 2063721 * 2
def baseEnd_2063721 : Nat := 470969248789966851465167

theorem tailTrace_2063721 : CollatzResearch.WordTrace tailWord_2063721 prefixEnd_2063721 470969248789966851465167 := by
  unfold tailWord_2063721
  simp only [CollatzResearch.WordTrace]
  refine ⟨75270088556498747331495017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50180059037665831554330011 75270088556498747331495017)
  ·
    refine ⟨56452566417374060498621263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75270088556498747331495017 56452566417374060498621263)
    ·
      refine ⟨84678849626061090747931895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56452566417374060498621263 84678849626061090747931895)
      ·
        refine ⟨127018274439091636121897843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84678849626061090747931895 127018274439091636121897843)
        ·
          refine ⟨190527411658637454182846765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127018274439091636121897843 190527411658637454182846765)
          ·
            refine ⟨71447779371989045318567537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 190527411658637454182846765 71447779371989045318567537)
            ·
              refine ⟨53585834528991783988925653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71447779371989045318567537 53585834528991783988925653)
              ·
                refine ⟨1255917996773244937240445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53585834528991783988925653 1255917996773244937240445)
                ·
                  refine ⟨470969248789966851465167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255917996773244937240445 470969248789966851465167)
                  ·
                    rfl

theorem cell21_2063721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 3].length) (baseStart_2063721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063721 prefixEnd_2063721 := by exact prefixLift 2063721
  have htrace : WordTrace (prefixWord ++ tailWord_2063721) baseStart_2063721 baseEnd_2063721 := by
    simpa [prefixWord, tailWord_2063721, baseEnd_2063721] using wordTrace_append hprefix tailTrace_2063721
  have hstable : (prefixWord ++ tailWord_2063721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063721).length < 2 ^ (prefixWord ++ tailWord_2063721).sum := by decide
  have hdescent : baseEnd_2063721 < baseStart_2063721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063735 : List Nat := [1, 1, 3, 1, 1, 2, 4, 4, 4]
def baseStart_2063735 : Nat := 118140960795 + 2063735 * 2 ^ 59
def prefixEnd_2063735 : Nat := 4983230072969 + 3 ^ 40 * 2063735 * 2
def baseEnd_2063735 : Nat := 470972443780705938231805

theorem tailTrace_2063735 : CollatzResearch.WordTrace tailWord_2063735 prefixEnd_2063735 470972443780705938231805 := by
  unfold tailWord_2063735
  simp only [CollatzResearch.WordTrace]
  refine ⟨75270599178448027722504659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50180399452298685148336439 75270599178448027722504659)
  ·
    refine ⟨112905898767672041583756989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75270599178448027722504659 112905898767672041583756989)
    ·
      refine ⟨42339712037877015593908871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 112905898767672041583756989 42339712037877015593908871)
      ·
        refine ⟨63509568056815523390863307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42339712037877015593908871 63509568056815523390863307)
        ·
          refine ⟨95264352085223285086294961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63509568056815523390863307 95264352085223285086294961)
          ·
            refine ⟨71448264063917463814721221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95264352085223285086294961 71448264063917463814721221)
            ·
              refine ⟨13396549511984524465260229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71448264063917463814721221 13396549511984524465260229)
              ·
                refine ⟨2511853033497098337236293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13396549511984524465260229 2511853033497098337236293)
                ·
                  refine ⟨470972443780705938231805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511853033497098337236293 470972443780705938231805)
                  ·
                    rfl

theorem cell21_2063735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 4, 4].length) (baseStart_2063735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063735 prefixEnd_2063735 := by exact prefixLift 2063735
  have htrace : WordTrace (prefixWord ++ tailWord_2063735) baseStart_2063735 baseEnd_2063735 := by
    simpa [prefixWord, tailWord_2063735, baseEnd_2063735] using wordTrace_append hprefix tailTrace_2063735
  have hstable : (prefixWord ++ tailWord_2063735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063735).length < 2 ^ (prefixWord ++ tailWord_2063735).sum := by decide
  have hdescent : baseEnd_2063735 < baseStart_2063735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063749 : List Nat := [1, 3, 1, 1, 3, 1, 3, 8]
def baseStart_2063749 : Nat := 118140960795 + 2063749 * 2 ^ 59
def prefixEnd_2063749 : Nat := 4983230072969 + 3 ^ 40 * 2063749 * 2
def baseEnd_2063749 : Nat := 156991879590481674999481

theorem tailTrace_2063749 : CollatzResearch.WordTrace tailWord_2063749 prefixEnd_2063749 156991879590481674999481 := by
  unfold tailWord_2063749
  simp only [CollatzResearch.WordTrace]
  refine ⟨75271109800397308113514301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50180739866931538742342867 75271109800397308113514301)
  ·
    refine ⟨28226666175148990542567863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75271109800397308113514301 28226666175148990542567863)
    ·
      refine ⟨42339999262723485813851795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28226666175148990542567863 42339999262723485813851795)
      ·
        refine ⟨63509998894085228720777693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42339999262723485813851795 63509998894085228720777693)
        ·
          refine ⟨23816249585281960770291635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63509998894085228720777693 23816249585281960770291635)
          ·
            refine ⟨35724374377922941155437453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23816249585281960770291635 35724374377922941155437453)
            ·
              refine ⟨13396640391721102933289045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35724374377922941155437453 13396640391721102933289045)
              ·
                refine ⟨156991879590481674999481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13396640391721102933289045 156991879590481674999481)
                ·
                  rfl

theorem cell21_2063749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_2063749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063749 prefixEnd_2063749 := by exact prefixLift 2063749
  have htrace : WordTrace (prefixWord ++ tailWord_2063749) baseStart_2063749 baseEnd_2063749 := by
    simpa [prefixWord, tailWord_2063749, baseEnd_2063749] using wordTrace_append hprefix tailTrace_2063749
  have hstable : (prefixWord ++ tailWord_2063749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063749).length < 2 ^ (prefixWord ++ tailWord_2063749).sum := by decide
  have hdescent : baseEnd_2063749 < baseStart_2063749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063752 : List Nat := [2, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_2063752 : Nat := 118140960795 + 2063752 * 2 ^ 59
def prefixEnd_2063752 : Nat := 4983230072969 + 3 ^ 40 * 2063752 * 2
def baseEnd_2063752 : Nat := 470976323412317686448437

theorem tailTrace_2063752 : CollatzResearch.WordTrace tailWord_2063752 prefixEnd_2063752 470976323412317686448437 := by
  unfold tailWord_2063752
  simp only [CollatzResearch.WordTrace]
  refine ⟨37635609609693219812936755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50180812812924293083915673 37635609609693219812936755)
  ·
    refine ⟨56453414414539829719405133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37635609609693219812936755 56453414414539829719405133)
    ·
      refine ⟨21170030405452436144776925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56453414414539829719405133 21170030405452436144776925)
      ·
        refine ⟨7938761402044663554291347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21170030405452436144776925 7938761402044663554291347)
        ·
          refine ⟨11908142103066995331437021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7938761402044663554291347 11908142103066995331437021)
          ·
            refine ⟨4465553288650123249288883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11908142103066995331437021 4465553288650123249288883)
            ·
              refine ⟨6698329932975184873933325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4465553288650123249288883 6698329932975184873933325)
              ·
                refine ⟨2511873724865694327724997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6698329932975184873933325 2511873724865694327724997)
                ·
                  refine ⟨470976323412317686448437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511873724865694327724997 470976323412317686448437)
                  ·
                    rfl

theorem cell21_2063752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_2063752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063752 prefixEnd_2063752 := by exact prefixLift 2063752
  have htrace : WordTrace (prefixWord ++ tailWord_2063752) baseStart_2063752 baseEnd_2063752 := by
    simpa [prefixWord, tailWord_2063752, baseEnd_2063752] using wordTrace_append hprefix tailTrace_2063752
  have hstable : (prefixWord ++ tailWord_2063752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063752).length < 2 ^ (prefixWord ++ tailWord_2063752).sum := by decide
  have hdescent : baseEnd_2063752 < baseStart_2063752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063811 : List Nat := [1, 1, 1, 3, 1, 1, 6, 3, 4]
def baseStart_2063811 : Nat := 118140960795 + 2063811 * 2 ^ 59
def prefixEnd_2063811 : Nat := 4983230072969 + 3 ^ 40 * 2063811 * 2
def baseEnd_2063811 : Nat := 470989788016146694964983

theorem tailTrace_2063811 : CollatzResearch.WordTrace tailWord_2063811 prefixEnd_2063811 470989788016146694964983 := by
  unfold tailWord_2063811
  simp only [CollatzResearch.WordTrace]
  refine ⟨75273371126172692702271287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50182247417448461801514191 75273371126172692702271287)
  ·
    refine ⟨112910056689259039053406931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75273371126172692702271287 112910056689259039053406931)
    ·
      refine ⟨169365085033888558580110397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112910056689259039053406931 169365085033888558580110397)
      ·
        refine ⟨63511906887708209467541399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169365085033888558580110397 63511906887708209467541399)
        ·
          refine ⟨95267860331562314201312099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63511906887708209467541399 95267860331562314201312099)
          ·
            refine ⟨142901790497343471301968149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95267860331562314201312099 142901790497343471301968149)
            ·
              refine ⟨6698521429562975217279757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142901790497343471301968149 6698521429562975217279757)
              ·
                refine ⟨2511945536086115706479909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6698521429562975217279757 2511945536086115706479909)
                ·
                  refine ⟨470989788016146694964983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511945536086115706479909 470989788016146694964983)
                  ·
                    rfl

theorem cell21_2063811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 4].length) (baseStart_2063811 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063811 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063811 prefixEnd_2063811 := by exact prefixLift 2063811
  have htrace : WordTrace (prefixWord ++ tailWord_2063811) baseStart_2063811 baseEnd_2063811 := by
    simpa [prefixWord, tailWord_2063811, baseEnd_2063811] using wordTrace_append hprefix tailTrace_2063811
  have hstable : (prefixWord ++ tailWord_2063811).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063811).length < 2 ^ (prefixWord ++ tailWord_2063811).sum := by decide
  have hdescent : baseEnd_2063811 < baseStart_2063811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063845 : List Nat := [1, 3, 1, 5, 1, 3, 1, 2, 4]
def baseStart_2063845 : Nat := 118140960795 + 2063845 * 2 ^ 59
def prefixEnd_2063845 : Nat := 4983230072969 + 3 ^ 40 * 2063845 * 2
def baseEnd_2063845 : Nat := 470997547279370191398247

theorem tailTrace_2063845 : CollatzResearch.WordTrace tailWord_2063845 prefixEnd_2063845 470997547279370191398247 := by
  unfold tailWord_2063845
  simp only [CollatzResearch.WordTrace]
  refine ⟨75274611208049516509008989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50183074138699677672672659 75274611208049516509008989)
  ·
    refine ⟨28227979203018568690878371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75274611208049516509008989 28227979203018568690878371)
    ·
      refine ⟨42341968804527853036317557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28227979203018568690878371 42341968804527853036317557)
      ·
        refine ⟨3969559575424486222154771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42341968804527853036317557 3969559575424486222154771)
        ·
          refine ⟨5954339363136729333232157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3969559575424486222154771 5954339363136729333232157)
          ·
            refine ⟨2232877261176273499962059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5954339363136729333232157 2232877261176273499962059)
            ·
              refine ⟨3349315891764410249943089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2232877261176273499962059 3349315891764410249943089)
              ·
                refine ⟨2511986918823307687457317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349315891764410249943089 2511986918823307687457317)
                ·
                  refine ⟨470997547279370191398247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2511986918823307687457317 470997547279370191398247)
                  ·
                    rfl

theorem cell21_2063845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_2063845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063845 prefixEnd_2063845 := by exact prefixLift 2063845
  have htrace : WordTrace (prefixWord ++ tailWord_2063845) baseStart_2063845 baseEnd_2063845 := by
    simpa [prefixWord, tailWord_2063845, baseEnd_2063845] using wordTrace_append hprefix tailTrace_2063845
  have hstable : (prefixWord ++ tailWord_2063845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063845).length < 2 ^ (prefixWord ++ tailWord_2063845).sum := by decide
  have hdescent : baseEnd_2063845 < baseStart_2063845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063856 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 5]
def baseStart_2063856 : Nat := 118140960795 + 2063856 * 2 ^ 59
def prefixEnd_2063856 : Nat := 4983230072969 + 3 ^ 40 * 2063856 * 2
def baseEnd_2063856 : Nat := 471000057629236616714891

theorem tailTrace_2063856 : CollatzResearch.WordTrace tailWord_2063856 prefixEnd_2063856 471000057629236616714891 := by
  unfold tailWord_2063856
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637506205504832693829711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50183341607339776925106281 37637506205504832693829711)
  ·
    refine ⟨56456259308257249040744567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37637506205504832693829711 56456259308257249040744567)
    ·
      refine ⟨84684388962385873561116851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56456259308257249040744567 84684388962385873561116851)
      ·
        refine ⟨127026583443578810341675277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84684388962385873561116851 127026583443578810341675277)
        ·
          refine ⟨47634968791342053878128229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127026583443578810341675277 47634968791342053878128229)
          ·
            refine ⟨8931556648376635102149043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47634968791342053878128229 8931556648376635102149043)
            ·
              refine ⟨13397334972564952653223565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931556648376635102149043 13397334972564952653223565)
              ·
                refine ⟨5024000614711857244958837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13397334972564952653223565 5024000614711857244958837)
                ·
                  refine ⟨471000057629236616714891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5024000614711857244958837 471000057629236616714891)
                  ·
                    rfl

theorem cell21_2063856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 5].length) (baseStart_2063856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063856 prefixEnd_2063856 := by exact prefixLift 2063856
  have htrace : WordTrace (prefixWord ++ tailWord_2063856) baseStart_2063856 baseEnd_2063856 := by
    simpa [prefixWord, tailWord_2063856, baseEnd_2063856] using wordTrace_append hprefix tailTrace_2063856
  have hstable : (prefixWord ++ tailWord_2063856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063856).length < 2 ^ (prefixWord ++ tailWord_2063856).sum := by decide
  have hdescent : baseEnd_2063856 < baseStart_2063856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063876 : List Nat := [2, 3, 2, 3, 2, 2, 2, 5]
def baseStart_2063876 : Nat := 118140960795 + 2063876 * 2 ^ 59
def prefixEnd_2063876 : Nat := 4983230072969 + 3 ^ 40 * 2063876 * 2
def baseEnd_2063876 : Nat := 157001540633907008793839

theorem tailTrace_2063876 : CollatzResearch.WordTrace tailWord_2063876 prefixEnd_2063876 157001540633907008793839 := by
  unfold tailWord_2063876
  simp only [CollatzResearch.WordTrace]
  refine ⟨37637870935468604401693741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50183827913958139202258321 37637870935468604401693741)
  ·
    refine ⟨14114201600800726650635153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37637870935468604401693741 14114201600800726650635153)
    ·
      refine ⟨10585651200600544987976365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14114201600800726650635153 10585651200600544987976365)
      ·
        refine ⟨3969619200225204370491137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10585651200600544987976365 3969619200225204370491137)
        ·
          refine ⟨2977214400168903277868353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3969619200225204370491137 2977214400168903277868353)
          ·
            refine ⟨2232910800126677458401265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977214400168903277868353 2232910800126677458401265)
            ·
              refine ⟨1674683100095008093800949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232910800126677458401265 1674683100095008093800949)
              ·
                refine ⟨157001540633907008793839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1674683100095008093800949 157001540633907008793839)
                ·
                  rfl

theorem cell21_2063876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_2063876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063876 prefixEnd_2063876 := by exact prefixLift 2063876
  have htrace : WordTrace (prefixWord ++ tailWord_2063876) baseStart_2063876 baseEnd_2063876 := by
    simpa [prefixWord, tailWord_2063876, baseEnd_2063876] using wordTrace_append hprefix tailTrace_2063876
  have hstable : (prefixWord ++ tailWord_2063876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063876).length < 2 ^ (prefixWord ++ tailWord_2063876).sum := by decide
  have hdescent : baseEnd_2063876 < baseStart_2063876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063907 : List Nat := [1, 1, 1, 4, 5, 1, 3, 2, 3]
def baseStart_2063907 : Nat := 118140960795 + 2063907 * 2 ^ 59
def prefixEnd_2063907 : Nat := 4983230072969 + 3 ^ 40 * 2063907 * 2
def baseEnd_2063907 : Nat := 471011696524071861364787

theorem tailTrace_2063907 : CollatzResearch.WordTrace tailWord_2063907 prefixEnd_2063907 471011696524071861364787 := by
  unfold tailWord_2063907
  simp only [CollatzResearch.WordTrace]
  refine ⟨75276872533824901097765975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50184581689216600731843983 75276872533824901097765975)
  ·
    refine ⟨112915308800737351646648963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75276872533824901097765975 112915308800737351646648963)
    ·
      refine ⟨169372963201106027469973445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112915308800737351646648963 169372963201106027469973445)
      ·
        refine ⟨31757430600207380150620021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169372963201106027469973445 31757430600207380150620021)
        ·
          refine ⟨2977259118769441889120627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31757430600207380150620021 2977259118769441889120627)
          ·
            refine ⟨4465888678154162833680941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977259118769441889120627 4465888678154162833680941)
            ·
              refine ⟨1674708254307811062630353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4465888678154162833680941 1674708254307811062630353)
              ·
                refine ⟨1256031190730858296972765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674708254307811062630353 1256031190730858296972765)
                ·
                  refine ⟨471011696524071861364787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256031190730858296972765 471011696524071861364787)
                  ·
                    rfl

theorem cell21_2063907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 3].length) (baseStart_2063907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063907 prefixEnd_2063907 := by exact prefixLift 2063907
  have htrace : WordTrace (prefixWord ++ tailWord_2063907) baseStart_2063907 baseEnd_2063907 := by
    simpa [prefixWord, tailWord_2063907, baseEnd_2063907] using wordTrace_append hprefix tailTrace_2063907
  have hstable : (prefixWord ++ tailWord_2063907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063907).length < 2 ^ (prefixWord ++ tailWord_2063907).sum := by decide
  have hdescent : baseEnd_2063907 < baseStart_2063907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063918 : List Nat := [4, 1, 3, 1, 2, 1, 1, 8]
def baseStart_2063918 : Nat := 118140960795 + 2063918 * 2 ^ 59
def prefixEnd_2063918 : Nat := 4983230072969 + 3 ^ 40 * 2063918 * 2
def baseEnd_2063918 : Nat := 157004735624646095560477

theorem tailTrace_2063918 : CollatzResearch.WordTrace tailWord_2063918 prefixEnd_2063918 157004735624646095560477 := by
  unfold tailWord_2063918
  simp only [CollatzResearch.WordTrace]
  refine ⟨9409659217098131247052051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50184849157856699984277605 9409659217098131247052051)
  ·
    refine ⟨14114488825647196870578077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9409659217098131247052051 14114488825647196870578077)
    ·
      refine ⟨5292933309617698826466779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14114488825647196870578077 5292933309617698826466779)
      ·
        refine ⟨7939399964426548239700169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5292933309617698826466779 7939399964426548239700169)
        ·
          refine ⟨5954549973319911179775127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7939399964426548239700169 5954549973319911179775127)
          ·
            refine ⟨8931824959979866769662691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5954549973319911179775127 8931824959979866769662691)
            ·
              refine ⟨13397737439969800154494037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8931824959979866769662691 13397737439969800154494037)
              ·
                refine ⟨157004735624646095560477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13397737439969800154494037 157004735624646095560477)
                ·
                  rfl

theorem cell21_2063918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 8].length) (baseStart_2063918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063918 prefixEnd_2063918 := by exact prefixLift 2063918
  have htrace : WordTrace (prefixWord ++ tailWord_2063918) baseStart_2063918 baseEnd_2063918 := by
    simpa [prefixWord, tailWord_2063918, baseEnd_2063918] using wordTrace_append hprefix tailTrace_2063918
  have hstable : (prefixWord ++ tailWord_2063918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063918).length < 2 ^ (prefixWord ++ tailWord_2063918).sum := by decide
  have hdescent : baseEnd_2063918 < baseStart_2063918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063958 : List Nat := [5, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2063958 : Nat := 118140960795 + 2063958 * 2 ^ 59
def prefixEnd_2063958 : Nat := 4983230072969 + 3 ^ 40 * 2063958 * 2
def baseEnd_2063958 : Nat := 471023335418907106014683

theorem tailTrace_2063958 : CollatzResearch.WordTrace tailWord_2063958 prefixEnd_2063958 471023335418907106014683 := by
  unfold tailWord_2063958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704920791040008550492033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50185821771093424538581685 4704920791040008550492033)
  ·
    refine ⟨3528690593280006412869025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4704920791040008550492033 3528690593280006412869025)
    ·
      refine ⟨2646517944960004809651769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3528690593280006412869025 2646517944960004809651769)
      ·
        refine ⟨1984888458720003607238827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2646517944960004809651769 1984888458720003607238827)
        ·
          refine ⟨2977332688080005410858241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984888458720003607238827 2977332688080005410858241)
          ·
            refine ⟨2232999516060004058143681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977332688080005410858241 2232999516060004058143681)
            ·
              refine ⟨1674749637045003043607761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232999516060004058143681 1674749637045003043607761)
              ·
                refine ⟨1256062227783752282705821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674749637045003043607761 1256062227783752282705821)
                ·
                  refine ⟨471023335418907106014683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256062227783752282705821 471023335418907106014683)
                  ·
                    rfl

theorem cell21_2063958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2063958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063958 prefixEnd_2063958 := by exact prefixLift 2063958
  have htrace : WordTrace (prefixWord ++ tailWord_2063958) baseStart_2063958 baseEnd_2063958 := by
    simpa [prefixWord, tailWord_2063958, baseEnd_2063958] using wordTrace_append hprefix tailTrace_2063958
  have hstable : (prefixWord ++ tailWord_2063958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063958).length < 2 ^ (prefixWord ++ tailWord_2063958).sum := by decide
  have hdescent : baseEnd_2063958 < baseStart_2063958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2063977 : List Nat := [1, 2, 1, 1, 1, 4, 5, 6]
def baseStart_2063977 : Nat := 118140960795 + 2063977 * 2 ^ 59
def prefixEnd_2063977 : Nat := 4983230072969 + 3 ^ 40 * 2063977 * 2
def baseEnd_2063977 : Nat := 157009223825922431732659

theorem tailTrace_2063977 : CollatzResearch.WordTrace tailWord_2063977 prefixEnd_2063977 157009223825922431732659 := by
  unfold tailWord_2063977
  simp only [CollatzResearch.WordTrace]
  refine ⟨75279425643571303052814185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50186283762380868701876123 75279425643571303052814185)
  ·
    refine ⟨56459569232678477289610639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75279425643571303052814185 56459569232678477289610639)
    ·
      refine ⟨84689353849017715934415959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56459569232678477289610639 84689353849017715934415959)
      ·
        refine ⟨127034030773526573901623939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84689353849017715934415959 127034030773526573901623939)
        ·
          refine ⟨190551046160289860852435909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127034030773526573901623939 190551046160289860852435909)
          ·
            refine ⟨35728321155054348909831733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 190551046160289860852435909 35728321155054348909831733)
            ·
              refine ⟨3349530108286345210296725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35728321155054348909831733 3349530108286345210296725)
              ·
                refine ⟨157009223825922431732659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3349530108286345210296725 157009223825922431732659)
                ·
                  rfl

theorem cell21_2063977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 6].length) (baseStart_2063977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2063977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2063977 prefixEnd_2063977 := by exact prefixLift 2063977
  have htrace : WordTrace (prefixWord ++ tailWord_2063977) baseStart_2063977 baseEnd_2063977 := by
    simpa [prefixWord, tailWord_2063977, baseEnd_2063977] using wordTrace_append hprefix tailTrace_2063977
  have hstable : (prefixWord ++ tailWord_2063977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2063977).length < 2 ^ (prefixWord ++ tailWord_2063977).sum := by decide
  have hdescent : baseEnd_2063977 < baseStart_2063977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2063977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064132 : List Nat := [2, 3, 2, 2, 1, 3, 2, 2, 4]
def baseStart_2064132 : Nat := 118140960795 + 2064132 * 2 ^ 59
def prefixEnd_2064132 : Nat := 4983230072969 + 3 ^ 40 * 2064132 * 2
def baseEnd_2064132 : Nat := 471063044589521470114327

theorem tailTrace_2064132 : CollatzResearch.WordTrace tailWord_2064132 prefixEnd_2064132 471063044589521470114327 := by
  unfold tailWord_2064132
  simp only [CollatzResearch.WordTrace]
  refine ⟨37642539479004882262353325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50190052638673176349804433 37642539479004882262353325)
  ·
    refine ⟨14115952304626830848382497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37642539479004882262353325 14115952304626830848382497)
    ·
      refine ⟨10586964228470123136286873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14115952304626830848382497 10586964228470123136286873)
      ·
        refine ⟨7940223171352592352215155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10586964228470123136286873 7940223171352592352215155)
        ·
          refine ⟨11910334757028888528322733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940223171352592352215155 11910334757028888528322733)
          ·
            refine ⟨4466375533885833198121025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11910334757028888528322733 4466375533885833198121025)
            ·
              refine ⟨3349781650414374898590769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4466375533885833198121025 3349781650414374898590769)
              ·
                refine ⟨2512336237810781173943077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3349781650414374898590769 2512336237810781173943077)
                ·
                  refine ⟨471063044589521470114327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2512336237810781173943077 471063044589521470114327)
                  ·
                    rfl

theorem cell21_2064132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_2064132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064132 prefixEnd_2064132 := by exact prefixLift 2064132
  have htrace : WordTrace (prefixWord ++ tailWord_2064132) baseStart_2064132 baseEnd_2064132 := by
    simpa [prefixWord, tailWord_2064132, baseEnd_2064132] using wordTrace_append hprefix tailTrace_2064132
  have hstable : (prefixWord ++ tailWord_2064132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064132).length < 2 ^ (prefixWord ++ tailWord_2064132).sum := by decide
  have hdescent : baseEnd_2064132 < baseStart_2064132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064160 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_2064160 : Nat := 118140960795 + 2064160 * 2 ^ 59
def prefixEnd_2064160 : Nat := 4983230072969 + 3 ^ 40 * 2064160 * 2
def baseEnd_2064160 : Nat := 471069434570999643647603

theorem tailTrace_2064160 : CollatzResearch.WordTrace tailWord_2064160 prefixEnd_2064160 471069434570999643647603 := by
  unfold tailWord_2064160
  simp only [CollatzResearch.WordTrace]
  refine ⟨37643050100954162653362967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50190733467938883537817289 37643050100954162653362967)
  ·
    refine ⟨56464575151431243980044451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37643050100954162653362967 56464575151431243980044451)
    ·
      refine ⟨84696862727146865970066677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56464575151431243980044451 84696862727146865970066677)
      ·
        refine ⟨7940330880670018684693751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84696862727146865970066677 7940330880670018684693751)
        ·
          refine ⟨11910496321005028027040627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7940330880670018684693751 11910496321005028027040627)
          ·
            refine ⟨17865744481507542040560941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11910496321005028027040627 17865744481507542040560941)
            ·
              refine ⟨6699654180565328265210353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17865744481507542040560941 6699654180565328265210353)
              ·
                refine ⟨5024740635423996198907765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6699654180565328265210353 5024740635423996198907765)
                ·
                  refine ⟨471069434570999643647603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5024740635423996198907765 471069434570999643647603)
                  ·
                    rfl

theorem cell21_2064160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_2064160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064160 prefixEnd_2064160 := by exact prefixLift 2064160
  have htrace : WordTrace (prefixWord ++ tailWord_2064160) baseStart_2064160 baseEnd_2064160 := by
    simpa [prefixWord, tailWord_2064160, baseEnd_2064160] using wordTrace_append hprefix tailTrace_2064160
  have hstable : (prefixWord ++ tailWord_2064160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064160).length < 2 ^ (prefixWord ++ tailWord_2064160).sum := by decide
  have hdescent : baseEnd_2064160 < baseStart_2064160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064177 : List Nat := [1, 2, 2, 3, 2, 2, 1, 5, 3]
def baseStart_2064177 : Nat := 118140960795 + 2064177 * 2 ^ 59
def prefixEnd_2064177 : Nat := 4983230072969 + 3 ^ 40 * 2064177 * 2
def baseEnd_2064177 : Nat := 471073314202611391864235

theorem tailTrace_2064177 : CollatzResearch.WordTrace tailWord_2064177 prefixEnd_2064177 471073314202611391864235 := by
  unfold tailWord_2064177
  simp only [CollatzResearch.WordTrace]
  refine ⟨75286720242846737210094785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50191146828564491473396523 75286720242846737210094785)
  ·
    refine ⟨56465040182135052907571089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75286720242846737210094785 56465040182135052907571089)
    ·
      refine ⟨42348780136601289680678317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56465040182135052907571089 42348780136601289680678317)
      ·
        refine ⟨15880792551225483630254369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42348780136601289680678317 15880792551225483630254369)
        ·
          refine ⟨11910594413419112722690777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15880792551225483630254369 11910594413419112722690777)
          ·
            refine ⟨8932945810064334542018083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11910594413419112722690777 8932945810064334542018083)
            ·
              refine ⟨13399418715096501813027125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8932945810064334542018083 13399418715096501813027125)
              ·
                refine ⟨1256195504540297044971293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13399418715096501813027125 1256195504540297044971293)
                ·
                  refine ⟨471073314202611391864235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256195504540297044971293 471073314202611391864235)
                  ·
                    rfl

theorem cell21_2064177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 3].length) (baseStart_2064177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064177 prefixEnd_2064177 := by exact prefixLift 2064177
  have htrace : WordTrace (prefixWord ++ tailWord_2064177) baseStart_2064177 baseEnd_2064177 := by
    simpa [prefixWord, tailWord_2064177, baseEnd_2064177] using wordTrace_append hprefix tailTrace_2064177
  have hstable : (prefixWord ++ tailWord_2064177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064177).length < 2 ^ (prefixWord ++ tailWord_2064177).sum := by decide
  have hdescent : baseEnd_2064177 < baseStart_2064177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064191 : List Nat := [1, 1, 2, 2, 6, 1, 1, 1, 6]
def baseStart_2064191 : Nat := 118140960795 + 2064191 * 2 ^ 59
def prefixEnd_2064191 : Nat := 4983230072969 + 3 ^ 40 * 2064191 * 2
def baseEnd_2064191 : Nat := 471076509193350478630873

theorem tailTrace_2064191 : CollatzResearch.WordTrace tailWord_2064191 prefixEnd_2064191 471076509193350478630873 := by
  unfold tailWord_2064191
  simp only [CollatzResearch.WordTrace]
  refine ⟨75287230864796017601104427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50191487243197345067402951 75287230864796017601104427)
  ·
    refine ⟨112930846297194026401656641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75287230864796017601104427 112930846297194026401656641)
    ·
      refine ⟨84698134722895519801242481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112930846297194026401656641 84698134722895519801242481)
      ·
        refine ⟨63523601042171639850931861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84698134722895519801242481 63523601042171639850931861)
        ·
          refine ⟨2977668798851795618012431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 63523601042171639850931861 2977668798851795618012431)
          ·
            refine ⟨4466503198277693427018647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977668798851795618012431 4466503198277693427018647)
            ·
              refine ⟨6699754797416540140527971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4466503198277693427018647 6699754797416540140527971)
              ·
                refine ⟨10049632196124810210791957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699754797416540140527971 10049632196124810210791957)
                ·
                  refine ⟨471076509193350478630873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10049632196124810210791957 471076509193350478630873)
                  ·
                    rfl

theorem cell21_2064191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 1, 6].length) (baseStart_2064191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064191 prefixEnd_2064191 := by exact prefixLift 2064191
  have htrace : WordTrace (prefixWord ++ tailWord_2064191) baseStart_2064191 baseEnd_2064191 := by
    simpa [prefixWord, tailWord_2064191, baseEnd_2064191] using wordTrace_append hprefix tailTrace_2064191
  have hstable : (prefixWord ++ tailWord_2064191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064191).length < 2 ^ (prefixWord ++ tailWord_2064191).sum := by decide
  have hdescent : baseEnd_2064191 < baseStart_2064191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064250 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_2064250 : Nat := 118140960795 + 2064250 * 2 ^ 59
def prefixEnd_2064250 : Nat := 4983230072969 + 3 ^ 40 * 2064250 * 2
def baseEnd_2064250 : Nat := 471089973797179487147419

theorem tailTrace_2064250 : CollatzResearch.WordTrace tailWord_2064250 prefixEnd_2064250 471089973797179487147419 := by
  unfold tailWord_2064250
  simp only [CollatzResearch.WordTrace]
  refine ⟨18822345692895567669375551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50192921847721513785001469 18822345692895567669375551)
  ·
    refine ⟨28233518539343351504063327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18822345692895567669375551 28233518539343351504063327)
    ·
      refine ⟨42350277809015027256094991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28233518539343351504063327 42350277809015027256094991)
      ·
        refine ⟨63525416713522540884142487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42350277809015027256094991 63525416713522540884142487)
        ·
          refine ⟨95288125070283811326213731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63525416713522540884142487 95288125070283811326213731)
          ·
            refine ⟨142932187605425716989320597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95288125070283811326213731 142932187605425716989320597)
            ·
              refine ⟨6699946294004330483874403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 142932187605425716989320597 6699946294004330483874403)
              ·
                refine ⟨10049919441006495725811605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6699946294004330483874403 10049919441006495725811605)
                ·
                  refine ⟨471089973797179487147419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10049919441006495725811605 471089973797179487147419)
                  ·
                    rfl

theorem cell21_2064250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_2064250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064250 prefixEnd_2064250 := by exact prefixLift 2064250
  have htrace : WordTrace (prefixWord ++ tailWord_2064250) baseStart_2064250 baseEnd_2064250 := by
    simpa [prefixWord, tailWord_2064250, baseEnd_2064250] using wordTrace_append hprefix tailTrace_2064250
  have hstable : (prefixWord ++ tailWord_2064250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064250).length < 2 ^ (prefixWord ++ tailWord_2064250).sum := by decide
  have hdescent : baseEnd_2064250 < baseStart_2064250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064346 : List Nat := [3, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_2064346 : Nat := 118140960795 + 2064346 * 2 ^ 59
def prefixEnd_2064346 : Nat := 4983230072969 + 3 ^ 40 * 2064346 * 2
def baseEnd_2064346 : Nat := 471111882305104653547223

theorem tailTrace_2064346 : CollatzResearch.WordTrace tailWord_2064346 prefixEnd_2064346 471111882305104653547223 := by
  unfold tailWord_2064346
  simp only [CollatzResearch.WordTrace]
  refine ⟨18823221044808619768249223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50195256119489652715331261 18823221044808619768249223)
  ·
    refine ⟨28234831567212929652373835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18823221044808619768249223 28234831567212929652373835)
    ·
      refine ⟨42352247350819394478560753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28234831567212929652373835 42352247350819394478560753)
      ·
        refine ⟨31764185513114545858920565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42352247350819394478560753 31764185513114545858920565)
        ·
          refine ⟨2977892391854488674273803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31764185513114545858920565 2977892391854488674273803)
          ·
            refine ⟨4466838587781733011410705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2977892391854488674273803 4466838587781733011410705)
            ·
              refine ⟨3350128940836299758558029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4466838587781733011410705 3350128940836299758558029)
              ·
                refine ⟨1256298352813612409459261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350128940836299758558029 1256298352813612409459261)
                ·
                  refine ⟨471111882305104653547223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256298352813612409459261 471111882305104653547223)
                  ·
                    rfl

theorem cell21_2064346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_2064346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064346 prefixEnd_2064346 := by exact prefixLift 2064346
  have htrace : WordTrace (prefixWord ++ tailWord_2064346) baseStart_2064346 baseEnd_2064346 := by
    simpa [prefixWord, tailWord_2064346, baseEnd_2064346] using wordTrace_append hprefix tailTrace_2064346
  have hstable : (prefixWord ++ tailWord_2064346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064346).length < 2 ^ (prefixWord ++ tailWord_2064346).sum := by decide
  have hdescent : baseEnd_2064346 < baseStart_2064346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064397 : List Nat := [1, 7, 1, 2, 1, 2, 1, 3, 3]
def baseStart_2064397 : Nat := 118140960795 + 2064397 * 2 ^ 59
def prefixEnd_2064397 : Nat := 4983230072969 + 3 ^ 40 * 2064397 * 2
def baseEnd_2064397 : Nat := 471123521199939898197119

theorem tailTrace_2064397 : CollatzResearch.WordTrace tailWord_2064397 prefixEnd_2064397 471123521199939898197119 := by
  unfold tailWord_2064397
  simp only [CollatzResearch.WordTrace]
  refine ⟨75294744302049714783103445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50196496201366476522068963 75294744302049714783103445)
  ·
    refine ⟨1764720569579290190228987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 75294744302049714783103445 1764720569579290190228987)
    ·
      refine ⟨2647080854368935285343481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1764720569579290190228987 2647080854368935285343481)
      ·
        refine ⟨1985310640776701464007611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2647080854368935285343481 1985310640776701464007611)
        ·
          refine ⟨2977965961165052196011417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1985310640776701464007611 2977965961165052196011417)
          ·
            refine ⟨2233474470873789147008563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2977965961165052196011417 2233474470873789147008563)
            ·
              refine ⟨3350211706310683720512845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2233474470873789147008563 3350211706310683720512845)
              ·
                refine ⟨1256329389866506395192317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350211706310683720512845 1256329389866506395192317)
                ·
                  refine ⟨471123521199939898197119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256329389866506395192317 471123521199939898197119)
                  ·
                    rfl

theorem cell21_2064397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_2064397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064397 prefixEnd_2064397 := by exact prefixLift 2064397
  have htrace : WordTrace (prefixWord ++ tailWord_2064397) baseStart_2064397 baseEnd_2064397 := by
    simpa [prefixWord, tailWord_2064397, baseEnd_2064397] using wordTrace_append hprefix tailTrace_2064397
  have hstable : (prefixWord ++ tailWord_2064397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064397).length < 2 ^ (prefixWord ++ tailWord_2064397).sum := by decide
  have hdescent : baseEnd_2064397 < baseStart_2064397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064433 : List Nat := [1, 2, 2, 3, 1, 4, 2, 6]
def baseStart_2064433 : Nat := 118140960795 + 2064433 * 2 ^ 59
def prefixEnd_2064433 : Nat := 4983230072969 + 3 ^ 40 * 2064433 * 2
def baseEnd_2064433 : Nat := 157043912296803945199015

theorem tailTrace_2064433 : CollatzResearch.WordTrace tailWord_2064433 prefixEnd_2064433 157043912296803945199015 := by
  unfold tailWord_2064433
  simp only [CollatzResearch.WordTrace]
  refine ⟨75296057329919292931413953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50197371553279528620942635 75296057329919292931413953)
  ·
    refine ⟨56472042997439469698560465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75296057329919292931413953 56472042997439469698560465)
    ·
      refine ⟨42354032248079602273920349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56472042997439469698560465 42354032248079602273920349)
      ·
        refine ⟨15882762093029850852720131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42354032248079602273920349 15882762093029850852720131)
        ·
          refine ⟨23824143139544776279080197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15882762093029850852720131 23824143139544776279080197)
          ·
            refine ⟨4467026838664645552327537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23824143139544776279080197 4467026838664645552327537)
            ·
              refine ⟨3350270128998484164245653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4467026838664645552327537 3350270128998484164245653)
              ·
                refine ⟨157043912296803945199015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3350270128998484164245653 157043912296803945199015)
                ·
                  rfl

theorem cell21_2064433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 6].length) (baseStart_2064433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064433 prefixEnd_2064433 := by exact prefixLift 2064433
  have htrace : WordTrace (prefixWord ++ tailWord_2064433) baseStart_2064433 baseEnd_2064433 := by
    simpa [prefixWord, tailWord_2064433, baseEnd_2064433] using wordTrace_append hprefix tailTrace_2064433
  have hstable : (prefixWord ++ tailWord_2064433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064433).length < 2 ^ (prefixWord ++ tailWord_2064433).sum := by decide
  have hdescent : baseEnd_2064433 < baseStart_2064433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064447 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 5]
def baseStart_2064447 : Nat := 118140960795 + 2064447 * 2 ^ 59
def prefixEnd_2064447 : Nat := 4983230072969 + 3 ^ 40 * 2064447 * 2
def baseEnd_2064447 : Nat := 471134931881150922363683

theorem tailTrace_2064447 : CollatzResearch.WordTrace tailWord_2064447 prefixEnd_2064447 471134931881150922363683 := by
  unfold tailWord_2064447
  simp only [CollatzResearch.WordTrace]
  refine ⟨75296567951868573322423595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50197711967912382214949063 75296567951868573322423595)
  ·
    refine ⟨112944851927802859983635393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75296567951868573322423595 112944851927802859983635393)
    ·
      refine ⟨84708638945852144987726545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 112944851927802859983635393 84708638945852144987726545)
      ·
        refine ⟨63531479209389108740794909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84708638945852144987726545 63531479209389108740794909)
        ·
          refine ⟨23824304703520915777798091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63531479209389108740794909 23824304703520915777798091)
          ·
            refine ⟨35736457055281373666697137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23824304703520915777798091 35736457055281373666697137)
            ·
              refine ⟨26802342791461030250022853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35736457055281373666697137 26802342791461030250022853)
              ·
                refine ⟨5025439273398943171879285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26802342791461030250022853 5025439273398943171879285)
                ·
                  refine ⟨471134931881150922363683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025439273398943171879285 471134931881150922363683)
                  ·
                    rfl

theorem cell21_2064447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 5].length) (baseStart_2064447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064447 prefixEnd_2064447 := by exact prefixLift 2064447
  have htrace : WordTrace (prefixWord ++ tailWord_2064447) baseStart_2064447 baseEnd_2064447 := by
    simpa [prefixWord, tailWord_2064447, baseEnd_2064447] using wordTrace_append hprefix tailTrace_2064447
  have hstable : (prefixWord ++ tailWord_2064447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064447).length < 2 ^ (prefixWord ++ tailWord_2064447).sum := by decide
  have hdescent : baseEnd_2064447 < baseStart_2064447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064540 : List Nat := [2, 2, 3, 2, 1, 1, 4, 1, 5]
def baseStart_2064540 : Nat := 118140960795 + 2064540 * 2 ^ 59
def prefixEnd_2064540 : Nat := 4983230072969 + 3 ^ 40 * 2064540 * 2
def baseEnd_2064540 : Nat := 471156155748203427313493

theorem tailTrace_2064540 : CollatzResearch.WordTrace tailWord_2064540 prefixEnd_2064540 471156155748203427313493 := by
  unfold tailWord_2064540
  simp only [CollatzResearch.WordTrace]
  refine ⟨37649979970265825102779537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50199973293687766803706049 37649979970265825102779537)
  ·
    refine ⟨28237484977699368827084653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37649979970265825102779537 28237484977699368827084653)
    ·
      refine ⟨10589056866637263310156745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28237484977699368827084653 10589056866637263310156745)
      ·
        refine ⟨7941792649977947482617559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10589056866637263310156745 7941792649977947482617559)
        ·
          refine ⟨11912688974966921223926339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941792649977947482617559 11912688974966921223926339)
          ·
            refine ⟨17869033462450381835889509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11912688974966921223926339 17869033462450381835889509)
            ·
              refine ⟨3350443774209446594229283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17869033462450381835889509 3350443774209446594229283)
              ·
                refine ⟨5025665661314169891343925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3350443774209446594229283 5025665661314169891343925)
                ·
                  refine ⟨471156155748203427313493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025665661314169891343925 471156155748203427313493)
                  ·
                    rfl

theorem cell21_2064540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_2064540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064540 prefixEnd_2064540 := by exact prefixLift 2064540
  have htrace : WordTrace (prefixWord ++ tailWord_2064540) baseStart_2064540 baseEnd_2064540 := by
    simpa [prefixWord, tailWord_2064540, baseEnd_2064540] using wordTrace_append hprefix tailTrace_2064540
  have hstable : (prefixWord ++ tailWord_2064540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064540).length < 2 ^ (prefixWord ++ tailWord_2064540).sum := by decide
  have hdescent : baseEnd_2064540 < baseStart_2064540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064568 : List Nat := [2, 1, 2, 1, 2, 1, 5, 7]
def baseStart_2064568 : Nat := 118140960795 + 2064568 * 2 ^ 59
def prefixEnd_2064568 : Nat := 4983230072969 + 3 ^ 40 * 2064568 * 2
def baseEnd_2064568 : Nat := 157054181909893866948923

theorem tailTrace_2064568 : CollatzResearch.WordTrace tailWord_2064568 prefixEnd_2064568 157054181909893866948923 := by
  unfold tailWord_2064568
  simp only [CollatzResearch.WordTrace]
  refine ⟨37650490592215105493789179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50200654122953473991718905 37650490592215105493789179)
  ·
    refine ⟨56475735888322658240683769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37650490592215105493789179 56475735888322658240683769)
    ·
      refine ⟨42356801916241993680512827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56475735888322658240683769 42356801916241993680512827)
      ·
        refine ⟨63535202874362990520769241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42356801916241993680512827 63535202874362990520769241)
        ·
          refine ⟨47651402155772242890576931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63535202874362990520769241 47651402155772242890576931)
          ·
            refine ⟨71477103233658364335865397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47651402155772242890576931 71477103233658364335865397)
            ·
              refine ⟨6700978428155471656487381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71477103233658364335865397 6700978428155471656487381)
              ·
                refine ⟨157054181909893866948923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6700978428155471656487381 157054181909893866948923)
                ·
                  rfl

theorem cell21_2064568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_2064568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064568 prefixEnd_2064568 := by exact prefixLift 2064568
  have htrace : WordTrace (prefixWord ++ tailWord_2064568) baseStart_2064568 baseEnd_2064568 := by
    simpa [prefixWord, tailWord_2064568, baseEnd_2064568] using wordTrace_append hprefix tailTrace_2064568
  have hstable : (prefixWord ++ tailWord_2064568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064568).length < 2 ^ (prefixWord ++ tailWord_2064568).sum := by decide
  have hdescent : baseEnd_2064568 < baseStart_2064568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064605 : List Nat := [1, 4, 3, 2, 1, 3, 2, 1, 4]
def baseStart_2064605 : Nat := 118140960795 + 2064605 * 2 ^ 59
def prefixEnd_2064605 : Nat := 4983230072969 + 3 ^ 40 * 2064605 * 2
def baseEnd_2064605 : Nat := 471170989633777758730027

theorem tailTrace_2064605 : CollatzResearch.WordTrace tailWord_2064605 prefixEnd_2064605 471170989633777758730027 := by
  unfold tailWord_2064605
  simp only [CollatzResearch.WordTrace]
  refine ⟨75302330685296166306675269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50201553790197444204450179 75302330685296166306675269)
  ·
    refine ⟨14119187003493031182501613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75302330685296166306675269 14119187003493031182501613)
    ·
      refine ⟨5294695126309886693438105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14119187003493031182501613 5294695126309886693438105)
      ·
        refine ⟨3971021344732415020078579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5294695126309886693438105 3971021344732415020078579)
        ·
          refine ⟨5956532017098622530117869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971021344732415020078579 5956532017098622530117869)
          ·
            refine ⟨2233699506411983448794201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5956532017098622530117869 2233699506411983448794201)
            ·
              refine ⟨1675274629808987586595651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2233699506411983448794201 1675274629808987586595651)
              ·
                refine ⟨2512911944713481379893477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675274629808987586595651 2512911944713481379893477)
                ·
                  refine ⟨471170989633777758730027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2512911944713481379893477 471170989633777758730027)
                  ·
                    rfl

theorem cell21_2064605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 4].length) (baseStart_2064605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064605 prefixEnd_2064605 := by exact prefixLift 2064605
  have htrace : WordTrace (prefixWord ++ tailWord_2064605) baseStart_2064605 baseEnd_2064605 := by
    simpa [prefixWord, tailWord_2064605, baseEnd_2064605] using wordTrace_append hprefix tailTrace_2064605
  have hstable : (prefixWord ++ tailWord_2064605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064605).length < 2 ^ (prefixWord ++ tailWord_2064605).sum := by decide
  have hdescent : baseEnd_2064605 < baseStart_2064605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064630 : List Nat := [5, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2064630 : Nat := 118140960795 + 2064630 * 2 ^ 59
def prefixEnd_2064630 : Nat := 4983230072969 + 3 ^ 40 * 2064630 * 2
def baseEnd_2064630 : Nat := 471176694974383270813309

theorem tailTrace_2064630 : CollatzResearch.WordTrace tailWord_2064630 prefixEnd_2064630 471176694974383270813309 := by
  unfold tailWord_2064630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4706452656887849723520959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50202161673470397050890229 4706452656887849723520959)
  ·
    refine ⟨7059678985331774585281439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4706452656887849723520959 7059678985331774585281439)
    ·
      refine ⟨10589518477997661877922159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7059678985331774585281439 10589518477997661877922159)
      ·
        refine ⟨15884277716996492816883239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10589518477997661877922159 15884277716996492816883239)
        ·
          refine ⟨23826416575494739225324859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15884277716996492816883239 23826416575494739225324859)
          ·
            refine ⟨35739624863242108837987289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23826416575494739225324859 35739624863242108837987289)
            ·
              refine ⟨26804718647431581628490467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35739624863242108837987289 26804718647431581628490467)
              ·
                refine ⟨40207077971147372442735701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26804718647431581628490467 40207077971147372442735701)
                ·
                  refine ⟨471176694974383270813309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40207077971147372442735701 471176694974383270813309)
                  ·
                    rfl

theorem cell21_2064630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2064630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064630 prefixEnd_2064630 := by exact prefixLift 2064630
  have htrace : WordTrace (prefixWord ++ tailWord_2064630) baseStart_2064630 baseEnd_2064630 := by
    simpa [prefixWord, tailWord_2064630, baseEnd_2064630] using wordTrace_append hprefix tailTrace_2064630
  have hstable : (prefixWord ++ tailWord_2064630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064630).length < 2 ^ (prefixWord ++ tailWord_2064630).sum := by decide
  have hdescent : baseEnd_2064630 < baseStart_2064630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064644 : List Nat := [2, 3, 2, 2, 12]
def baseStart_2064644 : Nat := 118140960795 + 2064644 * 2 ^ 59
def prefixEnd_2064644 : Nat := 4983230072969 + 3 ^ 40 * 2064644 * 2
def baseEnd_2064644 : Nat := 5817035678581757500987

theorem tailTrace_2064644 : CollatzResearch.WordTrace tailWord_2064644 prefixEnd_2064644 5817035678581757500987 := by
  unfold tailWord_2064644
  simp only [CollatzResearch.WordTrace]
  refine ⟨37651876566077437983672493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50202502088103250644896657 37651876566077437983672493)
  ·
    refine ⟨14119453712279039243877185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37651876566077437983672493 14119453712279039243877185)
    ·
      refine ⟨10589590284209279432907889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14119453712279039243877185 10589590284209279432907889)
      ·
        refine ⟨7942192713156959574680917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10589590284209279432907889 7942192713156959574680917)
        ·
          refine ⟨5817035678581757500987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 7942192713156959574680917 5817035678581757500987)
          ·
            rfl

theorem cell21_2064644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 12].length) (baseStart_2064644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064644 prefixEnd_2064644 := by exact prefixLift 2064644
  have htrace : WordTrace (prefixWord ++ tailWord_2064644) baseStart_2064644 baseEnd_2064644 := by
    simpa [prefixWord, tailWord_2064644, baseEnd_2064644] using wordTrace_append hprefix tailTrace_2064644
  have hstable : (prefixWord ++ tailWord_2064644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064644).length < 2 ^ (prefixWord ++ tailWord_2064644).sum := by decide
  have hdescent : baseEnd_2064644 < baseStart_2064644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064675 : List Nat := [1, 1, 1, 4, 2, 2, 3, 2, 5]
def baseStart_2064675 : Nat := 118140960795 + 2064675 * 2 ^ 59
def prefixEnd_2064675 : Nat := 4983230072969 + 3 ^ 40 * 2064675 * 2
def baseEnd_2064675 : Nat := 471186964587473192563217

theorem tailTrace_2064675 : CollatzResearch.WordTrace tailWord_2064675 prefixEnd_2064675 471186964587473192563217 := by
  unfold tailWord_2064675
  simp only [CollatzResearch.WordTrace]
  refine ⟨75304883795042568261723479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50203255863361712174482319 75304883795042568261723479)
  ·
    refine ⟨112957325692563852392585219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75304883795042568261723479 112957325692563852392585219)
    ·
      refine ⟨169435988538845778588877829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 112957325692563852392585219 169435988538845778588877829)
      ·
        refine ⟨31769247851033583485414593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169435988538845778588877829 31769247851033583485414593)
        ·
          refine ⟨23826935888275187614060945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31769247851033583485414593 23826935888275187614060945)
          ·
            refine ⟨17870201916206390710545709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23826935888275187614060945 17870201916206390710545709)
            ·
              refine ⟨6701325718577396516454641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17870201916206390710545709 6701325718577396516454641)
              ·
                refine ⟨5025994288933047387340981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6701325718577396516454641 5025994288933047387340981)
                ·
                  refine ⟨471186964587473192563217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5025994288933047387340981 471186964587473192563217)
                  ·
                    rfl

theorem cell21_2064675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 2, 5].length) (baseStart_2064675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064675 prefixEnd_2064675 := by exact prefixLift 2064675
  have htrace : WordTrace (prefixWord ++ tailWord_2064675) baseStart_2064675 baseEnd_2064675 := by
    simpa [prefixWord, tailWord_2064675, baseEnd_2064675] using wordTrace_append hprefix tailTrace_2064675
  have hstable : (prefixWord ++ tailWord_2064675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064675).length < 2 ^ (prefixWord ++ tailWord_2064675).sum := by decide
  have hdescent : baseEnd_2064675 < baseStart_2064675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064813 : List Nat := [1, 5, 2, 2, 2, 9]
def baseStart_2064813 : Nat := 118140960795 + 2064813 * 2 ^ 59
def prefixEnd_2064813 : Nat := 4983230072969 + 3 ^ 40 * 2064813 * 2
def baseEnd_2064813 : Nat := 17452535483985763676405

theorem tailTrace_2064813 : CollatzResearch.WordTrace tailWord_2064813 prefixEnd_2064813 17452535483985763676405 := by
  unfold tailWord_2064813
  simp only [CollatzResearch.WordTrace]
  refine ⟨75309917068542617830247093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50206611379028411886831395 75309917068542617830247093)
  ·
    refine ⟨7060304725175870421585665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75309917068542617830247093 7060304725175870421585665)
    ·
      refine ⟨5295228543881902816189249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7060304725175870421585665 5295228543881902816189249)
      ·
        refine ⟨3971421407911427112141937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5295228543881902816189249 3971421407911427112141937)
        ·
          refine ⟨2978566055933570334106453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3971421407911427112141937 2978566055933570334106453)
          ·
            refine ⟨17452535483985763676405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2978566055933570334106453 17452535483985763676405)
            ·
              rfl

theorem cell21_2064813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 9].length) (baseStart_2064813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064813 prefixEnd_2064813 := by exact prefixLift 2064813
  have htrace : WordTrace (prefixWord ++ tailWord_2064813) baseStart_2064813 baseEnd_2064813 := by
    simpa [prefixWord, tailWord_2064813, baseEnd_2064813] using wordTrace_append hprefix tailTrace_2064813
  have hstable : (prefixWord ++ tailWord_2064813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064813).length < 2 ^ (prefixWord ++ tailWord_2064813).sum := by decide
  have hdescent : baseEnd_2064813 < baseStart_2064813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064844 : List Nat := [2, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_2064844 : Nat := 118140960795 + 2064844 * 2 ^ 59
def prefixEnd_2064844 : Nat := 4983230072969 + 3 ^ 40 * 2064844 * 2
def baseEnd_2064844 : Nat := 471225532689966454246205

theorem tailTrace_2064844 : CollatzResearch.WordTrace tailWord_2064844 prefixEnd_2064844 471225532689966454246205 := by
  unfold tailWord_2064844
  simp only [CollatzResearch.WordTrace]
  refine ⟨37655523865715155062312793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50207365154286873416417057 37655523865715155062312793)
  ·
    refine ⟨28241642899286366296734595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37655523865715155062312793 28241642899286366296734595)
    ·
      refine ⟨42362464348929549445101893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28241642899286366296734595 42362464348929549445101893)
      ·
        refine ⟨7942962065424290520956605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42362464348929549445101893 7942962065424290520956605)
        ·
          refine ⟨2978610774534108945358727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7942962065424290520956605 2978610774534108945358727)
          ·
            refine ⟨4467916161801163418038091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978610774534108945358727 4467916161801163418038091)
            ·
              refine ⟨6701874242701745127057137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4467916161801163418038091 6701874242701745127057137)
              ·
                refine ⟨5026405682026308845292853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6701874242701745127057137 5026405682026308845292853)
                ·
                  refine ⟨471225532689966454246205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5026405682026308845292853 471225532689966454246205)
                  ·
                    rfl

theorem cell21_2064844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_2064844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064844 prefixEnd_2064844 := by exact prefixLift 2064844
  have htrace : WordTrace (prefixWord ++ tailWord_2064844) baseStart_2064844 baseEnd_2064844 := by
    simpa [prefixWord, tailWord_2064844, baseEnd_2064844] using wordTrace_append hprefix tailTrace_2064844
  have hstable : (prefixWord ++ tailWord_2064844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064844).length < 2 ^ (prefixWord ++ tailWord_2064844).sum := by decide
  have hdescent : baseEnd_2064844 < baseStart_2064844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064861 : List Nat := [1, 4, 3, 1, 1, 1, 4, 3, 3]
def baseStart_2064861 : Nat := 118140960795 + 2064861 * 2 ^ 59
def prefixEnd_2064861 : Nat := 4983230072969 + 3 ^ 40 * 2064861 * 2
def baseEnd_2064861 : Nat := 471229412321578202462837

theorem tailTrace_2064861 : CollatzResearch.WordTrace tailWord_2064861 prefixEnd_2064861 471229412321578202462837 := by
  unfold tailWord_2064861
  simp only [CollatzResearch.WordTrace]
  refine ⟨75311667772368722027994437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50207778514912481351996291 75311667772368722027994437)
  ·
    refine ⟨14120937707319135380248957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75311667772368722027994437 14120937707319135380248957)
    ·
      refine ⟨5295351640244675767593359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14120937707319135380248957 5295351640244675767593359)
      ·
        refine ⟨7943027460367013651390039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5295351640244675767593359 7943027460367013651390039)
        ·
          refine ⟨11914541190550520477085059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7943027460367013651390039 11914541190550520477085059)
          ·
            refine ⟨17871811785825780715627589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11914541190550520477085059 17871811785825780715627589)
            ·
              refine ⟨3350964709842333884180173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17871811785825780715627589 3350964709842333884180173)
              ·
                refine ⟨1256611766190875206567565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3350964709842333884180173 1256611766190875206567565)
                ·
                  refine ⟨471229412321578202462837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256611766190875206567565 471229412321578202462837)
                  ·
                    rfl

theorem cell21_2064861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_2064861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064861 prefixEnd_2064861 := by exact prefixLift 2064861
  have htrace : WordTrace (prefixWord ++ tailWord_2064861) baseStart_2064861 baseEnd_2064861 := by
    simpa [prefixWord, tailWord_2064861, baseEnd_2064861] using wordTrace_append hprefix tailTrace_2064861
  have hstable : (prefixWord ++ tailWord_2064861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064861).length < 2 ^ (prefixWord ++ tailWord_2064861).sum := by decide
  have hdescent : baseEnd_2064861 < baseStart_2064861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064872 : List Nat := [2, 1, 4, 1, 1, 4, 8]
def baseStart_2064872 : Nat := 118140960795 + 2064872 * 2 ^ 59
def prefixEnd_2064872 : Nat := 4983230072969 + 3 ^ 40 * 2064872 * 2
def baseEnd_2064872 : Nat := 52359102519049403086609

theorem tailTrace_2064872 : CollatzResearch.WordTrace tailWord_2064872 prefixEnd_2064872 52359102519049403086609 := by
  unfold tailWord_2064872
  simp only [CollatzResearch.WordTrace]
  refine ⟨37656034487664435453322435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50208045983552580604429913 37656034487664435453322435)
  ·
    refine ⟨56484051731496653179983653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37656034487664435453322435 56484051731496653179983653)
    ·
      refine ⟨10590759699655622471246935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56484051731496653179983653 10590759699655622471246935)
      ·
        refine ⟨15886139549483433706870403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10590759699655622471246935 15886139549483433706870403)
        ·
          refine ⟨23829209324225150560305605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15886139549483433706870403 23829209324225150560305605)
          ·
            refine ⟨4467976748292215730057301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23829209324225150560305605 4467976748292215730057301)
            ·
              refine ⟨52359102519049403086609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4467976748292215730057301 52359102519049403086609)
              ·
                rfl

theorem cell21_2064872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 8].length) (baseStart_2064872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064872 prefixEnd_2064872 := by exact prefixLift 2064872
  have htrace : WordTrace (prefixWord ++ tailWord_2064872) baseStart_2064872 baseEnd_2064872 := by
    simpa [prefixWord, tailWord_2064872, baseEnd_2064872] using wordTrace_append hprefix tailTrace_2064872
  have hstable : (prefixWord ++ tailWord_2064872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064872).length < 2 ^ (prefixWord ++ tailWord_2064872).sum := by decide
  have hdescent : baseEnd_2064872 < baseStart_2064872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064917 : List Nat := [1, 3, 2, 1, 3, 1, 1, 1, 8]
def baseStart_2064917 : Nat := 118140960795 + 2064917 * 2 ^ 59
def prefixEnd_2064917 : Nat := 4983230072969 + 3 ^ 40 * 2064917 * 2
def baseEnd_2064917 : Nat := 471242192284534549529389

theorem tailTrace_2064917 : CollatzResearch.WordTrace tailWord_2064917 prefixEnd_2064917 471242192284534549529389 := by
  unfold tailWord_2064917
  simp only [CollatzResearch.WordTrace]
  refine ⟨75313710260165843592033005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50209140173443895728022003 75313710260165843592033005)
  ·
    refine ⟨28242641347562191347012377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75313710260165843592033005 28242641347562191347012377)
    ·
      refine ⟨21181981010671643510259283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28242641347562191347012377 21181981010671643510259283)
      ·
        refine ⟨31772971516007465265388925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21181981010671643510259283 31772971516007465265388925)
        ·
          refine ⟨11914864318502799474520847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31772971516007465265388925 11914864318502799474520847)
          ·
            refine ⟨17872296477754199211781271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11914864318502799474520847 17872296477754199211781271)
            ·
              refine ⟨26808444716631298817671907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17872296477754199211781271 26808444716631298817671907)
              ·
                refine ⟨40212667074946948226507861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26808444716631298817671907 40212667074946948226507861)
                ·
                  refine ⟨471242192284534549529389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40212667074946948226507861 471242192284534549529389)
                  ·
                    rfl

theorem cell21_2064917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_2064917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064917 prefixEnd_2064917 := by exact prefixLift 2064917
  have htrace : WordTrace (prefixWord ++ tailWord_2064917) baseStart_2064917 baseEnd_2064917 := by
    simpa [prefixWord, tailWord_2064917, baseEnd_2064917] using wordTrace_append hprefix tailTrace_2064917
  have hstable : (prefixWord ++ tailWord_2064917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064917).length < 2 ^ (prefixWord ++ tailWord_2064917).sum := by decide
  have hdescent : baseEnd_2064917 < baseStart_2064917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2064996 : List Nat := [2, 3, 1, 1, 2, 2, 3, 4, 3]
def baseStart_2064996 : Nat := 118140960795 + 2064996 * 2 ^ 59
def prefixEnd_2064996 : Nat := 4983230072969 + 3 ^ 40 * 2064996 * 2
def baseEnd_2064996 : Nat := 471260221160847967712561

theorem tailTrace_2064996 : CollatzResearch.WordTrace tailWord_2064996 prefixEnd_2064996 471260221160847967712561 := by
  unfold tailWord_2064996
  simp only [CollatzResearch.WordTrace]
  refine ⟨37658295813439820042079421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50211061084586426722772561 37658295813439820042079421)
  ·
    refine ⟨14121860930039932515779783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37658295813439820042079421 14121860930039932515779783)
    ·
      refine ⟨21182791395059898773669675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14121860930039932515779783 21182791395059898773669675)
      ·
        refine ⟨31774187092589848160504513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21182791395059898773669675 31774187092589848160504513)
        ·
          refine ⟨23830640319442386120378385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31774187092589848160504513 23830640319442386120378385)
          ·
            refine ⟨17872980239581789590283789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23830640319442386120378385 17872980239581789590283789)
            ·
              refine ⟨6702367589843171096356421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17872980239581789590283789 6702367589843171096356421)
              ·
                refine ⟨1256693923095594580566829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6702367589843171096356421 1256693923095594580566829)
                ·
                  refine ⟨471260221160847967712561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256693923095594580566829 471260221160847967712561)
                  ·
                    rfl

theorem cell21_2064996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 4, 3].length) (baseStart_2064996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2064996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2064996 prefixEnd_2064996 := by exact prefixLift 2064996
  have htrace : WordTrace (prefixWord ++ tailWord_2064996) baseStart_2064996 baseEnd_2064996 := by
    simpa [prefixWord, tailWord_2064996, baseEnd_2064996] using wordTrace_append hprefix tailTrace_2064996
  have hstable : (prefixWord ++ tailWord_2064996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2064996).length < 2 ^ (prefixWord ++ tailWord_2064996).sum := by decide
  have hdescent : baseEnd_2064996 < baseStart_2064996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2064996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065044 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 4]
def baseStart_2065044 : Nat := 118140960795 + 2065044 * 2 ^ 59
def prefixEnd_2065044 : Nat := 4983230072969 + 3 ^ 40 * 2065044 * 2
def baseEnd_2065044 : Nat := 471271175414810550912463

theorem tailTrace_2065044 : CollatzResearch.WordTrace tailWord_2065044 prefixEnd_2065044 471271175414810550912463 := by
  unfold tailWord_2065044
  simp only [CollatzResearch.WordTrace]
  refine ⟨37659171165352872140953093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50212228220470496187937457 37659171165352872140953093)
  ·
    refine ⟨7061094593503663526428705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37659171165352872140953093 7061094593503663526428705)
    ·
      refine ⟨5295820945127747644821529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7061094593503663526428705 5295820945127747644821529)
      ·
        refine ⟨3971865708845810733616147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5295820945127747644821529 3971865708845810733616147)
        ·
          refine ⟨5957798563268716100424221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971865708845810733616147 5957798563268716100424221)
          ·
            refine ⟨2234174461225768537659083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5957798563268716100424221 2234174461225768537659083)
            ·
              refine ⟨3351261691838652806488625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234174461225768537659083 3351261691838652806488625)
              ·
                refine ⟨2513446268878989604866469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351261691838652806488625 2513446268878989604866469)
                ·
                  refine ⟨471271175414810550912463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513446268878989604866469 471271175414810550912463)
                  ·
                    rfl

theorem cell21_2065044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_2065044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065044 prefixEnd_2065044 := by exact prefixLift 2065044
  have htrace : WordTrace (prefixWord ++ tailWord_2065044) baseStart_2065044 baseEnd_2065044 := by
    simpa [prefixWord, tailWord_2065044, baseEnd_2065044] using wordTrace_append hprefix tailTrace_2065044
  have hstable : (prefixWord ++ tailWord_2065044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065044).length < 2 ^ (prefixWord ++ tailWord_2065044).sum := by decide
  have hdescent : baseEnd_2065044 < baseStart_2065044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065100 : List Nat := [2, 2, 1, 5, 1, 1, 9]
def baseStart_2065100 : Nat := 118140960795 + 2065100 * 2 ^ 59
def prefixEnd_2065100 : Nat := 4983230072969 + 3 ^ 40 * 2065100 * 2
def baseEnd_2065100 : Nat := 52364883930862988664335

theorem tailTrace_2065100 : CollatzResearch.WordTrace tailWord_2065100 prefixEnd_2065100 52364883930862988664335 := by
  unfold tailWord_2065100
  simp only [CollatzResearch.WordTrace]
  refine ⟨37660192409251432922972377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50213589879001910563963169 37660192409251432922972377)
  ·
    refine ⟨28245144306938574692229283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37660192409251432922972377 28245144306938574692229283)
    ·
      refine ⟨42367716460407862038343925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28245144306938574692229283 42367716460407862038343925)
      ·
        refine ⟨3971973418163237066094743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 42367716460407862038343925 3971973418163237066094743)
        ·
          refine ⟨5957960127244855599142115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3971973418163237066094743 5957960127244855599142115)
          ·
            refine ⟨8936940190867283398713173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5957960127244855599142115 8936940190867283398713173)
            ·
              refine ⟨52364883930862988664335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8936940190867283398713173 52364883930862988664335)
              ·
                rfl

theorem cell21_2065100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 9].length) (baseStart_2065100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065100 prefixEnd_2065100 := by exact prefixLift 2065100
  have htrace : WordTrace (prefixWord ++ tailWord_2065100) baseStart_2065100 baseEnd_2065100 := by
    simpa [prefixWord, tailWord_2065100, baseEnd_2065100] using wordTrace_append hprefix tailTrace_2065100
  have hstable : (prefixWord ++ tailWord_2065100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065100).length < 2 ^ (prefixWord ++ tailWord_2065100).sum := by decide
  have hdescent : baseEnd_2065100 < baseStart_2065100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065106 : List Nat := [3, 2, 2, 2, 3, 1, 3, 2, 3]
def baseStart_2065106 : Nat := 118140960795 + 2065106 * 2 ^ 59
def prefixEnd_2065106 : Nat := 4983230072969 + 3 ^ 40 * 2065106 * 2
def baseEnd_2065106 : Nat := 471285324659512220879003

theorem tailTrace_2065106 : CollatzResearch.WordTrace tailWord_2065106 prefixEnd_2065106 471285324659512220879003 := by
  unfold tailWord_2065106
  simp only [CollatzResearch.WordTrace]
  refine ⟨18830150914120282217665793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50213735770987419247108781 18830150914120282217665793)
  ·
    refine ⟨14122613185590211663249345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18830150914120282217665793 14122613185590211663249345)
    ·
      refine ⟨10591959889192658747437009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14122613185590211663249345 10591959889192658747437009)
      ·
        refine ⟨7943969916894494060577757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10591959889192658747437009 7943969916894494060577757)
        ·
          refine ⟨2978988718835435272716659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7943969916894494060577757 2978988718835435272716659)
          ·
            refine ⟨4468483078253152909074989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2978988718835435272716659 4468483078253152909074989)
            ·
              refine ⟨1675681154344932340903121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4468483078253152909074989 1675681154344932340903121)
              ·
                refine ⟨1256760865758699255677341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675681154344932340903121 1256760865758699255677341)
                ·
                  refine ⟨471285324659512220879003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256760865758699255677341 471285324659512220879003)
                  ·
                    rfl

theorem cell21_2065106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_2065106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065106 prefixEnd_2065106 := by exact prefixLift 2065106
  have htrace : WordTrace (prefixWord ++ tailWord_2065106) baseStart_2065106 baseEnd_2065106 := by
    simpa [prefixWord, tailWord_2065106, baseEnd_2065106] using wordTrace_append hprefix tailTrace_2065106
  have hstable : (prefixWord ++ tailWord_2065106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065106).length < 2 ^ (prefixWord ++ tailWord_2065106).sum := by decide
  have hdescent : baseEnd_2065106 < baseStart_2065106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065162 : List Nat := [3, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_2065162 : Nat := 118140960795 + 2065162 * 2 ^ 59
def prefixEnd_2065162 : Nat := 4983230072969 + 3 ^ 40 * 2065162 * 2
def baseEnd_2065162 : Nat := 471298104622468567945555

theorem tailTrace_2065162 : CollatzResearch.WordTrace tailWord_2065162 prefixEnd_2065162 471298104622468567945555 := by
  unfold tailWord_2065162
  simp only [CollatzResearch.WordTrace]
  refine ⟨18830661536069562608675435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50215097429518833623134493 18830661536069562608675435)
  ·
    refine ⟨28245992304104343913013153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18830661536069562608675435 28245992304104343913013153)
    ·
      refine ⟨21184494228078257934759865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28245992304104343913013153 21184494228078257934759865)
      ·
        refine ⟨15888370671058693451069899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21184494228078257934759865 15888370671058693451069899)
        ·
          refine ⟨23832556006588040176604849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15888370671058693451069899 23832556006588040176604849)
          ·
            refine ⟨17874417004941030132453637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23832556006588040176604849 17874417004941030132453637)
            ·
              refine ⟨3351453188426443149835057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17874417004941030132453637 3351453188426443149835057)
              ·
                refine ⟨2513589891319832362376293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3351453188426443149835057 2513589891319832362376293)
                ·
                  refine ⟨471298104622468567945555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513589891319832362376293 471298104622468567945555)
                  ·
                    rfl

theorem cell21_2065162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_2065162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065162 prefixEnd_2065162 := by exact prefixLift 2065162
  have htrace : WordTrace (prefixWord ++ tailWord_2065162) baseStart_2065162 baseEnd_2065162 := by
    simpa [prefixWord, tailWord_2065162, baseEnd_2065162] using wordTrace_append hprefix tailTrace_2065162
  have hstable : (prefixWord ++ tailWord_2065162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065162).length < 2 ^ (prefixWord ++ tailWord_2065162).sum := by decide
  have hdescent : baseEnd_2065162 < baseStart_2065162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065221 : List Nat := [1, 3, 1, 1, 1, 2, 2, 6, 4]
def baseStart_2065221 : Nat := 118140960795 + 2065221 * 2 ^ 59
def prefixEnd_2065221 : Nat := 4983230072969 + 3 ^ 40 * 2065221 * 2
def baseEnd_2065221 : Nat := 471311569226297576462101

theorem tailTrace_2065221 : CollatzResearch.WordTrace tailWord_2065221 prefixEnd_2065221 471311569226297576462101 := by
  unfold tailWord_2065221
  simp only [CollatzResearch.WordTrace]
  refine ⟨75324798051064503511099517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50216532034043002340733011 75324798051064503511099517)
  ·
    refine ⟨28246799269149188816662319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75324798051064503511099517 28246799269149188816662319)
    ·
      refine ⟨42370198903723783224993479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28246799269149188816662319 42370198903723783224993479)
      ·
        refine ⟨63555298355585674837490219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42370198903723783224993479 63555298355585674837490219)
        ·
          refine ⟨95332947533378512256235329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63555298355585674837490219 95332947533378512256235329)
          ·
            refine ⟨71499710650033884192176497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95332947533378512256235329 71499710650033884192176497)
            ·
              refine ⟨53624782987525413144132373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71499710650033884192176497 53624782987525413144132373)
              ·
                refine ⟨2513661702540253741131205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 53624782987525413144132373 2513661702540253741131205)
                ·
                  refine ⟨471311569226297576462101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513661702540253741131205 471311569226297576462101)
                  ·
                    rfl

theorem cell21_2065221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_2065221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065221 prefixEnd_2065221 := by exact prefixLift 2065221
  have htrace : WordTrace (prefixWord ++ tailWord_2065221) baseStart_2065221 baseEnd_2065221 := by
    simpa [prefixWord, tailWord_2065221, baseEnd_2065221] using wordTrace_append hprefix tailTrace_2065221
  have hstable : (prefixWord ++ tailWord_2065221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065221).length < 2 ^ (prefixWord ++ tailWord_2065221).sum := by decide
  have hdescent : baseEnd_2065221 < baseStart_2065221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065252 : List Nat := [2, 3, 1, 1, 4, 2, 1, 7]
def baseStart_2065252 : Nat := 118140960795 + 2065252 * 2 ^ 59
def prefixEnd_2065252 : Nat := 4983230072969 + 3 ^ 40 * 2065252 * 2
def baseEnd_2065252 : Nat := 157106214616216137148457

theorem tailTrace_2065252 : CollatzResearch.WordTrace tailWord_2065252 prefixEnd_2065252 157106214616216137148457 := by
  unfold tailWord_2065252
  simp only [CollatzResearch.WordTrace]
  refine ⟨37662964356976097902739005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50217285809301463870318673 37662964356976097902739005)
  ·
    refine ⟨14123611633866036713527127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37662964356976097902739005 14123611633866036713527127)
    ·
      refine ⟨21185417450799055070290691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14123611633866036713527127 21185417450799055070290691)
      ·
        refine ⟨31778126176198582605436037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21185417450799055070290691 31778126176198582605436037)
        ·
          refine ⟨5958398658037234238519257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31778126176198582605436037 5958398658037234238519257)
          ·
            refine ⟨4468798993527925678889443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5958398658037234238519257 4468798993527925678889443)
            ·
              refine ⟨6703198490291888518334165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4468798993527925678889443 6703198490291888518334165)
              ·
                refine ⟨157106214616216137148457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6703198490291888518334165 157106214616216137148457)
                ·
                  rfl

theorem cell21_2065252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_2065252 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065252 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065252 prefixEnd_2065252 := by exact prefixLift 2065252
  have htrace : WordTrace (prefixWord ++ tailWord_2065252) baseStart_2065252 baseEnd_2065252 := by
    simpa [prefixWord, tailWord_2065252, baseEnd_2065252] using wordTrace_append hprefix tailTrace_2065252
  have hstable : (prefixWord ++ tailWord_2065252).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065252).length < 2 ^ (prefixWord ++ tailWord_2065252).sum := by decide
  have hdescent : baseEnd_2065252 < baseStart_2065252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065266 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 7]
def baseStart_2065266 : Nat := 118140960795 + 2065266 * 2 ^ 59
def prefixEnd_2065266 : Nat := 4983230072969 + 3 ^ 40 * 2065266 * 2
def baseEnd_2065266 : Nat := 471321838839387498212009

theorem tailTrace_2065266 : CollatzResearch.WordTrace tailWord_2065266 prefixEnd_2065266 471321838839387498212009 := by
  unfold tailWord_2065266
  simp only [CollatzResearch.WordTrace]
  refine ⟨18831609833975369049121913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50217626223934317464325101 18831609833975369049121913)
  ·
    refine ⟨14123707375481526786841435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18831609833975369049121913 14123707375481526786841435)
    ·
      refine ⟨21185561063222290180262153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14123707375481526786841435 21185561063222290180262153)
      ·
        refine ⟨15889170797416717635196615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21185561063222290180262153 15889170797416717635196615)
        ·
          refine ⟨23833756196125076452794923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15889170797416717635196615 23833756196125076452794923)
          ·
            refine ⟨35750634294187614679192385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23833756196125076452794923 35750634294187614679192385)
            ·
              refine ⟨26812975720640711009394289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35750634294187614679192385 26812975720640711009394289)
              ·
                refine ⟨20109731790480533257045717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26812975720640711009394289 20109731790480533257045717)
                ·
                  refine ⟨471321838839387498212009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20109731790480533257045717 471321838839387498212009)
                  ·
                    rfl

theorem cell21_2065266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_2065266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065266 prefixEnd_2065266 := by exact prefixLift 2065266
  have htrace : WordTrace (prefixWord ++ tailWord_2065266) baseStart_2065266 baseEnd_2065266 := by
    simpa [prefixWord, tailWord_2065266, baseEnd_2065266] using wordTrace_append hprefix tailTrace_2065266
  have hstable : (prefixWord ++ tailWord_2065266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065266).length < 2 ^ (prefixWord ++ tailWord_2065266).sum := by decide
  have hdescent : baseEnd_2065266 < baseStart_2065266 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065390 : List Nat := [4, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_2065390 : Nat := 118140960795 + 2065390 * 2 ^ 59
def prefixEnd_2065390 : Nat := 4983230072969 + 3 ^ 40 * 2065390 * 2
def baseEnd_2065390 : Nat := 471350137328790838145089

theorem tailTrace_2065390 : CollatzResearch.WordTrace tailWord_2065390 prefixEnd_2065390 471350137328790838145089 := by
  unfold tailWord_2065390
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416370248431530671750203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50220641324968163582667749 9416370248431530671750203)
  ·
    refine ⟨14124555372647296007625305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9416370248431530671750203 14124555372647296007625305)
    ·
      refine ⟨10593416529485472005718979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14124555372647296007625305 10593416529485472005718979)
      ·
        refine ⟨15890124794228208008578469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10593416529485472005718979 15890124794228208008578469)
        ·
          refine ⟨2979398398917789001608463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15890124794228208008578469 2979398398917789001608463)
          ·
            refine ⟨4469097598376683502412695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979398398917789001608463 4469097598376683502412695)
            ·
              refine ⟨6703646397565025253619043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469097598376683502412695 6703646397565025253619043)
              ·
                refine ⟨10055469596347537880428565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6703646397565025253619043 10055469596347537880428565)
                ·
                  refine ⟨471350137328790838145089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10055469596347537880428565 471350137328790838145089)
                  ·
                    rfl

theorem cell21_2065390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_2065390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065390 prefixEnd_2065390 := by exact prefixLift 2065390
  have htrace : WordTrace (prefixWord ++ tailWord_2065390) baseStart_2065390 baseEnd_2065390 := by
    simpa [prefixWord, tailWord_2065390, baseEnd_2065390] using wordTrace_append hprefix tailTrace_2065390
  have hstable : (prefixWord ++ tailWord_2065390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065390).length < 2 ^ (prefixWord ++ tailWord_2065390).sum := by decide
  have hdescent : baseEnd_2065390 < baseStart_2065390 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065452 : List Nat := [2, 2, 1, 1, 1, 2, 7, 2, 3]
def baseStart_2065452 : Nat := 118140960795 + 2065452 * 2 ^ 59
def prefixEnd_2065452 : Nat := 4983230072969 + 3 ^ 40 * 2065452 * 2
def baseEnd_2065452 : Nat := 471364286573492508111629

theorem tailTrace_2065452 : CollatzResearch.WordTrace tailWord_2065452 prefixEnd_2065452 471364286573492508111629 := by
  unfold tailWord_2065452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37666611656613814981379305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50222148875485086641839073 37666611656613814981379305)
  ·
    refine ⟨28249958742460361236034479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37666611656613814981379305 28249958742460361236034479)
    ·
      refine ⟨42374938113690541854051719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28249958742460361236034479 42374938113690541854051719)
      ·
        refine ⟨63562407170535812781077579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42374938113690541854051719 63562407170535812781077579)
        ·
          refine ⟨95343610755803719171616369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63562407170535812781077579 95343610755803719171616369)
          ·
            refine ⟨71507708066852789378712277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95343610755803719171616369 71507708066852789378712277)
            ·
              refine ⟨1675961907816862251063569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71507708066852789378712277 1675961907816862251063569)
              ·
                refine ⟨1256971430862646688297677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1675961907816862251063569 1256971430862646688297677)
                ·
                  refine ⟨471364286573492508111629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1256971430862646688297677 471364286573492508111629)
                  ·
                    rfl

theorem cell21_2065452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_2065452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065452 prefixEnd_2065452 := by exact prefixLift 2065452
  have htrace : WordTrace (prefixWord ++ tailWord_2065452) baseStart_2065452 baseEnd_2065452 := by
    simpa [prefixWord, tailWord_2065452, baseEnd_2065452] using wordTrace_append hprefix tailTrace_2065452
  have hstable : (prefixWord ++ tailWord_2065452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065452).length < 2 ^ (prefixWord ++ tailWord_2065452).sum := by decide
  have hdescent : baseEnd_2065452 < baseStart_2065452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065466 : List Nat := [3, 1, 1, 1, 3, 1, 6, 1, 4]
def baseStart_2065466 : Nat := 118140960795 + 2065466 * 2 ^ 59
def prefixEnd_2065466 : Nat := 4983230072969 + 3 ^ 40 * 2065466 * 2
def baseEnd_2065466 : Nat := 471367481564231594878267

theorem tailTrace_2065466 : CollatzResearch.WordTrace tailWord_2065466 prefixEnd_2065466 471367481564231594878267 := by
  unfold tailWord_2065466
  simp only [CollatzResearch.WordTrace]
  refine ⟨18833433483794227588442063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50222489290117940235845501 18833433483794227588442063)
  ·
    refine ⟨28250150225691341382663095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18833433483794227588442063 28250150225691341382663095)
    ·
      refine ⟨42375225338537012073994643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28250150225691341382663095 42375225338537012073994643)
      ·
        refine ⟨63562838007805518110991965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42375225338537012073994643 63562838007805518110991965)
        ·
          refine ⟨23836064252927069291621987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63562838007805518110991965 23836064252927069291621987)
          ·
            refine ⟨35754096379390603937432981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23836064252927069291621987 35754096379390603937432981)
            ·
              refine ⟨1675973267783934559567171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 35754096379390603937432981 1675973267783934559567171)
              ·
                refine ⟨2513959901675901839350757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675973267783934559567171 2513959901675901839350757)
                ·
                  refine ⟨471367481564231594878267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2513959901675901839350757 471367481564231594878267)
                  ·
                    rfl

theorem cell21_2065466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 4].length) (baseStart_2065466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065466 prefixEnd_2065466 := by exact prefixLift 2065466
  have htrace : WordTrace (prefixWord ++ tailWord_2065466) baseStart_2065466 baseEnd_2065466 := by
    simpa [prefixWord, tailWord_2065466, baseEnd_2065466] using wordTrace_append hprefix tailTrace_2065466
  have hstable : (prefixWord ++ tailWord_2065466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065466).length < 2 ^ (prefixWord ++ tailWord_2065466).sum := by decide
  have hdescent : baseEnd_2065466 < baseStart_2065466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065590 : List Nat := [5, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2065590 : Nat := 118140960795 + 2065590 * 2 ^ 59
def prefixEnd_2065590 : Nat := 4983230072969 + 3 ^ 40 * 2065590 * 2
def baseEnd_2065590 : Nat := 157131926684544978270449

theorem tailTrace_2065590 : CollatzResearch.WordTrace tailWord_2065590 prefixEnd_2065590 157131926684544978270449 := by
  unfold tailWord_2065590
  simp only [CollatzResearch.WordTrace]
  refine ⟨4708641036670479970705139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50225504391151786354188149 4708641036670479970705139)
  ·
    refine ⟨7062961555005719956057709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4708641036670479970705139 7062961555005719956057709)
    ·
      refine ⟨2648610583127144983521641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7062961555005719956057709 2648610583127144983521641)
      ·
        refine ⟨1986457937345358737641231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2648610583127144983521641 1986457937345358737641231)
        ·
          refine ⟨2979686906018038106461847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1986457937345358737641231 2979686906018038106461847)
          ·
            refine ⟨4469530359027057159692771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2979686906018038106461847 4469530359027057159692771)
            ·
              refine ⟨6704295538540585739539157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4469530359027057159692771 6704295538540585739539157)
              ·
                refine ⟨157131926684544978270449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6704295538540585739539157 157131926684544978270449)
                ·
                  rfl

theorem cell21_2065590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2065590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065590 prefixEnd_2065590 := by exact prefixLift 2065590
  have htrace : WordTrace (prefixWord ++ tailWord_2065590) baseStart_2065590 baseEnd_2065590 := by
    simpa [prefixWord, tailWord_2065590, baseEnd_2065590] using wordTrace_append hprefix tailTrace_2065590
  have hstable : (prefixWord ++ tailWord_2065590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065590).length < 2 ^ (prefixWord ++ tailWord_2065590).sum := by decide
  have hdescent : baseEnd_2065590 < baseStart_2065590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065621 : List Nat := [1, 3, 2, 4, 1, 2, 3, 2, 3]
def baseStart_2065621 : Nat := 118140960795 + 2065621 * 2 ^ 59
def prefixEnd_2065621 : Nat := 4983230072969 + 3 ^ 40 * 2065621 * 2
def baseEnd_2065621 : Nat := 471402854675985769794617

theorem tailTrace_2065621 : CollatzResearch.WordTrace tailWord_2065621 prefixEnd_2065621 471402854675985769794617 := by
  unfold tailWord_2065621
  simp only [CollatzResearch.WordTrace]
  refine ⟨75339387249615371825660717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50226258166410247883773811 75339387249615371825660717)
  ·
    refine ⟨28252270218605764434622769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75339387249615371825660717 28252270218605764434622769)
    ·
      refine ⟨21189202663954323325967077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28252270218605764434622769 21189202663954323325967077)
      ·
        refine ⟨3972975499491435623618827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21189202663954323325967077 3972975499491435623618827)
        ·
          refine ⟨5959463249237153435428241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3972975499491435623618827 5959463249237153435428241)
          ·
            refine ⟨4469597436927865076571181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5959463249237153435428241 4469597436927865076571181)
            ·
              refine ⟨1676099038847949403714193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4469597436927865076571181 1676099038847949403714193)
              ·
                refine ⟨1257074279135962052785645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676099038847949403714193 1257074279135962052785645)
                ·
                  refine ⟨471402854675985769794617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257074279135962052785645 471402854675985769794617)
                  ·
                    rfl

theorem cell21_2065621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_2065621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065621 prefixEnd_2065621 := by exact prefixLift 2065621
  have htrace : WordTrace (prefixWord ++ tailWord_2065621) baseStart_2065621 baseEnd_2065621 := by
    simpa [prefixWord, tailWord_2065621, baseEnd_2065621] using wordTrace_append hprefix tailTrace_2065621
  have hstable : (prefixWord ++ tailWord_2065621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065621).length < 2 ^ (prefixWord ++ tailWord_2065621).sum := by decide
  have hdescent : baseEnd_2065621 < baseStart_2065621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065646 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 5]
def baseStart_2065646 : Nat := 118140960795 + 2065646 * 2 ^ 59
def prefixEnd_2065646 : Nat := 4983230072969 + 3 ^ 40 * 2065646 * 2
def baseEnd_2065646 : Nat := 471408560016591281877899

theorem tailTrace_2065646 : CollatzResearch.WordTrace tailWord_2065646 prefixEnd_2065646 471408560016591281877899 := by
  unfold tailWord_2065646
  simp only [CollatzResearch.WordTrace]
  refine ⟨9417537384315600136915099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50226866049683200730213861 9417537384315600136915099)
  ·
    refine ⟨14126306076473400205372649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9417537384315600136915099 14126306076473400205372649)
    ·
      refine ⟨10594729557355050154029487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14126306076473400205372649 10594729557355050154029487)
      ·
        refine ⟨15892094336032575231044231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10594729557355050154029487 15892094336032575231044231)
        ·
          refine ⟨23838141504048862846566347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15892094336032575231044231 23838141504048862846566347)
          ·
            refine ⟨35757212256073294269849521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23838141504048862846566347 35757212256073294269849521)
            ·
              refine ⟨26817909192054970702387141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35757212256073294269849521 26817909192054970702387141)
              ·
                refine ⟨5028357973510307006697589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26817909192054970702387141 5028357973510307006697589)
                ·
                  refine ⟨471408560016591281877899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5028357973510307006697589 471408560016591281877899)
                  ·
                    rfl

theorem cell21_2065646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_2065646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065646 prefixEnd_2065646 := by exact prefixLift 2065646
  have htrace : WordTrace (prefixWord ++ tailWord_2065646) baseStart_2065646 baseEnd_2065646 := by
    simpa [prefixWord, tailWord_2065646, baseEnd_2065646] using wordTrace_append hprefix tailTrace_2065646
  have hstable : (prefixWord ++ tailWord_2065646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065646).length < 2 ^ (prefixWord ++ tailWord_2065646).sum := by decide
  have hdescent : baseEnd_2065646 < baseStart_2065646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065790 : List Nat := [4, 2, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2065790 : Nat := 118140960795 + 2065790 * 2 ^ 59
def prefixEnd_2065790 : Nat := 4983230072969 + 3 ^ 40 * 2065790 * 2
def baseEnd_2065790 : Nat := 471441422778479031477605

theorem tailTrace_2065790 : CollatzResearch.WordTrace tailWord_2065790 prefixEnd_2065790 471441422778479031477605 := by
  unfold tailWord_2065790
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418193898250389211070353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50230367457335409125708549 9418193898250389211070353)
  ·
    refine ⟨7063645423687791908302765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9418193898250389211070353 7063645423687791908302765)
    ·
      refine ⟨2648867033882921965613537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7063645423687791908302765 2648867033882921965613537)
      ·
        refine ⟨1986650275412191474210153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2648867033882921965613537 1986650275412191474210153)
        ·
          refine ⟨1489987706559143605657615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1986650275412191474210153 1489987706559143605657615)
          ·
            refine ⟨2234981559838715408486423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1489987706559143605657615 2234981559838715408486423)
            ·
              refine ⟨3352472339758073112729635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234981559838715408486423 3352472339758073112729635)
              ·
                refine ⟨5028708509637109669094453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352472339758073112729635 5028708509637109669094453)
                ·
                  refine ⟨471441422778479031477605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5028708509637109669094453 471441422778479031477605)
                  ·
                    rfl

theorem cell21_2065790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2065790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065790 prefixEnd_2065790 := by exact prefixLift 2065790
  have htrace : WordTrace (prefixWord ++ tailWord_2065790) baseStart_2065790 baseEnd_2065790 := by
    simpa [prefixWord, tailWord_2065790, baseEnd_2065790] using wordTrace_append hprefix tailTrace_2065790
  have hstable : (prefixWord ++ tailWord_2065790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065790).length < 2 ^ (prefixWord ++ tailWord_2065790).sum := by decide
  have hdescent : baseEnd_2065790 < baseStart_2065790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065849 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 3]
def baseStart_2065849 : Nat := 118140960795 + 2065849 * 2 ^ 59
def prefixEnd_2065849 : Nat := 4983230072969 + 3 ^ 40 * 2065849 * 2
def baseEnd_2065849 : Nat := 471454887382308039994151

theorem tailTrace_2065849 : CollatzResearch.WordTrace tailWord_2065849 prefixEnd_2065849 471454887382308039994151 := by
  unfold tailWord_2065849
  simp only [CollatzResearch.WordTrace]
  refine ⟨75347703092789366764960601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50231802061859577843307067 75347703092789366764960601)
  ·
    refine ⟨56510777319592025073720451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75347703092789366764960601 56510777319592025073720451)
    ·
      refine ⟨84766165979388037610580677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56510777319592025073720451 84766165979388037610580677)
      ·
        refine ⟨15893656121135257051983877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84766165979388037610580677 15893656121135257051983877)
        ·
          refine ⟨2980060522712860697246977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15893656121135257051983877 2980060522712860697246977)
          ·
            refine ⟨2235045392034645522935233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2980060522712860697246977 2235045392034645522935233)
            ·
              refine ⟨1676284044025984142201425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235045392034645522935233 1676284044025984142201425)
              ·
                refine ⟨1257213033019488106651069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676284044025984142201425 1257213033019488106651069)
                ·
                  refine ⟨471454887382308039994151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257213033019488106651069 471454887382308039994151)
                  ·
                    rfl

theorem cell21_2065849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_2065849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065849 prefixEnd_2065849 := by exact prefixLift 2065849
  have htrace : WordTrace (prefixWord ++ tailWord_2065849) baseStart_2065849 baseEnd_2065849 := by
    simpa [prefixWord, tailWord_2065849, baseEnd_2065849] using wordTrace_append hprefix tailTrace_2065849
  have hstable : (prefixWord ++ tailWord_2065849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065849).length < 2 ^ (prefixWord ++ tailWord_2065849).sum := by decide
  have hdescent : baseEnd_2065849 < baseStart_2065849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065860 : List Nat := [2, 3, 3, 2, 1, 1, 3, 6]
def baseStart_2065860 : Nat := 118140960795 + 2065860 * 2 ^ 59
def prefixEnd_2065860 : Nat := 4983230072969 + 3 ^ 40 * 2065860 * 2
def baseEnd_2065860 : Nat := 157152465910724821770265

theorem tailTrace_2065860 : CollatzResearch.WordTrace tailWord_2065860 prefixEnd_2065860 157152465910724821770265 := by
  unfold tailWord_2065860
  simp only [CollatzResearch.WordTrace]
  refine ⟨37674052147874757821805517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50232069530499677095740689 37674052147874757821805517)
  ·
    refine ⟨14127769555453034183177069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37674052147874757821805517 14127769555453034183177069)
    ·
      refine ⟨5297913583294887818691401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14127769555453034183177069 5297913583294887818691401)
      ·
        refine ⟨3973435187471165864018551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5297913583294887818691401 3973435187471165864018551)
        ·
          refine ⟨5960152781206748796027827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3973435187471165864018551 5960152781206748796027827)
          ·
            refine ⟨8940229171810123194041741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960152781206748796027827 8940229171810123194041741)
            ·
              refine ⟨3352585939428796197765653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8940229171810123194041741 3352585939428796197765653)
              ·
                refine ⟨157152465910724821770265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3352585939428796197765653 157152465910724821770265)
                ·
                  rfl

theorem cell21_2065860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 6].length) (baseStart_2065860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065860 prefixEnd_2065860 := by exact prefixLift 2065860
  have htrace : WordTrace (prefixWord ++ tailWord_2065860) baseStart_2065860 baseEnd_2065860 := by
    simpa [prefixWord, tailWord_2065860, baseEnd_2065860] using wordTrace_append hprefix tailTrace_2065860
  have hstable : (prefixWord ++ tailWord_2065860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065860).length < 2 ^ (prefixWord ++ tailWord_2065860).sum := by decide
  have hdescent : baseEnd_2065860 < baseStart_2065860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065891 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 3]
def baseStart_2065891 : Nat := 118140960795 + 2065891 * 2 ^ 59
def prefixEnd_2065891 : Nat := 4983230072969 + 3 ^ 40 * 2065891 * 2
def baseEnd_2065891 : Nat := 471464472354525300294065

theorem tailTrace_2065891 : CollatzResearch.WordTrace tailWord_2065891 prefixEnd_2065891 471464472354525300294065 := by
  unfold tailWord_2065891
  simp only [CollatzResearch.WordTrace]
  refine ⟨75349234958637207937989527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50232823305758138625326351 75349234958637207937989527)
  ·
    refine ⟨113023852437955811906984291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75349234958637207937989527 113023852437955811906984291)
    ·
      refine ⟨169535778656933717860476437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113023852437955811906984291 169535778656933717860476437)
      ·
        refine ⟨7946989624543768024709833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 169535778656933717860476437 7946989624543768024709833)
        ·
          refine ⟨5960242218407826018532375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7946989624543768024709833 5960242218407826018532375)
          ·
            refine ⟨8940363327611739027798563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5960242218407826018532375 8940363327611739027798563)
            ·
              refine ⟨13410544991417608541697845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8940363327611739027798563 13410544991417608541697845)
              ·
                refine ⟨1257238592945400800784173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13410544991417608541697845 1257238592945400800784173)
                ·
                  refine ⟨471464472354525300294065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257238592945400800784173 471464472354525300294065)
                  ·
                    rfl

theorem cell21_2065891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 3].length) (baseStart_2065891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065891 prefixEnd_2065891 := by exact prefixLift 2065891
  have htrace : WordTrace (prefixWord ++ tailWord_2065891) baseStart_2065891 baseEnd_2065891 := by
    simpa [prefixWord, tailWord_2065891, baseEnd_2065891] using wordTrace_append hprefix tailTrace_2065891
  have hstable : (prefixWord ++ tailWord_2065891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065891).length < 2 ^ (prefixWord ++ tailWord_2065891).sum := by decide
  have hdescent : baseEnd_2065891 < baseStart_2065891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2065905 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 4]
def baseStart_2065905 : Nat := 118140960795 + 2065905 * 2 ^ 59
def prefixEnd_2065905 : Nat := 4983230072969 + 3 ^ 40 * 2065905 * 2
def baseEnd_2065905 : Nat := 471467667345264387060703

theorem tailTrace_2065905 : CollatzResearch.WordTrace tailWord_2065905 prefixEnd_2065905 471467667345264387060703 := by
  unfold tailWord_2065905
  simp only [CollatzResearch.WordTrace]
  refine ⟨75349745580586488328999169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50233163720390992219332779 75349745580586488328999169)
  ·
    refine ⟨56512309185439866246749377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75349745580586488328999169 56512309185439866246749377)
    ·
      refine ⟨42384231889079899685062033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56512309185439866246749377 42384231889079899685062033)
      ·
        refine ⟨31788173916809924763796525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42384231889079899685062033 31788173916809924763796525)
        ·
          refine ⟨11920565218803721786423697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31788173916809924763796525 11920565218803721786423697)
          ·
            refine ⟨8940423914102791339817773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11920565218803721786423697 8940423914102791339817773)
            ·
              refine ⟨3352658967788546752431665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8940423914102791339817773 3352658967788546752431665)
              ·
                refine ⟨2514494225841410064323749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3352658967788546752431665 2514494225841410064323749)
                ·
                  refine ⟨471467667345264387060703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2514494225841410064323749 471467667345264387060703)
                  ·
                    rfl

theorem cell21_2065905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_2065905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2065905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2065905 prefixEnd_2065905 := by exact prefixLift 2065905
  have htrace : WordTrace (prefixWord ++ tailWord_2065905) baseStart_2065905 baseEnd_2065905 := by
    simpa [prefixWord, tailWord_2065905, baseEnd_2065905] using wordTrace_append hprefix tailTrace_2065905
  have hstable : (prefixWord ++ tailWord_2065905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2065905).length < 2 ^ (prefixWord ++ tailWord_2065905).sum := by decide
  have hdescent : baseEnd_2065905 < baseStart_2065905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2065905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066029 : List Nat := [1, 5, 1, 1, 5, 1, 1, 6]
def baseStart_2066029 : Nat := 118140960795 + 2066029 * 2 ^ 59
def prefixEnd_2066029 : Nat := 4983230072969 + 3 ^ 40 * 2066029 * 2
def baseEnd_2066029 : Nat := 157165321944889242331261

theorem tailTrace_2066029 : CollatzResearch.WordTrace tailWord_2066029 prefixEnd_2066029 157165321944889242331261 := by
  unfold tailWord_2066029
  simp only [CollatzResearch.WordTrace]
  refine ⟨75354268232137257506513141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50236178821424838337675427 75354268232137257506513141)
  ·
    refine ⟨7064462646762867891235607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75354268232137257506513141 7064462646762867891235607)
    ·
      refine ⟨10596693970144301836853411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7064462646762867891235607 10596693970144301836853411)
      ·
        refine ⟨15895040955216452755280117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10596693970144301836853411 15895040955216452755280117)
        ·
          refine ⟨1490160089551542445807511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15895040955216452755280117 1490160089551542445807511)
          ·
            refine ⟨2235240134327313668711267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490160089551542445807511 2235240134327313668711267)
            ·
              refine ⟨3352860201490970503066901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235240134327313668711267 3352860201490970503066901)
              ·
                refine ⟨157165321944889242331261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3352860201490970503066901 157165321944889242331261)
                ·
                  rfl

theorem cell21_2066029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 6].length) (baseStart_2066029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066029 prefixEnd_2066029 := by exact prefixLift 2066029
  have htrace : WordTrace (prefixWord ++ tailWord_2066029) baseStart_2066029 baseEnd_2066029 := by
    simpa [prefixWord, tailWord_2066029, baseEnd_2066029] using wordTrace_append hprefix tailTrace_2066029
  have hstable : (prefixWord ++ tailWord_2066029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066029).length < 2 ^ (prefixWord ++ tailWord_2066029).sum := by decide
  have hdescent : baseEnd_2066029 < baseStart_2066029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066085 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 5]
def baseStart_2066085 : Nat := 118140960795 + 2066085 * 2 ^ 59
def prefixEnd_2066085 : Nat := 4983230072969 + 3 ^ 40 * 2066085 * 2
def baseEnd_2066085 : Nat := 471508745797624074060335

theorem tailTrace_2066085 : CollatzResearch.WordTrace tailWord_2066085 prefixEnd_2066085 471508745797624074060335 := by
  unfold tailWord_2066085
  simp only [CollatzResearch.WordTrace]
  refine ⟨75356310719934379070551709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50237540479956252713701139 75356310719934379070551709)
  ·
    refine ⟨28258616519975392151456891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75356310719934379070551709 28258616519975392151456891)
    ·
      refine ⟨42387924779963088227185337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28258616519975392151456891 42387924779963088227185337)
      ·
        refine ⟨31790943584972316170389003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42387924779963088227185337 31790943584972316170389003)
        ·
          refine ⟨47686415377458474255583505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31790943584972316170389003 47686415377458474255583505)
          ·
            refine ⟨35764811533093855691687629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47686415377458474255583505 35764811533093855691687629)
            ·
              refine ⟨13411804324910195884382861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35764811533093855691687629 13411804324910195884382861)
              ·
                refine ⟨5029426621841323456643573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13411804324910195884382861 5029426621841323456643573)
                ·
                  refine ⟨471508745797624074060335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5029426621841323456643573 471508745797624074060335)
                  ·
                    rfl

theorem cell21_2066085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_2066085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066085 prefixEnd_2066085 := by exact prefixLift 2066085
  have htrace : WordTrace (prefixWord ++ tailWord_2066085) baseStart_2066085 baseEnd_2066085 := by
    simpa [prefixWord, tailWord_2066085, baseEnd_2066085] using wordTrace_append hprefix tailTrace_2066085
  have hstable : (prefixWord ++ tailWord_2066085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066085).length < 2 ^ (prefixWord ++ tailWord_2066085).sum := by decide
  have hdescent : baseEnd_2066085 < baseStart_2066085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066116 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_2066116 : Nat := 118140960795 + 2066116 * 2 ^ 59
def prefixEnd_2066116 : Nat := 4983230072969 + 3 ^ 40 * 2066116 * 2
def baseEnd_2066116 : Nat := 471515820419974909043605

theorem tailTrace_2066116 : CollatzResearch.WordTrace tailWord_2066116 prefixEnd_2066116 471515820419974909043605 := by
  unfold tailWord_2066116
  simp only [CollatzResearch.WordTrace]
  refine ⟨37678720691411035682465101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50238294255214714243286801 37678720691411035682465101)
  ·
    refine ⟨14129520259279138380924413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37678720691411035682465101 14129520259279138380924413)
    ·
      refine ⟨5298570097229676892846655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14129520259279138380924413 5298570097229676892846655)
      ·
        refine ⟨7947855145844515339269983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298570097229676892846655 7947855145844515339269983)
        ·
          refine ⟨11921782718766773008904975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947855145844515339269983 11921782718766773008904975)
          ·
            refine ⟨17882674078150159513357463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11921782718766773008904975 17882674078150159513357463)
            ·
              refine ⟨26824011117225239270036195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17882674078150159513357463 26824011117225239270036195)
              ·
                refine ⟨40236016675837858905054293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26824011117225239270036195 40236016675837858905054293)
                ·
                  refine ⟨471515820419974909043605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40236016675837858905054293 471515820419974909043605)
                  ·
                    rfl

theorem cell21_2066116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_2066116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066116 prefixEnd_2066116 := by exact prefixLift 2066116
  have htrace : WordTrace (prefixWord ++ tailWord_2066116) baseStart_2066116 baseEnd_2066116 := by
    simpa [prefixWord, tailWord_2066116, baseEnd_2066116] using wordTrace_append hprefix tailTrace_2066116
  have hstable : (prefixWord ++ tailWord_2066116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066116).length < 2 ^ (prefixWord ++ tailWord_2066116).sum := by decide
  have hdescent : baseEnd_2066116 < baseStart_2066116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066175 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 8]
def baseStart_2066175 : Nat := 118140960795 + 2066175 * 2 ^ 59
def prefixEnd_2066175 : Nat := 4983230072969 + 3 ^ 40 * 2066175 * 2
def baseEnd_2066175 : Nat := 471529285023803917560151

theorem tailTrace_2066175 : CollatzResearch.WordTrace tailWord_2066175 prefixEnd_2066175 471529285023803917560151 := by
  unfold tailWord_2066175
  simp only [CollatzResearch.WordTrace]
  refine ⟨75359593289608324441327979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50239728859738882960885319 75359593289608324441327979)
  ·
    refine ⟨113039389934412486661991969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75359593289608324441327979 113039389934412486661991969)
    ·
      refine ⟨84779542450809364996493977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113039389934412486661991969 84779542450809364996493977)
      ·
        refine ⟨63584656838107023747370483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84779542450809364996493977 63584656838107023747370483)
        ·
          refine ⟨95376985257160535621055725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63584656838107023747370483 95376985257160535621055725)
          ·
            refine ⟨35766369471435200857895897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95376985257160535621055725 35766369471435200857895897)
            ·
              refine ⟨26824777103576400643421923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35766369471435200857895897 26824777103576400643421923)
              ·
                refine ⟨40237165655364600965132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26824777103576400643421923 40237165655364600965132885)
                ·
                  refine ⟨471529285023803917560151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40237165655364600965132885 471529285023803917560151)
                  ·
                    rfl

theorem cell21_2066175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 8].length) (baseStart_2066175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066175 prefixEnd_2066175 := by exact prefixLift 2066175
  have htrace : WordTrace (prefixWord ++ tailWord_2066175) baseStart_2066175 baseEnd_2066175 := by
    simpa [prefixWord, tailWord_2066175, baseEnd_2066175] using wordTrace_append hprefix tailTrace_2066175
  have hstable : (prefixWord ++ tailWord_2066175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066175).length < 2 ^ (prefixWord ++ tailWord_2066175).sum := by decide
  have hdescent : baseEnd_2066175 < baseStart_2066175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066305 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 3]
def baseStart_2066305 : Nat := 118140960795 + 2066305 * 2 ^ 59
def prefixEnd_2066305 : Nat := 4983230072969 + 3 ^ 40 * 2066305 * 2
def baseEnd_2066305 : Nat := 471558952794952580393219

theorem tailTrace_2066305 : CollatzResearch.WordTrace tailWord_2066305 prefixEnd_2066305 471558952794952580393219 := by
  unfold tailWord_2066305
  simp only [CollatzResearch.WordTrace]
  refine ⟨75364334779137356643560369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50242889852758237762373579 75364334779137356643560369)
  ·
    refine ⟨56523251084353017482670277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75364334779137356643560369 56523251084353017482670277)
    ·
      refine ⟨10598109578316190778000677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56523251084353017482670277 10598109578316190778000677)
      ·
        refine ⟨1987145545934285770875127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10598109578316190778000677 1987145545934285770875127)
        ·
          refine ⟨2980718318901428656312691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987145545934285770875127 2980718318901428656312691)
          ·
            refine ⟨4471077478352142984469037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980718318901428656312691 4471077478352142984469037)
            ·
              refine ⟨1676654054382053619175889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4471077478352142984469037 1676654054382053619175889)
              ·
                refine ⟨1257490540786540214381917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1676654054382053619175889 1257490540786540214381917)
                ·
                  refine ⟨471558952794952580393219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257490540786540214381917 471558952794952580393219)
                  ·
                    rfl

theorem cell21_2066305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_2066305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066305 prefixEnd_2066305 := by exact prefixLift 2066305
  have htrace : WordTrace (prefixWord ++ tailWord_2066305) baseStart_2066305 baseEnd_2066305 := by
    simpa [prefixWord, tailWord_2066305, baseEnd_2066305] using wordTrace_append hprefix tailTrace_2066305
  have hstable : (prefixWord ++ tailWord_2066305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066305).length < 2 ^ (prefixWord ++ tailWord_2066305).sum := by decide
  have hdescent : baseEnd_2066305 < baseStart_2066305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066364 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 3]
def baseStart_2066364 : Nat := 118140960795 + 2066364 * 2 ^ 59
def prefixEnd_2066364 : Nat := 4983230072969 + 3 ^ 40 * 2066364 * 2
def baseEnd_2066364 : Nat := 471572417398781588909765

theorem tailTrace_2066364 : CollatzResearch.WordTrace tailWord_2066364 prefixEnd_2066364 471572417398781588909765 := by
  unfold tailWord_2066364
  simp only [CollatzResearch.WordTrace]
  refine ⟨37683243342961804859979073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50244324457282406479972097 37683243342961804859979073)
  ·
    refine ⟨28262432507221353644984305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37683243342961804859979073 28262432507221353644984305)
    ·
      refine ⟨21196824380416015233738229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28262432507221353644984305 21196824380416015233738229)
      ·
        refine ⟨1987202285664001428162959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21196824380416015233738229 1987202285664001428162959)
        ·
          refine ⟨2980803428496002142244439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987202285664001428162959 2980803428496002142244439)
          ·
            refine ⟨4471205142744003213366659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2980803428496002142244439 4471205142744003213366659)
            ·
              refine ⟨6706807714116004820049989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471205142744003213366659 6706807714116004820049989)
              ·
                refine ⟨1257526446396750903759373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6706807714116004820049989 1257526446396750903759373)
                ·
                  refine ⟨471572417398781588909765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257526446396750903759373 471572417398781588909765)
                  ·
                    rfl

theorem cell21_2066364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 3].length) (baseStart_2066364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066364 prefixEnd_2066364 := by exact prefixLift 2066364
  have htrace : WordTrace (prefixWord ++ tailWord_2066364) baseStart_2066364 baseEnd_2066364 := by
    simpa [prefixWord, tailWord_2066364, baseEnd_2066364] using wordTrace_append hprefix tailTrace_2066364
  have hstable : (prefixWord ++ tailWord_2066364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066364).length < 2 ^ (prefixWord ++ tailWord_2066364).sum := by decide
  have hdescent : baseEnd_2066364 < baseStart_2066364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066389 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_2066389 : Nat := 118140960795 + 2066389 * 2 ^ 59
def prefixEnd_2066389 : Nat := 4983230072969 + 3 ^ 40 * 2066389 * 2
def baseEnd_2066389 : Nat := 471578122739387100993047

theorem tailTrace_2066389 : CollatzResearch.WordTrace tailWord_2066389 prefixEnd_2066389 471578122739387100993047 := by
  unfold tailWord_2066389
  simp only [CollatzResearch.WordTrace]
  refine ⟨75367398510833038989618221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50244932340555359326412147 75367398510833038989618221)
  ·
    refine ⟨28262774441562389621106833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75367398510833038989618221 28262774441562389621106833)
    ·
      refine ⟨21197080831171792215830125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28262774441562389621106833 21197080831171792215830125)
      ·
        refine ⟨7948905311689422080936297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21197080831171792215830125 7948905311689422080936297)
        ·
          refine ⟨5961678983767066560702223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7948905311689422080936297 5961678983767066560702223)
          ·
            refine ⟨8942518475650599841053335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5961678983767066560702223 8942518475650599841053335)
            ·
              refine ⟨13413777713475899761580003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8942518475650599841053335 13413777713475899761580003)
              ·
                refine ⟨20120666570213849642370005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13413777713475899761580003 20120666570213849642370005)
                ·
                  refine ⟨471578122739387100993047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20120666570213849642370005 471578122739387100993047)
                  ·
                    rfl

theorem cell21_2066389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_2066389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066389 prefixEnd_2066389 := by exact prefixLift 2066389
  have htrace : WordTrace (prefixWord ++ tailWord_2066389) baseStart_2066389 baseEnd_2066389 := by
    simpa [prefixWord, tailWord_2066389, baseEnd_2066389] using wordTrace_append hprefix tailTrace_2066389
  have hstable : (prefixWord ++ tailWord_2066389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066389).length < 2 ^ (prefixWord ++ tailWord_2066389).sum := by decide
  have hdescent : baseEnd_2066389 < baseStart_2066389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066437 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 4]
def baseStart_2066437 : Nat := 118140960795 + 2066437 * 2 ^ 59
def prefixEnd_2066437 : Nat := 4983230072969 + 3 ^ 40 * 2066437 * 2
def baseEnd_2066437 : Nat := 471589076993349684192949

theorem tailTrace_2066437 : CollatzResearch.WordTrace tailWord_2066437 prefixEnd_2066437 471589076993349684192949 := by
  unfold tailWord_2066437
  simp only [CollatzResearch.WordTrace]
  refine ⟨75369149214659143187365565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50246099476439428791577043 75369149214659143187365565)
  ·
    refine ⟨28263430955497178695262087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75369149214659143187365565 28263430955497178695262087)
    ·
      refine ⟨42395146433245768042893131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28263430955497178695262087 42395146433245768042893131)
      ·
        refine ⟨63592719649868652064339697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42395146433245768042893131 63592719649868652064339697)
        ·
          refine ⟨47694539737401489048254773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63592719649868652064339697 47694539737401489048254773)
          ·
            refine ⟨4471363100381389598273885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47694539737401489048254773 4471363100381389598273885)
            ·
              refine ⟨1676761162643021099352707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4471363100381389598273885 1676761162643021099352707)
              ·
                refine ⟨2515141743964531649029061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676761162643021099352707 2515141743964531649029061)
                ·
                  refine ⟨471589076993349684192949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515141743964531649029061 471589076993349684192949)
                  ·
                    rfl

theorem cell21_2066437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_2066437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066437 prefixEnd_2066437 := by exact prefixLift 2066437
  have htrace : WordTrace (prefixWord ++ tailWord_2066437) baseStart_2066437 baseEnd_2066437 := by
    simpa [prefixWord, tailWord_2066437, baseEnd_2066437] using wordTrace_append hprefix tailTrace_2066437
  have hstable : (prefixWord ++ tailWord_2066437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066437).length < 2 ^ (prefixWord ++ tailWord_2066437).sum := by decide
  have hdescent : baseEnd_2066437 < baseStart_2066437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066468 : List Nat := [2, 3, 1, 4, 3, 1, 7]
def baseStart_2066468 : Nat := 118140960795 + 2066468 * 2 ^ 59
def prefixEnd_2066468 : Nat := 4983230072969 + 3 ^ 40 * 2066468 * 2
def baseEnd_2066468 : Nat := 52399572401744502130691

theorem tailTrace_2066468 : CollatzResearch.WordTrace tailWord_2066468 prefixEnd_2066468 52399572401744502130691 := by
  unfold tailWord_2066468
  simp only [CollatzResearch.WordTrace]
  refine ⟨37685139938773417740872029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50246853251697890321162705 37685139938773417740872029)
  ·
    refine ⟨14131927477040031652827011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37685139938773417740872029 14131927477040031652827011)
    ·
      refine ⟨21197891215560047479240517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14131927477040031652827011 21197891215560047479240517)
      ·
        refine ⟨3974604602917508902357597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21197891215560047479240517 3974604602917508902357597)
        ·
          refine ⟨1490476726094065838384099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3974604602917508902357597 1490476726094065838384099)
          ·
            refine ⟨2235715089141098757576149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490476726094065838384099 2235715089141098757576149)
            ·
              refine ⟨52399572401744502130691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2235715089141098757576149 52399572401744502130691)
              ·
                rfl

theorem cell21_2066468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 7].length) (baseStart_2066468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066468 prefixEnd_2066468 := by exact prefixLift 2066468
  have htrace : WordTrace (prefixWord ++ tailWord_2066468) baseStart_2066468 baseEnd_2066468 := by
    simpa [prefixWord, tailWord_2066468, baseEnd_2066468] using wordTrace_append hprefix tailTrace_2066468
  have hstable : (prefixWord ++ tailWord_2066468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066468).length < 2 ^ (prefixWord ++ tailWord_2066468).sum := by decide
  have hdescent : baseEnd_2066468 < baseStart_2066468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066482 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_2066482 : Nat := 118140960795 + 2066482 * 2 ^ 59
def prefixEnd_2066482 : Nat := 4983230072969 + 3 ^ 40 * 2066482 * 2
def baseEnd_2066482 : Nat := 471599346606439605942857

theorem tailTrace_2066482 : CollatzResearch.WordTrace tailWord_2066482 prefixEnd_2066482 471599346606439605942857 := by
  unfold tailWord_2066482
  simp only [CollatzResearch.WordTrace]
  refine ⟨18842697624874028968188425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50247193666330743915169133 18842697624874028968188425)
  ·
    refine ⟨14132023218655521726141319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18842697624874028968188425 14132023218655521726141319)
    ·
      refine ⟨21198034827983282589211979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14132023218655521726141319 21198034827983282589211979)
      ·
        refine ⟨31797052241974923883817969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21198034827983282589211979 31797052241974923883817969)
        ·
          refine ⟨23847789181481192912863477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31797052241974923883817969 23847789181481192912863477)
          ·
            refine ⟨2235730235763861835580951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23847789181481192912863477 2235730235763861835580951)
            ·
              refine ⟨3353595353645792753371427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235730235763861835580951 3353595353645792753371427)
              ·
                refine ⟨5030393030468689130057141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3353595353645792753371427 5030393030468689130057141)
                ·
                  refine ⟨471599346606439605942857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5030393030468689130057141 471599346606439605942857)
                  ·
                    rfl

theorem cell21_2066482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_2066482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066482 prefixEnd_2066482 := by exact prefixLift 2066482
  have htrace : WordTrace (prefixWord ++ tailWord_2066482) baseStart_2066482 baseEnd_2066482 := by
    simpa [prefixWord, tailWord_2066482, baseEnd_2066482] using wordTrace_append hprefix tailTrace_2066482
  have hstable : (prefixWord ++ tailWord_2066482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066482).length < 2 ^ (prefixWord ++ tailWord_2066482).sum := by decide
  have hdescent : baseEnd_2066482 < baseStart_2066482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066496 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 4]
def baseStart_2066496 : Nat := 118140960795 + 2066496 * 2 ^ 59
def prefixEnd_2066496 : Nat := 4983230072969 + 3 ^ 40 * 2066496 * 2
def baseEnd_2066496 : Nat := 471602541597178692709495

theorem tailTrace_2066496 : CollatzResearch.WordTrace tailWord_2066496 prefixEnd_2066496 471602541597178692709495 := by
  unfold tailWord_2066496
  simp only [CollatzResearch.WordTrace]
  refine ⟨37685650560722698131881671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50247534080963597509175561 37685650560722698131881671)
  ·
    refine ⟨56528475841084047197822507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37685650560722698131881671 56528475841084047197822507)
    ·
      refine ⟨84792713761626070796733761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56528475841084047197822507 84792713761626070796733761)
      ·
        refine ⟨63594535321219553097550321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84792713761626070796733761 63594535321219553097550321)
        ·
          refine ⟨47695901490914664823162741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63594535321219553097550321 47695901490914664823162741)
          ·
            refine ⟨4471490764773249827171507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47695901490914664823162741 4471490764773249827171507)
            ·
              refine ⟨6707236147159874740757261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4471490764773249827171507 6707236147159874740757261)
              ·
                refine ⟨2515213555184953027783973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707236147159874740757261 2515213555184953027783973)
                ·
                  refine ⟨471602541597178692709495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515213555184953027783973 471602541597178692709495)
                  ·
                    rfl

theorem cell21_2066496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 4].length) (baseStart_2066496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066496 prefixEnd_2066496 := by exact prefixLift 2066496
  have htrace : WordTrace (prefixWord ++ tailWord_2066496) baseStart_2066496 baseEnd_2066496 := by
    simpa [prefixWord, tailWord_2066496, baseEnd_2066496] using wordTrace_append hprefix tailTrace_2066496
  have hstable : (prefixWord ++ tailWord_2066496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066496).length < 2 ^ (prefixWord ++ tailWord_2066496).sum := by decide
  have hdescent : baseEnd_2066496 < baseStart_2066496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066510 : List Nat := [4, 1, 1, 1, 1, 4, 2, 7]
def baseStart_2066510 : Nat := 118140960795 + 2066510 * 2 ^ 59
def prefixEnd_2066510 : Nat := 4983230072969 + 3 ^ 40 * 2066510 * 2
def baseEnd_2066510 : Nat := 157201912195972593158711

theorem tailTrace_2066510 : CollatzResearch.WordTrace tailWord_2066510 prefixEnd_2066510 157201912195972593158711 := by
  unfold tailWord_2066510
  simp only [CollatzResearch.WordTrace]
  refine ⟨9421476467924334581846623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50247874495596451103181989 9421476467924334581846623)
  ·
    refine ⟨14132214701886501872769935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9421476467924334581846623 14132214701886501872769935)
    ·
      refine ⟨21198322052829752809154903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14132214701886501872769935 21198322052829752809154903)
      ·
        refine ⟨31797483079244629213732355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21198322052829752809154903 31797483079244629213732355)
        ·
          refine ⟨47696224618866943820598533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31797483079244629213732355 47696224618866943820598533)
          ·
            refine ⟨8943042116037551966362225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47696224618866943820598533 8943042116037551966362225)
            ·
              refine ⟨6707281587028163974771669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8943042116037551966362225 6707281587028163974771669)
              ·
                refine ⟨157201912195972593158711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6707281587028163974771669 157201912195972593158711)
                ·
                  rfl

theorem cell21_2066510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 7].length) (baseStart_2066510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066510 prefixEnd_2066510 := by exact prefixLift 2066510
  have htrace : WordTrace (prefixWord ++ tailWord_2066510) baseStart_2066510 baseEnd_2066510 := by
    simpa [prefixWord, tailWord_2066510, baseEnd_2066510] using wordTrace_append hprefix tailTrace_2066510
  have hstable : (prefixWord ++ tailWord_2066510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066510).length < 2 ^ (prefixWord ++ tailWord_2066510).sum := by decide
  have hdescent : baseEnd_2066510 < baseStart_2066510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066530 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_2066530 : Nat := 118140960795 + 2066530 * 2 ^ 59
def prefixEnd_2066530 : Nat := 4983230072969 + 3 ^ 40 * 2066530 * 2
def baseEnd_2066530 : Nat := 471610300860402189142759

theorem tailTrace_2066530 : CollatzResearch.WordTrace tailWord_2066530 prefixEnd_2066530 471610300860402189142759 := by
  unfold tailWord_2066530
  simp only [CollatzResearch.WordTrace]
  refine ⟨18843135300830555017625261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50248360802214813380334029 18843135300830555017625261)
  ·
    refine ⟨7066175737811458131609473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18843135300830555017625261 7066175737811458131609473)
    ·
      refine ⟨5299631803358593598707105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7066175737811458131609473 5299631803358593598707105)
      ·
        refine ⟨3974723852518945199030329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5299631803358593598707105 3974723852518945199030329)
        ·
          refine ⟨2981042889389208899272747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3974723852518945199030329 2981042889389208899272747)
          ·
            refine ⟨4471564334083813348909121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981042889389208899272747 4471564334083813348909121)
            ·
              refine ⟨3353673250562860011681841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4471564334083813348909121 3353673250562860011681841)
              ·
                refine ⟨2515254937922145008761381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353673250562860011681841 2515254937922145008761381)
                ·
                  refine ⟨471610300860402189142759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515254937922145008761381 471610300860402189142759)
                  ·
                    rfl

theorem cell21_2066530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_2066530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066530 prefixEnd_2066530 := by exact prefixLift 2066530
  have htrace : WordTrace (prefixWord ++ tailWord_2066530) baseStart_2066530 baseEnd_2066530 := by
    simpa [prefixWord, tailWord_2066530, baseEnd_2066530] using wordTrace_append hprefix tailTrace_2066530
  have hstable : (prefixWord ++ tailWord_2066530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066530).length < 2 ^ (prefixWord ++ tailWord_2066530).sum := by decide
  have hdescent : baseEnd_2066530 < baseStart_2066530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066541 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2066541 : Nat := 118140960795 + 2066541 * 2 ^ 59
def prefixEnd_2066541 : Nat := 4983230072969 + 3 ^ 40 * 2066541 * 2
def baseEnd_2066541 : Nat := 471612811210268614459403

theorem tailTrace_2066541 : CollatzResearch.WordTrace tailWord_2066541 prefixEnd_2066541 471612811210268614459403 := by
  unfold tailWord_2066541
  simp only [CollatzResearch.WordTrace]
  refine ⟨75372942406282368949151477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50248628270854912632767651 75372942406282368949151477)
  ·
    refine ⟨7066213350588972088982951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75372942406282368949151477 7066213350588972088982951)
    ·
      refine ⟨10599320025883458133474427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7066213350588972088982951 10599320025883458133474427)
      ·
        refine ⟨15898980038825187200211641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599320025883458133474427 15898980038825187200211641)
        ·
          refine ⟨11924235029118890400158731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15898980038825187200211641 11924235029118890400158731)
          ·
            refine ⟨17886352543678335600238097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11924235029118890400158731 17886352543678335600238097)
            ·
              refine ⟨13414764407758751700178573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17886352543678335600238097 13414764407758751700178573)
              ·
                refine ⟨5030536652909531887566965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13414764407758751700178573 5030536652909531887566965)
                ·
                  refine ⟨471612811210268614459403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5030536652909531887566965 471612811210268614459403)
                  ·
                    rfl

theorem cell21_2066541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2066541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066541 prefixEnd_2066541 := by exact prefixLift 2066541
  have htrace : WordTrace (prefixWord ++ tailWord_2066541) baseStart_2066541 baseEnd_2066541 := by
    simpa [prefixWord, tailWord_2066541, baseEnd_2066541] using wordTrace_append hprefix tailTrace_2066541
  have hstable : (prefixWord ++ tailWord_2066541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066541).length < 2 ^ (prefixWord ++ tailWord_2066541).sum := by decide
  have hdescent : baseEnd_2066541 < baseStart_2066541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066589 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 4]
def baseStart_2066589 : Nat := 118140960795 + 2066589 * 2 ^ 59
def prefixEnd_2066589 : Nat := 4983230072969 + 3 ^ 40 * 2066589 * 2
def baseEnd_2066589 : Nat := 471623765464231197659305

theorem tailTrace_2066589 : CollatzResearch.WordTrace tailWord_2066589 prefixEnd_2066589 471623765464231197659305 := by
  unfold tailWord_2066589
  simp only [CollatzResearch.WordTrace]
  refine ⟨75374693110108473146898821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50249795406738982097932547 75374693110108473146898821)
  ·
    refine ⟨14132754958145338715043529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75374693110108473146898821 14132754958145338715043529)
    ·
      refine ⟨10599566218609004036282647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14132754958145338715043529 10599566218609004036282647)
      ·
        refine ⟨15899349327913506054423971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10599566218609004036282647 15899349327913506054423971)
        ·
          refine ⟨23849023991870259081635957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15899349327913506054423971 23849023991870259081635957)
          ·
            refine ⟨2235845999237836788903371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23849023991870259081635957 2235845999237836788903371)
            ·
              refine ⟨3353768998856755183355057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2235845999237836788903371 3353768998856755183355057)
              ·
                refine ⟨2515326749142566387516293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3353768998856755183355057 2515326749142566387516293)
                ·
                  refine ⟨471623765464231197659305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515326749142566387516293 471623765464231197659305)
                  ·
                    rfl

theorem cell21_2066589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_2066589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066589 prefixEnd_2066589 := by exact prefixLift 2066589
  have htrace : WordTrace (prefixWord ++ tailWord_2066589) baseStart_2066589 baseEnd_2066589 := by
    simpa [prefixWord, tailWord_2066589, baseEnd_2066589] using wordTrace_append hprefix tailTrace_2066589
  have hstable : (prefixWord ++ tailWord_2066589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066589).length < 2 ^ (prefixWord ++ tailWord_2066589).sum := by decide
  have hdescent : baseEnd_2066589 < baseStart_2066589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066620 : List Nat := [2, 2, 2, 3, 3, 2, 2, 5]
def baseStart_2066620 : Nat := 118140960795 + 2066620 * 2 ^ 59
def prefixEnd_2066620 : Nat := 4983230072969 + 3 ^ 40 * 2066620 * 2
def baseEnd_2066620 : Nat := 157210280028860677547525

theorem tailTrace_2066620 : CollatzResearch.WordTrace tailWord_2066620 prefixEnd_2066620 157210280028860677547525 := by
  unfold tailWord_2066620
  simp only [CollatzResearch.WordTrace]
  refine ⟨37687911886498082720638657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50250549181997443627518209 37687911886498082720638657)
  ·
    refine ⟨28265933914873562040478993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37687911886498082720638657 28265933914873562040478993)
    ·
      refine ⟨21199450436155171530359245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28265933914873562040478993 21199450436155171530359245)
      ·
        refine ⟨7949793913558189323884717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21199450436155171530359245 7949793913558189323884717)
        ·
          refine ⟨2981172717584320996456769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7949793913558189323884717 2981172717584320996456769)
          ·
            refine ⟨2235879538188240747342577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981172717584320996456769 2235879538188240747342577)
            ·
              refine ⟨1676909653641180560506933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2235879538188240747342577 1676909653641180560506933)
              ·
                refine ⟨157210280028860677547525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1676909653641180560506933 157210280028860677547525)
                ·
                  rfl

theorem cell21_2066620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_2066620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066620 prefixEnd_2066620 := by exact prefixLift 2066620
  have htrace : WordTrace (prefixWord ++ tailWord_2066620) baseStart_2066620 baseEnd_2066620 := by
    simpa [prefixWord, tailWord_2066620, baseEnd_2066620] using wordTrace_append hprefix tailTrace_2066620
  have hstable : (prefixWord ++ tailWord_2066620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066620).length < 2 ^ (prefixWord ++ tailWord_2066620).sum := by decide
  have hdescent : baseEnd_2066620 < baseStart_2066620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066724 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 4]
def baseStart_2066724 : Nat := 118140960795 + 2066724 * 2 ^ 59
def prefixEnd_2066724 : Nat := 4983230072969 + 3 ^ 40 * 2066724 * 2
def baseEnd_2066724 : Nat := 471654574303500962909029

theorem tailTrace_2066724 : CollatzResearch.WordTrace tailWord_2066724 prefixEnd_2066724 471654574303500962909029 := by
  unfold tailWord_2066724
  simp only [CollatzResearch.WordTrace]
  refine ⟨37689808482309695601531613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50253077976412927468708817 37689808482309695601531613)
  ·
    refine ⟨14133678180866135850574355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37689808482309695601531613 14133678180866135850574355)
    ·
      refine ⟨21200517271299203775861533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14133678180866135850574355 21200517271299203775861533)
      ·
        refine ⟨7950193976737201415948075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21200517271299203775861533 7950193976737201415948075)
        ·
          refine ⟨11925290965105802123922113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7950193976737201415948075 11925290965105802123922113)
          ·
            refine ⟨8943968223829351592941585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925290965105802123922113 8943968223829351592941585)
            ·
              refine ⟨6707976167872013694706189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8943968223829351592941585 6707976167872013694706189)
              ·
                refine ⟨2515491062952005135514821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6707976167872013694706189 2515491062952005135514821)
                ·
                  refine ⟨471654574303500962909029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515491062952005135514821 471654574303500962909029)
                  ·
                    rfl

theorem cell21_2066724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_2066724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066724 prefixEnd_2066724 := by exact prefixLift 2066724
  have htrace : WordTrace (prefixWord ++ tailWord_2066724) baseStart_2066724 baseEnd_2066724 := by
    simpa [prefixWord, tailWord_2066724, baseEnd_2066724] using wordTrace_append hprefix tailTrace_2066724
  have hstable : (prefixWord ++ tailWord_2066724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066724).length < 2 ^ (prefixWord ++ tailWord_2066724).sum := by decide
  have hdescent : baseEnd_2066724 < baseStart_2066724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066769 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 5]
def baseStart_2066769 : Nat := 118140960795 + 2066769 * 2 ^ 59
def prefixEnd_2066769 : Nat := 4983230072969 + 3 ^ 40 * 2066769 * 2
def baseEnd_2066769 : Nat := 471664843916590884658937

theorem tailTrace_2066769 : CollatzResearch.WordTrace tailWord_2066769 prefixEnd_2066769 471664843916590884658937 := by
  unfold tailWord_2066769
  simp only [CollatzResearch.WordTrace]
  refine ⟨75381258249456363888451361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50254172166304242592300907 75381258249456363888451361)
  ·
    refine ⟨56535943687092272916338521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75381258249456363888451361 56535943687092272916338521)
    ·
      refine ⟨42401957765319204687253891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56535943687092272916338521 42401957765319204687253891)
      ·
        refine ⟨63602936647978807030880837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42401957765319204687253891 63602936647978807030880837)
        ·
          refine ⟨11925550621496026318290157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63602936647978807030880837 11925550621496026318290157)
          ·
            refine ⟨4472081483061009869358809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11925550621496026318290157 4472081483061009869358809)
            ·
              refine ⟨3354061112295757402019107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4472081483061009869358809 3354061112295757402019107)
              ·
                refine ⟨5031091668443636103028661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354061112295757402019107 5031091668443636103028661)
                ·
                  refine ⟨471664843916590884658937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5031091668443636103028661 471664843916590884658937)
                  ·
                    rfl

theorem cell21_2066769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_2066769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066769 prefixEnd_2066769 := by exact prefixLift 2066769
  have htrace : WordTrace (prefixWord ++ tailWord_2066769) baseStart_2066769 baseEnd_2066769 := by
    simpa [prefixWord, tailWord_2066769, baseEnd_2066769] using wordTrace_append hprefix tailTrace_2066769
  have hstable : (prefixWord ++ tailWord_2066769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066769).length < 2 ^ (prefixWord ++ tailWord_2066769).sum := by decide
  have hdescent : baseEnd_2066769 < baseStart_2066769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066783 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 4]
def baseStart_2066783 : Nat := 118140960795 + 2066783 * 2 ^ 59
def prefixEnd_2066783 : Nat := 4983230072969 + 3 ^ 40 * 2066783 * 2
def baseEnd_2066783 : Nat := 471668038907329971425575

theorem tailTrace_2066783 : CollatzResearch.WordTrace tailWord_2066783 prefixEnd_2066783 471668038907329971425575 := by
  unfold tailWord_2066783
  simp only [CollatzResearch.WordTrace]
  refine ⟨75381768871405644279461003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50254512580937096186307335 75381768871405644279461003)
  ·
    refine ⟨113072653307108466419191505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75381768871405644279461003 113072653307108466419191505)
    ·
      refine ⟨84804489980331349814393629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113072653307108466419191505 84804489980331349814393629)
      ·
        refine ⟨31801683742624256180397611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84804489980331349814393629 31801683742624256180397611)
        ·
          refine ⟨47702525613936384270596417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31801683742624256180397611 47702525613936384270596417)
          ·
            refine ⟨35776894210452288202947313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47702525613936384270596417 35776894210452288202947313)
            ·
              refine ⟨26832670657839216152210485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35776894210452288202947313 26832670657839216152210485)
              ·
                refine ⟨2515562874172426514269733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26832670657839216152210485 2515562874172426514269733)
                ·
                  refine ⟨471668038907329971425575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515562874172426514269733 471668038907329971425575)
                  ·
                    rfl

theorem cell21_2066783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 4].length) (baseStart_2066783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066783 prefixEnd_2066783 := by exact prefixLift 2066783
  have htrace : WordTrace (prefixWord ++ tailWord_2066783) baseStart_2066783 baseEnd_2066783 := by
    simpa [prefixWord, tailWord_2066783, baseEnd_2066783] using wordTrace_append hprefix tailTrace_2066783
  have hstable : (prefixWord ++ tailWord_2066783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066783).length < 2 ^ (prefixWord ++ tailWord_2066783).sum := by decide
  have hdescent : baseEnd_2066783 < baseStart_2066783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066873 : List Nat := [1, 2, 1, 4, 3, 10]
def baseStart_2066873 : Nat := 118140960795 + 2066873 * 2 ^ 59
def prefixEnd_2066873 : Nat := 4983230072969 + 3 ^ 40 * 2066873 * 2
def baseEnd_2066873 : Nat := 17469947338278141293533

theorem tailTrace_2066873 : CollatzResearch.WordTrace tailWord_2066873 prefixEnd_2066873 17469947338278141293533 := by
  unfold tailWord_2066873
  simp only [CollatzResearch.WordTrace]
  refine ⟨75385051441079589650237273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50256700960719726433491515 75385051441079589650237273)
  ·
    refine ⟨56538788580809692237677955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75385051441079589650237273 56538788580809692237677955)
    ·
      refine ⟨84808182871214538356516933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56538788580809692237677955 84808182871214538356516933)
      ·
        refine ⟨15901534288352725941846925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84808182871214538356516933 15901534288352725941846925)
        ·
          refine ⟨5963075358132272228192597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15901534288352725941846925 5963075358132272228192597)
          ·
            refine ⟨17469947338278141293533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5963075358132272228192597 17469947338278141293533)
            ·
              rfl

theorem cell21_2066873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 10].length) (baseStart_2066873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066873 prefixEnd_2066873 := by exact prefixLift 2066873
  have htrace : WordTrace (prefixWord ++ tailWord_2066873) baseStart_2066873 baseEnd_2066873 := by
    simpa [prefixWord, tailWord_2066873, baseEnd_2066873] using wordTrace_append hprefix tailTrace_2066873
  have hstable : (prefixWord ++ tailWord_2066873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066873).length < 2 ^ (prefixWord ++ tailWord_2066873).sum := by decide
  have hdescent : baseEnd_2066873 < baseStart_2066873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066876 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 4]
def baseStart_2066876 : Nat := 118140960795 + 2066876 * 2 ^ 59
def prefixEnd_2066876 : Nat := 4983230072969 + 3 ^ 40 * 2066876 * 2
def baseEnd_2066876 : Nat := 471689262774382476375385

theorem tailTrace_2066876 : CollatzResearch.WordTrace tailWord_2066876 prefixEnd_2066876 471689262774382476375385 := by
  unfold tailWord_2066876
  simp only [CollatzResearch.WordTrace]
  refine ⟨37692580430034360581298241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50256773906712480775064321 37692580430034360581298241)
  ·
    refine ⟨28269435322525770435973681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37692580430034360581298241 28269435322525770435973681)
    ·
      refine ⟨21202076491894327826980261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28269435322525770435973681 21202076491894327826980261)
      ·
        refine ⟨3975389342230186467558799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21202076491894327826980261 3975389342230186467558799)
        ·
          refine ⟨5963084013345279701338199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3975389342230186467558799 5963084013345279701338199)
          ·
            refine ⟨8944626020017919552007299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963084013345279701338199 8944626020017919552007299)
            ·
              refine ⟨13416939030026879328010949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8944626020017919552007299 13416939030026879328010949)
              ·
                refine ⟨2515676068130039874002053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13416939030026879328010949 2515676068130039874002053)
                ·
                  refine ⟨471689262774382476375385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2515676068130039874002053 471689262774382476375385)
                  ·
                    rfl

theorem cell21_2066876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_2066876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066876 prefixEnd_2066876 := by exact prefixLift 2066876
  have htrace : WordTrace (prefixWord ++ tailWord_2066876) baseStart_2066876 baseEnd_2066876 := by
    simpa [prefixWord, tailWord_2066876, baseEnd_2066876] using wordTrace_append hprefix tailTrace_2066876
  have hstable : (prefixWord ++ tailWord_2066876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066876).length < 2 ^ (prefixWord ++ tailWord_2066876).sum := by decide
  have hdescent : baseEnd_2066876 < baseStart_2066876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2066989 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 5]
def baseStart_2066989 : Nat := 118140960795 + 2066989 * 2 ^ 59
def prefixEnd_2066989 : Nat := 4983230072969 + 3 ^ 40 * 2066989 * 2
def baseEnd_2066989 : Nat := 471715050913919390991821

theorem tailTrace_2066989 : CollatzResearch.WordTrace tailWord_2066989 prefixEnd_2066989 471715050913919390991821 := by
  unfold tailWord_2066989
  simp only [CollatzResearch.WordTrace]
  refine ⟨75389282308659341461460021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50259521539106227640973347 75389282308659341461460021)
  ·
    refine ⟨7067745216436813262011877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75389282308659341461460021 7067745216436813262011877)
    ·
      refine ⟨1325202228081902486627227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7067745216436813262011877 1325202228081902486627227)
      ·
        refine ⟨1987803342122853729940841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325202228081902486627227 1987803342122853729940841)
        ·
          refine ⟨1490852506592140297455631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1987803342122853729940841 1490852506592140297455631)
          ·
            refine ⟨2236278759888210446183447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490852506592140297455631 2236278759888210446183447)
            ·
              refine ⟨3354418139832315669275171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236278759888210446183447 3354418139832315669275171)
              ·
                refine ⟨5031627209748473503912757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3354418139832315669275171 5031627209748473503912757)
                ·
                  refine ⟨471715050913919390991821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5031627209748473503912757 471715050913919390991821)
                  ·
                    rfl

theorem cell21_2066989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_2066989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2066989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2066989 prefixEnd_2066989 := by exact prefixLift 2066989
  have htrace : WordTrace (prefixWord ++ tailWord_2066989) baseStart_2066989 baseEnd_2066989 := by
    simpa [prefixWord, tailWord_2066989, baseEnd_2066989] using wordTrace_append hprefix tailTrace_2066989
  have hstable : (prefixWord ++ tailWord_2066989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2066989).length < 2 ^ (prefixWord ++ tailWord_2066989).sum := by decide
  have hdescent : baseEnd_2066989 < baseStart_2066989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2066989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067025 : List Nat := [1, 2, 2, 1, 3, 3, 2, 7]
def baseStart_2067025 : Nat := 118140960795 + 2067025 * 2 ^ 59
def prefixEnd_2067025 : Nat := 4983230072969 + 3 ^ 40 * 2067025 * 2
def baseEnd_2067025 : Nat := 157241088868130442797249

theorem tailTrace_2067025 : CollatzResearch.WordTrace tailWord_2067025 prefixEnd_2067025 157241088868130442797249 := by
  unfold tailWord_2067025
  simp only [CollatzResearch.WordTrace]
  refine ⟨75390595336528919609770529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50260396891019279739847019 75390595336528919609770529)
  ·
    refine ⟨56542946502396689707327897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75390595336528919609770529 56542946502396689707327897)
    ·
      refine ⟨42407209876797517280495923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56542946502396689707327897 42407209876797517280495923)
      ·
        refine ⟨63610814815196275920743885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42407209876797517280495923 63610814815196275920743885)
        ·
          refine ⟨23854055555698603470278957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63610814815196275920743885 23854055555698603470278957)
          ·
            refine ⟨8945270833386976301354609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23854055555698603470278957 8945270833386976301354609)
            ·
              refine ⟨6708953125040232226015957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8945270833386976301354609 6708953125040232226015957)
              ·
                refine ⟨157241088868130442797249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6708953125040232226015957 157241088868130442797249)
                ·
                  rfl

theorem cell21_2067025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_2067025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067025 prefixEnd_2067025 := by exact prefixLift 2067025
  have htrace : WordTrace (prefixWord ++ tailWord_2067025) baseStart_2067025 baseEnd_2067025 := by
    simpa [prefixWord, tailWord_2067025, baseEnd_2067025] using wordTrace_append hprefix tailTrace_2067025
  have hstable : (prefixWord ++ tailWord_2067025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067025).length < 2 ^ (prefixWord ++ tailWord_2067025).sum := by decide
  have hdescent : baseEnd_2067025 < baseStart_2067025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067042 : List Nat := [3, 3, 2, 3, 10]
def baseStart_2067042 : Nat := 118140960795 + 2067042 * 2 ^ 59
def prefixEnd_2067042 : Nat := 4983230072969 + 3 ^ 40 * 2067042 * 2
def baseEnd_2067042 : Nat := 5823791928839544155659

theorem tailTrace_2067042 : CollatzResearch.WordTrace tailWord_2067042 prefixEnd_2067042 5823791928839544155659 := by
  unfold tailWord_2067042
  simp only [CollatzResearch.WordTrace]
  refine ⟨18847803844366832878284845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50260810251644887675426253 18847803844366832878284845)
  ·
    refine ⟨7067926441637562329356817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18847803844366832878284845 7067926441637562329356817)
    ·
      refine ⟨5300944831228171747017613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7067926441637562329356817 5300944831228171747017613)
      ·
        refine ⟨1987854311710564405131605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5300944831228171747017613 1987854311710564405131605)
        ·
          refine ⟨5823791928839544155659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1987854311710564405131605 5823791928839544155659)
          ·
            rfl

theorem cell21_2067042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 10].length) (baseStart_2067042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067042 prefixEnd_2067042 := by exact prefixLift 2067042
  have htrace : WordTrace (prefixWord ++ tailWord_2067042) baseStart_2067042 baseEnd_2067042 := by
    simpa [prefixWord, tailWord_2067042, baseEnd_2067042] using wordTrace_append hprefix tailTrace_2067042
  have hstable : (prefixWord ++ tailWord_2067042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067042).length < 2 ^ (prefixWord ++ tailWord_2067042).sum := by decide
  have hdescent : baseEnd_2067042 < baseStart_2067042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067048 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 3]
def baseStart_2067048 : Nat := 118140960795 + 2067048 * 2 ^ 59
def prefixEnd_2067048 : Nat := 4983230072969 + 3 ^ 40 * 2067048 * 2
def baseEnd_2067048 : Nat := 471728515517748399508367

theorem tailTrace_2067048 : CollatzResearch.WordTrace tailWord_2067048 prefixEnd_2067048 471728515517748399508367 := by
  unfold tailWord_2067048
  simp only [CollatzResearch.WordTrace]
  refine ⟨37695717107722797268928899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50260956143630396358571865 37695717107722797268928899)
  ·
    refine ⟨56543575661584195903393349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37695717107722797268928899 56543575661584195903393349)
    ·
      refine ⟨10601920436547036731886253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56543575661584195903393349 10601920436547036731886253)
      ·
        refine ⟨3975720163705138774457345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10601920436547036731886253 3975720163705138774457345)
        ·
          refine ⟨2981790122778854080843009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3975720163705138774457345 2981790122778854080843009)
          ·
            refine ⟨2236342592084140560632257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2981790122778854080843009 2236342592084140560632257)
            ·
              refine ⟨1677256944063105420474193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236342592084140560632257 1677256944063105420474193)
              ·
                refine ⟨1257942708047329065355645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1677256944063105420474193 1257942708047329065355645)
                ·
                  refine ⟨471728515517748399508367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257942708047329065355645 471728515517748399508367)
                  ·
                    rfl

theorem cell21_2067048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 3].length) (baseStart_2067048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067048 prefixEnd_2067048 := by exact prefixLift 2067048
  have htrace : WordTrace (prefixWord ++ tailWord_2067048) baseStart_2067048 baseEnd_2067048 := by
    simpa [prefixWord, tailWord_2067048, baseEnd_2067048] using wordTrace_append hprefix tailTrace_2067048
  have hstable : (prefixWord ++ tailWord_2067048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067048).length < 2 ^ (prefixWord ++ tailWord_2067048).sum := by decide
  have hdescent : baseEnd_2067048 < baseStart_2067048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067090 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 3]
def baseStart_2067090 : Nat := 118140960795 + 2067090 * 2 ^ 59
def prefixEnd_2067090 : Nat := 4983230072969 + 3 ^ 40 * 2067090 * 2
def baseEnd_2067090 : Nat := 471738100489965659808281

theorem tailTrace_2067090 : CollatzResearch.WordTrace tailWord_2067090 prefixEnd_2067090 471738100489965659808281 := by
  unfold tailWord_2067090
  simp only [CollatzResearch.WordTrace]
  refine ⟨18848241520323358927721681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50261977387528957140591149 18848241520323358927721681)
  ·
    refine ⟨14136181140242519195791261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18848241520323358927721681 14136181140242519195791261)
    ·
      refine ⟨5301067927590944698421723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14136181140242519195791261 5301067927590944698421723)
      ·
        refine ⟨7951601891386417047632585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5301067927590944698421723 7951601891386417047632585)
        ·
          refine ⟨5963701418539812785724439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7951601891386417047632585 5963701418539812785724439)
          ·
            refine ⟨8945552127809719178586659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5963701418539812785724439 8945552127809719178586659)
            ·
              refine ⟨13418328191714578767879989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8945552127809719178586659 13418328191714578767879989)
              ·
                refine ⟨1257968267973241759488749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13418328191714578767879989 1257968267973241759488749)
                ·
                  refine ⟨471738100489965659808281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1257968267973241759488749 471738100489965659808281)
                  ·
                    rfl

theorem cell21_2067090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_2067090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067090 prefixEnd_2067090 := by exact prefixLift 2067090
  have htrace : WordTrace (prefixWord ++ tailWord_2067090) baseStart_2067090 baseEnd_2067090 := by
    simpa [prefixWord, tailWord_2067090, baseEnd_2067090] using wordTrace_append hprefix tailTrace_2067090
  have hstable : (prefixWord ++ tailWord_2067090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067090).length < 2 ^ (prefixWord ++ tailWord_2067090).sum := by decide
  have hdescent : baseEnd_2067090 < baseStart_2067090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067132 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 5]
def baseStart_2067132 : Nat := 118140960795 + 2067132 * 2 ^ 59
def prefixEnd_2067132 : Nat := 4983230072969 + 3 ^ 40 * 2067132 * 2
def baseEnd_2067132 : Nat := 471747685462182920108195

theorem tailTrace_2067132 : CollatzResearch.WordTrace tailWord_2067132 prefixEnd_2067132 471747685462182920108195 := by
  unfold tailWord_2067132
  simp only [CollatzResearch.WordTrace]
  refine ⟨37697248973570638441957825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50262998631427517922610433 37697248973570638441957825)
  ·
    refine ⟨28272936730177978831468369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37697248973570638441957825 28272936730177978831468369)
    ·
      refine ⟨21204702547633484123601277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28272936730177978831468369 21204702547633484123601277)
      ·
        refine ⟨7951763455362556546350479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21204702547633484123601277 7951763455362556546350479)
        ·
          refine ⟨11927645183043834819525719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7951763455362556546350479 11927645183043834819525719)
          ·
            refine ⟨17891467774565752229288579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11927645183043834819525719 17891467774565752229288579)
            ·
              refine ⟨26837201661848628343932869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17891467774565752229288579 26837201661848628343932869)
              ·
                refine ⟨5031975311596617814487413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26837201661848628343932869 5031975311596617814487413)
                ·
                  refine ⟨471747685462182920108195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5031975311596617814487413 471747685462182920108195)
                  ·
                    rfl

theorem cell21_2067132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_2067132 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067132 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067132 prefixEnd_2067132 := by exact prefixLift 2067132
  have htrace : WordTrace (prefixWord ++ tailWord_2067132) baseStart_2067132 baseEnd_2067132 := by
    simpa [prefixWord, tailWord_2067132, baseEnd_2067132] using wordTrace_append hprefix tailTrace_2067132
  have hstable : (prefixWord ++ tailWord_2067132).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067132).length < 2 ^ (prefixWord ++ tailWord_2067132).sum := by decide
  have hdescent : baseEnd_2067132 < baseStart_2067132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067191 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 7]
def baseStart_2067191 : Nat := 118140960795 + 2067191 * 2 ^ 59
def prefixEnd_2067191 : Nat := 4983230072969 + 3 ^ 40 * 2067191 * 2
def baseEnd_2067191 : Nat := 471761150066011928624741

theorem tailTrace_2067191 : CollatzResearch.WordTrace tailWord_2067191 prefixEnd_2067191 471761150066011928624741 := by
  unfold tailWord_2067191
  simp only [CollatzResearch.WordTrace]
  refine ⟨75396649853927529960313427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50264433235951686640208951 75396649853927529960313427)
  ·
    refine ⟨113094974780891294940470141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75396649853927529960313427 113094974780891294940470141)
    ·
      refine ⟨42410615542834235602676303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113094974780891294940470141 42410615542834235602676303)
      ·
        refine ⟨63615923314251353404014455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42410615542834235602676303 63615923314251353404014455)
        ·
          refine ⟨95423884971377030106021683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63615923314251353404014455 95423884971377030106021683)
          ·
            refine ⟨143135827457065545159032525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95423884971377030106021683 143135827457065545159032525)
            ·
              refine ⟨53675935296399579434637197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143135827457065545159032525 53675935296399579434637197)
              ·
                refine ⟨20128475736149842287988949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53675935296399579434637197 20128475736149842287988949)
                ·
                  refine ⟨471761150066011928624741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20128475736149842287988949 471761150066011928624741)
                  ·
                    rfl

theorem cell21_2067191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 7].length) (baseStart_2067191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067191 prefixEnd_2067191 := by exact prefixLift 2067191
  have htrace : WordTrace (prefixWord ++ tailWord_2067191) baseStart_2067191 baseEnd_2067191 := by
    simpa [prefixWord, tailWord_2067191, baseEnd_2067191] using wordTrace_append hprefix tailTrace_2067191
  have hstable : (prefixWord ++ tailWord_2067191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067191).length < 2 ^ (prefixWord ++ tailWord_2067191).sum := by decide
  have hdescent : baseEnd_2067191 < baseStart_2067191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067242 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_2067242 : Nat := 118140960795 + 2067242 * 2 ^ 59
def prefixEnd_2067242 : Nat := 4983230072969 + 3 ^ 40 * 2067242 * 2
def baseEnd_2067242 : Nat := 471772788960847173274637

theorem tailTrace_2067242 : CollatzResearch.WordTrace tailWord_2067242 prefixEnd_2067242 471772788960847173274637 := by
  unfold tailWord_2067242
  simp only [CollatzResearch.WordTrace]
  refine ⟨18849627494185691417604995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50265673317828510446946653 18849627494185691417604995)
  ·
    refine ⟨28274441241278537126407493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18849627494185691417604995 28274441241278537126407493)
    ·
      refine ⟨5301457732739725711201405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28274441241278537126407493 5301457732739725711201405)
      ·
        refine ⟨1988046649777397141700527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5301457732739725711201405 1988046649777397141700527)
        ·
          refine ⟨2982069974666095712550791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1988046649777397141700527 2982069974666095712550791)
          ·
            refine ⟨4473104961999143568826187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982069974666095712550791 4473104961999143568826187)
            ·
              refine ⟨6709657442998715353239281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473104961999143568826187 6709657442998715353239281)
              ·
                refine ⟨5032243082249036514929461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6709657442998715353239281 5032243082249036514929461)
                ·
                  refine ⟨471772788960847173274637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032243082249036514929461 471772788960847173274637)
                  ·
                    rfl

theorem cell21_2067242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_2067242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067242 prefixEnd_2067242 := by exact prefixLift 2067242
  have htrace : WordTrace (prefixWord ++ tailWord_2067242) baseStart_2067242 baseEnd_2067242 := by
    simpa [prefixWord, tailWord_2067242, baseEnd_2067242] using wordTrace_append hprefix tailTrace_2067242
  have hstable : (prefixWord ++ tailWord_2067242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067242).length < 2 ^ (prefixWord ++ tailWord_2067242).sum := by decide
  have hdescent : baseEnd_2067242 < baseStart_2067242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067267 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 7]
def baseStart_2067267 : Nat := 118140960795 + 2067267 * 2 ^ 59
def prefixEnd_2067267 : Nat := 4983230072969 + 3 ^ 40 * 2067267 * 2
def baseEnd_2067267 : Nat := 471778494301452685357919

theorem tailTrace_2067267 : CollatzResearch.WordTrace tailWord_2067267 prefixEnd_2067267 471778494301452685357919 := by
  unfold tailWord_2067267
  simp only [CollatzResearch.WordTrace]
  refine ⟨75399421801652194940080055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50266281201101463293386703 75399421801652194940080055)
  ·
    refine ⟨113099132702478292410120083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75399421801652194940080055 113099132702478292410120083)
    ·
      refine ⟨169648699053717438615180125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113099132702478292410120083 169648699053717438615180125)
      ·
        refine ⟨63618262145144039480692547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 169648699053717438615180125 63618262145144039480692547)
        ·
          refine ⟨95427393217716059221038821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63618262145144039480692547 95427393217716059221038821)
          ·
            refine ⟨17892636228321761103944779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95427393217716059221038821 17892636228321761103944779)
            ·
              refine ⟨26838954342482641655917169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17892636228321761103944779 26838954342482641655917169)
              ·
                refine ⟨20129215756861981241937877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26838954342482641655917169 20129215756861981241937877)
                ·
                  refine ⟨471778494301452685357919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20129215756861981241937877 471778494301452685357919)
                  ·
                    rfl

theorem cell21_2067267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 7].length) (baseStart_2067267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067267 prefixEnd_2067267 := by exact prefixLift 2067267
  have htrace : WordTrace (prefixWord ++ tailWord_2067267) baseStart_2067267 baseEnd_2067267 := by
    simpa [prefixWord, tailWord_2067267, baseEnd_2067267] using wordTrace_append hprefix tailTrace_2067267
  have hstable : (prefixWord ++ tailWord_2067267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067267).length < 2 ^ (prefixWord ++ tailWord_2067267).sum := by decide
  have hdescent : baseEnd_2067267 < baseStart_2067267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067388 : List Nat := [2, 2, 2, 15]
def baseStart_2067388 : Nat := 118140960795 + 2067388 * 2 ^ 59
def prefixEnd_2067388 : Nat := 4983230072969 + 3 ^ 40 * 2067388 * 2
def baseEnd_2067388 : Nat := 1941588922427915077535

theorem tailTrace_2067388 : CollatzResearch.WordTrace tailWord_2067388 prefixEnd_2067388 1941588922427915077535 := by
  unfold tailWord_2067388
  simp only [CollatzResearch.WordTrace]
  refine ⟨37701917517106916302617409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50269223356142555070156545 37701917517106916302617409)
  ·
    refine ⟨28276438137830187226963057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37701917517106916302617409 28276438137830187226963057)
    ·
      refine ⟨21207328603372640420222293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28276438137830187226963057 21207328603372640420222293)
      ·
        refine ⟨1941588922427915077535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 21207328603372640420222293 1941588922427915077535)
        ·
          rfl

theorem cell21_2067388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 15].length) (baseStart_2067388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067388 prefixEnd_2067388 := by exact prefixLift 2067388
  have htrace : WordTrace (prefixWord ++ tailWord_2067388) baseStart_2067388 baseEnd_2067388 := by
    simpa [prefixWord, tailWord_2067388, baseEnd_2067388] using wordTrace_append hprefix tailTrace_2067388
  have hstable : (prefixWord ++ tailWord_2067388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067388).length < 2 ^ (prefixWord ++ tailWord_2067388).sum := by decide
  have hdescent : baseEnd_2067388 < baseStart_2067388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067442 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_2067442 : Nat := 118140960795 + 2067442 * 2 ^ 59
def prefixEnd_2067442 : Nat := 4983230072969 + 3 ^ 40 * 2067442 * 2
def baseEnd_2067442 : Nat := 471818431685691269940895

theorem tailTrace_2067442 : CollatzResearch.WordTrace tailWord_2067442 prefixEnd_2067442 471818431685691269940895 := by
  unfold tailWord_2067442
  simp only [CollatzResearch.WordTrace]
  refine ⟨18851451144004549956925145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50270536384012133218467053 18851451144004549956925145)
  ·
    refine ⟨14138588358003412467693859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18851451144004549956925145 14138588358003412467693859)
    ·
      refine ⟨21207882537005118701540789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14138588358003412467693859 21207882537005118701540789)
      ·
        refine ⟨1988238987844229878269449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21207882537005118701540789 1988238987844229878269449)
        ·
          refine ⟨1491179240883172408702087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1988238987844229878269449 1491179240883172408702087)
          ·
            refine ⟨2236768861324758613053131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491179240883172408702087 2236768861324758613053131)
            ·
              refine ⟨3355153291987137919579697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236768861324758613053131 3355153291987137919579697)
              ·
                refine ⟨2516364968990353439684773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3355153291987137919579697 2516364968990353439684773)
                ·
                  refine ⟨471818431685691269940895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516364968990353439684773 471818431685691269940895)
                  ·
                    rfl

theorem cell21_2067442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_2067442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067442 prefixEnd_2067442 := by exact prefixLift 2067442
  have htrace : WordTrace (prefixWord ++ tailWord_2067442) baseStart_2067442 baseEnd_2067442 := by
    simpa [prefixWord, tailWord_2067442, baseEnd_2067442] using wordTrace_append hprefix tailTrace_2067442
  have hstable : (prefixWord ++ tailWord_2067442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067442).length < 2 ^ (prefixWord ++ tailWord_2067442).sum := by decide
  have hdescent : baseEnd_2067442 < baseStart_2067442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067481 : List Nat := [1, 2, 1, 2, 1, 1, 8, 5]
def baseStart_2067481 : Nat := 118140960795 + 2067481 * 2 ^ 59
def prefixEnd_2067481 : Nat := 4983230072969 + 3 ^ 40 * 2067481 * 2
def baseEnd_2067481 : Nat := 157275777339011956263605

theorem tailTrace_2067481 : CollatzResearch.WordTrace tailWord_2067481 prefixEnd_2067481 157275777339011956263605 := by
  unfold tailWord_2067481
  simp only [CollatzResearch.WordTrace]
  refine ⟨75407227022876909488370297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50271484681917939658913531 75407227022876909488370297)
  ·
    refine ⟨56555420267157682116277723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75407227022876909488370297 56555420267157682116277723)
    ·
      refine ⟨84833130400736523174416585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56555420267157682116277723 84833130400736523174416585)
      ·
        refine ⟨63624847800552392380812439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84833130400736523174416585 63624847800552392380812439)
        ·
          refine ⟨95437271700828588571218659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63624847800552392380812439 95437271700828588571218659)
          ·
            refine ⟨143155907551242882856827989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95437271700828588571218659 143155907551242882856827989)
            ·
              refine ⟨1677608291616127533478453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 143155907551242882856827989 1677608291616127533478453)
              ·
                refine ⟨157275777339011956263605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677608291616127533478453 157275777339011956263605)
                ·
                  rfl

theorem cell21_2067481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 5].length) (baseStart_2067481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067481 prefixEnd_2067481 := by exact prefixLift 2067481
  have htrace : WordTrace (prefixWord ++ tailWord_2067481) baseStart_2067481 baseEnd_2067481 := by
    simpa [prefixWord, tailWord_2067481, baseEnd_2067481] using wordTrace_append hprefix tailTrace_2067481
  have hstable : (prefixWord ++ tailWord_2067481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067481).length < 2 ^ (prefixWord ++ tailWord_2067481).sum := by decide
  have hdescent : baseEnd_2067481 < baseStart_2067481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067498 : List Nat := [3, 1, 4, 1, 3, 2, 7]
def baseStart_2067498 : Nat := 118140960795 + 2067498 * 2 ^ 59
def prefixEnd_2067498 : Nat := 4983230072969 + 3 ^ 40 * 2067498 * 2
def baseEnd_2067498 : Nat := 52425690183183068556383

theorem tailTrace_2067498 : CollatzResearch.WordTrace tailWord_2067498 prefixEnd_2067498 52425690183183068556383 := by
  unfold tailWord_2067498
  simp only [CollatzResearch.WordTrace]
  refine ⟨18851961765953830347934787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50271898042543547594492765 18851961765953830347934787)
  ·
    refine ⟨28277942648930745521902181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18851961765953830347934787 28277942648930745521902181)
    ·
      refine ⟨5302114246674514785356659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28277942648930745521902181 5302114246674514785356659)
      ·
        refine ⟨7953171370011772178034989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5302114246674514785356659 7953171370011772178034989)
        ·
          refine ⟨2982439263754414566763121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7953171370011772178034989 2982439263754414566763121)
          ·
            refine ⟨2236829447815810925072341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2982439263754414566763121 2236829447815810925072341)
            ·
              refine ⟨52425690183183068556383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2236829447815810925072341 52425690183183068556383)
              ·
                rfl

theorem cell21_2067498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 7].length) (baseStart_2067498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067498 prefixEnd_2067498 := by exact prefixLift 2067498
  have htrace : WordTrace (prefixWord ++ tailWord_2067498) baseStart_2067498 baseEnd_2067498 := by
    simpa [prefixWord, tailWord_2067498, baseEnd_2067498] using wordTrace_append hprefix tailTrace_2067498
  have hstable : (prefixWord ++ tailWord_2067498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067498).length < 2 ^ (prefixWord ++ tailWord_2067498).sum := by decide
  have hdescent : baseEnd_2067498 < baseStart_2067498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067512 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_2067512 : Nat := 118140960795 + 2067512 * 2 ^ 59
def prefixEnd_2067512 : Nat := 4983230072969 + 3 ^ 40 * 2067512 * 2
def baseEnd_2067512 : Nat := 471834406639386703774085

theorem tailTrace_2067512 : CollatzResearch.WordTrace tailWord_2067512 prefixEnd_2067512 471834406639386703774085 := by
  unfold tailWord_2067512
  simp only [CollatzResearch.WordTrace]
  refine ⟨37704178842882300891374395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50272238457176401188499193 37704178842882300891374395)
  ·
    refine ⟨56556268264323451337061593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37704178842882300891374395 56556268264323451337061593)
    ·
      refine ⟨42417201198242588502796195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56556268264323451337061593 42417201198242588502796195)
      ·
        refine ⟨63625801797363882754194293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42417201198242588502796195 63625801797363882754194293)
        ·
          refine ⟨5964918918502864008205715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63625801797363882754194293 5964918918502864008205715)
          ·
            refine ⟨8947378377754296012308573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5964918918502864008205715 8947378377754296012308573)
            ·
              refine ⟨3355266891657861004615715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8947378377754296012308573 3355266891657861004615715)
              ·
                refine ⟨5032900337486791506923573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3355266891657861004615715 5032900337486791506923573)
                ·
                  refine ⟨471834406639386703774085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5032900337486791506923573 471834406639386703774085)
                  ·
                    rfl

theorem cell21_2067512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_2067512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067512 prefixEnd_2067512 := by exact prefixLift 2067512
  have htrace : WordTrace (prefixWord ++ tailWord_2067512) baseStart_2067512 baseEnd_2067512 := by
    simpa [prefixWord, tailWord_2067512, baseEnd_2067512] using wordTrace_append hprefix tailTrace_2067512
  have hstable : (prefixWord ++ tailWord_2067512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067512).length < 2 ^ (prefixWord ++ tailWord_2067512).sum := by decide
  have hdescent : baseEnd_2067512 < baseStart_2067512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067588 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 5]
def baseStart_2067588 : Nat := 118140960795 + 2067588 * 2 ^ 59
def prefixEnd_2067588 : Nat := 4983230072969 + 3 ^ 40 * 2067588 * 2
def baseEnd_2067588 : Nat := 471851750874827460507263

theorem tailTrace_2067588 : CollatzResearch.WordTrace tailWord_2067588 prefixEnd_2067588 471851750874827460507263 := by
  unfold tailWord_2067588
  simp only [CollatzResearch.WordTrace]
  refine ⟨37705564816744633381257709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50274086422326177841676945 37705564816744633381257709)
  ·
    refine ⟨14139586806279237517971641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37705564816744633381257709 14139586806279237517971641)
    ·
      refine ⟨10604690104709428138478731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14139586806279237517971641 10604690104709428138478731)
      ·
        refine ⟨15907035157064142207718097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10604690104709428138478731 15907035157064142207718097)
        ·
          refine ⟨11930276367798106655788573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15907035157064142207718097 11930276367798106655788573)
          ·
            refine ⟨4473853637924289995920715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11930276367798106655788573 4473853637924289995920715)
            ·
              refine ⟨6710780456886434993881073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4473853637924289995920715 6710780456886434993881073)
              ·
                refine ⟨5033085342664826245410805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710780456886434993881073 5033085342664826245410805)
                ·
                  refine ⟨471851750874827460507263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033085342664826245410805 471851750874827460507263)
                  ·
                    rfl

theorem cell21_2067588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 5].length) (baseStart_2067588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067588 prefixEnd_2067588 := by exact prefixLift 2067588
  have htrace : WordTrace (prefixWord ++ tailWord_2067588) baseStart_2067588 baseEnd_2067588 := by
    simpa [prefixWord, tailWord_2067588, baseEnd_2067588] using wordTrace_append hprefix tailTrace_2067588
  have hstable : (prefixWord ++ tailWord_2067588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067588).length < 2 ^ (prefixWord ++ tailWord_2067588).sum := by decide
  have hdescent : baseEnd_2067588 < baseStart_2067588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067616 : List Nat := [2, 1, 1, 4, 2, 1, 10]
def baseStart_2067616 : Nat := 118140960795 + 2067616 * 2 ^ 59
def prefixEnd_2067616 : Nat := 4983230072969 + 3 ^ 40 * 2067616 * 2
def baseEnd_2067616 : Nat := 52428682317367292671171

theorem tailTrace_2067616 : CollatzResearch.WordTrace tailWord_2067616 prefixEnd_2067616 52428682317367292671171 := by
  unfold tailWord_2067616
  simp only [CollatzResearch.WordTrace]
  refine ⟨37706075438693913772267351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50274767251591885029689801 37706075438693913772267351)
  ·
    refine ⟨56559113158040870658401027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37706075438693913772267351 56559113158040870658401027)
    ·
      refine ⟨84838669737061305987601541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56559113158040870658401027 84838669737061305987601541)
      ·
        refine ⟨15907250575698994872675289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84838669737061305987601541 15907250575698994872675289)
        ·
          refine ⟨11930437931774246154506467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15907250575698994872675289 11930437931774246154506467)
          ·
            refine ⟨17895656897661369231759701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11930437931774246154506467 17895656897661369231759701)
            ·
              refine ⟨52428682317367292671171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17895656897661369231759701 52428682317367292671171)
              ·
                rfl

theorem cell21_2067616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 10].length) (baseStart_2067616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067616 prefixEnd_2067616 := by exact prefixLift 2067616
  have htrace : WordTrace (prefixWord ++ tailWord_2067616) baseStart_2067616 baseEnd_2067616 := by
    simpa [prefixWord, tailWord_2067616, baseEnd_2067616] using wordTrace_append hprefix tailTrace_2067616
  have hstable : (prefixWord ++ tailWord_2067616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067616).length < 2 ^ (prefixWord ++ tailWord_2067616).sum := by decide
  have hdescent : baseEnd_2067616 < baseStart_2067616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067647 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 5]
def baseStart_2067647 : Nat := 118140960795 + 2067647 * 2 ^ 59
def prefixEnd_2067647 : Nat := 4983230072969 + 3 ^ 40 * 2067647 * 2
def baseEnd_2067647 : Nat := 471865215478656469023809

theorem tailTrace_2067647 : CollatzResearch.WordTrace tailWord_2067647 prefixEnd_2067647 471865215478656469023809 := by
  unfold tailWord_2067647
  simp only [CollatzResearch.WordTrace]
  refine ⟨75413281540275519838913195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50275521026850346559275463 75413281540275519838913195)
  ·
    refine ⟨113119922310413279758369793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75413281540275519838913195 113119922310413279758369793)
    ·
      refine ⟨84839941732809959818777345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113119922310413279758369793 84839941732809959818777345)
      ·
        refine ⟨63629956299607469864083009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84839941732809959818777345 63629956299607469864083009)
        ·
          refine ⟨47722467224705602398062257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63629956299607469864083009 47722467224705602398062257)
          ·
            refine ⟨35791850418529201798546693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47722467224705602398062257 35791850418529201798546693)
            ·
              refine ⟨6710971953474225337227505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35791850418529201798546693 6710971953474225337227505)
              ·
                refine ⟨5033228965105669002920629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6710971953474225337227505 5033228965105669002920629)
                ·
                  refine ⟨471865215478656469023809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033228965105669002920629 471865215478656469023809)
                  ·
                    rfl

theorem cell21_2067647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 5].length) (baseStart_2067647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067647 prefixEnd_2067647 := by exact prefixLift 2067647
  have htrace : WordTrace (prefixWord ++ tailWord_2067647) baseStart_2067647 baseEnd_2067647 := by
    simpa [prefixWord, tailWord_2067647, baseEnd_2067647] using wordTrace_append hprefix tailTrace_2067647
  have hstable : (prefixWord ++ tailWord_2067647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067647).length < 2 ^ (prefixWord ++ tailWord_2067647).sum := by decide
  have hdescent : baseEnd_2067647 < baseStart_2067647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067692 : List Nat := [2, 2, 1, 1, 2, 4, 1, 8]
def baseStart_2067692 : Nat := 118140960795 + 2067692 * 2 ^ 59
def prefixEnd_2067692 : Nat := 4983230072969 + 3 ^ 40 * 2067692 * 2
def baseEnd_2067692 : Nat := 157291828363915463591239

theorem tailTrace_2067692 : CollatzResearch.WordTrace tailWord_2067692 prefixEnd_2067692 157291828363915463591239 := by
  unfold tailWord_2067692
  simp only [CollatzResearch.WordTrace]
  refine ⟨37707461412556246262150665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50276615216741661682867553 37707461412556246262150665)
  ·
    refine ⟨28280596059417184696612999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37707461412556246262150665 28280596059417184696612999)
    ·
      refine ⟨42420894089125777044919499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28280596059417184696612999 42420894089125777044919499)
      ·
        refine ⟨63631341133688665567379249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42420894089125777044919499 63631341133688665567379249)
        ·
          refine ⟨47723505850266499175534437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63631341133688665567379249 47723505850266499175534437)
          ·
            refine ⟨8948157346924968595412707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47723505850266499175534437 8948157346924968595412707)
            ·
              refine ⟨13422236020387452893119061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948157346924968595412707 13422236020387452893119061)
              ·
                refine ⟨157291828363915463591239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13422236020387452893119061 157291828363915463591239)
                ·
                  rfl

theorem cell21_2067692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_2067692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067692 prefixEnd_2067692 := by exact prefixLift 2067692
  have htrace : WordTrace (prefixWord ++ tailWord_2067692) baseStart_2067692 baseEnd_2067692 := by
    simpa [prefixWord, tailWord_2067692, baseEnd_2067692] using wordTrace_append hprefix tailTrace_2067692
  have hstable : (prefixWord ++ tailWord_2067692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067692).length < 2 ^ (prefixWord ++ tailWord_2067692).sum := by decide
  have hdescent : baseEnd_2067692 < baseStart_2067692 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067695 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 4]
def baseStart_2067695 : Nat := 118140960795 + 2067695 * 2 ^ 59
def prefixEnd_2067695 : Nat := 4983230072969 + 3 ^ 40 * 2067695 * 2
def baseEnd_2067695 : Nat := 471876169732619052223711

theorem tailTrace_2067695 : CollatzResearch.WordTrace tailWord_2067695 prefixEnd_2067695 471876169732619052223711 := by
  unfold tailWord_2067695
  simp only [CollatzResearch.WordTrace]
  refine ⟨75415032244101624036660539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50276688162734416024440359 75415032244101624036660539)
  ·
    refine ⟨113122548366152436054990809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75415032244101624036660539 113122548366152436054990809)
    ·
      refine ⟨84841911274614327041243107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113122548366152436054990809 84841911274614327041243107)
      ·
        refine ⟨127262866911921490561864661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84841911274614327041243107 127262866911921490561864661)
        ·
          refine ⟨2982723443248159935043703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 127262866911921490561864661 2982723443248159935043703)
          ·
            refine ⟨4474085164872239902565555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2982723443248159935043703 4474085164872239902565555)
            ·
              refine ⟨6711127747308359853848333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474085164872239902565555 6711127747308359853848333)
              ·
                refine ⟨2516672905240634945193125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6711127747308359853848333 2516672905240634945193125)
                ·
                  refine ⟨471876169732619052223711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2516672905240634945193125 471876169732619052223711)
                  ·
                    rfl

theorem cell21_2067695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 4].length) (baseStart_2067695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067695 prefixEnd_2067695 := by exact prefixLift 2067695
  have htrace : WordTrace (prefixWord ++ tailWord_2067695) baseStart_2067695 baseEnd_2067695 := by
    simpa [prefixWord, tailWord_2067695, baseEnd_2067695] using wordTrace_append hprefix tailTrace_2067695
  have hstable : (prefixWord ++ tailWord_2067695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067695).length < 2 ^ (prefixWord ++ tailWord_2067695).sum := by decide
  have hdescent : baseEnd_2067695 < baseStart_2067695 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067757 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 5]
def baseStart_2067757 : Nat := 118140960795 + 2067757 * 2 ^ 59
def prefixEnd_2067757 : Nat := 4983230072969 + 3 ^ 40 * 2067757 * 2
def baseEnd_2067757 : Nat := 471890318977320722190251

theorem tailTrace_2067757 : CollatzResearch.WordTrace tailWord_2067757 prefixEnd_2067757 471890318977320722190251 := by
  unfold tailWord_2067757
  simp only [CollatzResearch.WordTrace]
  refine ⟨75417293569877008625417525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50278195713251339083611683 75417293569877008625417525)
  ·
    refine ⟨7070371272175969558632893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 75417293569877008625417525 7070371272175969558632893)
    ·
      refine ⟨2651389227065988584487335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7070371272175969558632893 2651389227065988584487335)
      ·
        refine ⟨3977083840598982876731003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651389227065988584487335 3977083840598982876731003)
        ·
          refine ⟨5965625760898474315096505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3977083840598982876731003 5965625760898474315096505)
          ·
            refine ⟨4474219320673855736322379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5965625760898474315096505 4474219320673855736322379)
            ·
              refine ⟨6711328981010783604483569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474219320673855736322379 6711328981010783604483569)
              ·
                refine ⟨5033496735758087703362677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6711328981010783604483569 5033496735758087703362677)
                ·
                  refine ⟨471890318977320722190251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033496735758087703362677 471890318977320722190251)
                  ·
                    rfl

theorem cell21_2067757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_2067757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067757 prefixEnd_2067757 := by exact prefixLift 2067757
  have htrace : WordTrace (prefixWord ++ tailWord_2067757) baseStart_2067757 baseEnd_2067757 := by
    simpa [prefixWord, tailWord_2067757, baseEnd_2067757] using wordTrace_append hprefix tailTrace_2067757
  have hstable : (prefixWord ++ tailWord_2067757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067757).length < 2 ^ (prefixWord ++ tailWord_2067757).sum := by decide
  have hdescent : baseEnd_2067757 < baseStart_2067757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067799 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_2067799 : Nat := 118140960795 + 2067799 * 2 ^ 59
def prefixEnd_2067799 : Nat := 4983230072969 + 3 ^ 40 * 2067799 * 2
def baseEnd_2067799 : Nat := 471899903949537982490165

theorem tailTrace_2067799 : CollatzResearch.WordTrace tailWord_2067799 prefixEnd_2067799 471899903949537982490165 := by
  unfold tailWord_2067799
  simp only [CollatzResearch.WordTrace]
  refine ⟨75418825435724849798446451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50279216957149899865630967 75418825435724849798446451)
  ·
    refine ⟨113128238153587274697669677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75418825435724849798446451 113128238153587274697669677)
    ·
      refine ⟨42423089307595228011626129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113128238153587274697669677 42423089307595228011626129)
      ·
        refine ⟨31817316980696421008719597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42423089307595228011626129 31817316980696421008719597)
        ·
          refine ⟨11931493867761157878269849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31817316980696421008719597 11931493867761157878269849)
          ·
            refine ⟨8948620400820868408702387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11931493867761157878269849 8948620400820868408702387)
            ·
              refine ⟨13422930601231302613053581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8948620400820868408702387 13422930601231302613053581)
              ·
                refine ⟨5033598975461738479895093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13422930601231302613053581 5033598975461738479895093)
                ·
                  refine ⟨471899903949537982490165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5033598975461738479895093 471899903949537982490165)
                  ·
                    rfl

theorem cell21_2067799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_2067799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067799 prefixEnd_2067799 := by exact prefixLift 2067799
  have htrace : WordTrace (prefixWord ++ tailWord_2067799) baseStart_2067799 baseEnd_2067799 := by
    simpa [prefixWord, tailWord_2067799, baseEnd_2067799] using wordTrace_append hprefix tailTrace_2067799
  have hstable : (prefixWord ++ tailWord_2067799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067799).length < 2 ^ (prefixWord ++ tailWord_2067799).sum := by decide
  have hdescent : baseEnd_2067799 < baseStart_2067799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067844 : List Nat := [2, 3, 2, 1, 1, 3, 9]
def baseStart_2067844 : Nat := 118140960795 + 2067844 * 2 ^ 59
def prefixEnd_2067844 : Nat := 4983230072969 + 3 ^ 40 * 2067844 * 2
def baseEnd_2067844 : Nat := 52434463729180878248897

theorem tailTrace_2067844 : CollatzResearch.WordTrace tailWord_2067844 prefixEnd_2067844 52434463729180878248897 := by
  unfold tailWord_2067844
  simp only [CollatzResearch.WordTrace]
  refine ⟨37710233360280911241917293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50280311147041214989223057 37710233360280911241917293)
  ·
    refine ⟨14141337510105341715718985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37710233360280911241917293 14141337510105341715718985)
    ·
      refine ⟨10606003132579006286789239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14141337510105341715718985 10606003132579006286789239)
      ·
        refine ⟨15909004698868509430183859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10606003132579006286789239 15909004698868509430183859)
        ·
          refine ⟨23863507048302764145275789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15909004698868509430183859 23863507048302764145275789)
          ·
            refine ⟨8948815143113536554478421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23863507048302764145275789 8948815143113536554478421)
            ·
              refine ⟨52434463729180878248897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8948815143113536554478421 52434463729180878248897)
              ·
                rfl

theorem cell21_2067844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 9].length) (baseStart_2067844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067844 prefixEnd_2067844 := by exact prefixLift 2067844
  have htrace : WordTrace (prefixWord ++ tailWord_2067844) baseStart_2067844 baseEnd_2067844 := by
    simpa [prefixWord, tailWord_2067844, baseEnd_2067844] using wordTrace_append hprefix tailTrace_2067844
  have hstable : (prefixWord ++ tailWord_2067844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067844).length < 2 ^ (prefixWord ++ tailWord_2067844).sum := by decide
  have hdescent : baseEnd_2067844 < baseStart_2067844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067937 : List Nat := [1, 2, 3, 1, 2, 4, 3, 5]
def baseStart_2067937 : Nat := 118140960795 + 2067937 * 2 ^ 59
def prefixEnd_2067937 : Nat := 4983230072969 + 3 ^ 40 * 2067937 * 2
def baseEnd_2067937 : Nat := 157310465809893469729961

theorem tailTrace_2067937 : CollatzResearch.WordTrace tailWord_2067937 prefixEnd_2067937 157310465809893469729961 := by
  unfold tailWord_2067937
  simp only [CollatzResearch.WordTrace]
  refine ⟨75423858709224899366970065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50282572472816599577980043 75423858709224899366970065)
  ·
    refine ⟨56567894031918674525227549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75423858709224899366970065 56567894031918674525227549)
    ·
      refine ⟨21212960261969502946960331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56567894031918674525227549 21212960261969502946960331)
      ·
        refine ⟨31819440392954254420440497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21212960261969502946960331 31819440392954254420440497)
        ·
          refine ⟨23864580294715690815330373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31819440392954254420440497 23864580294715690815330373)
          ·
            refine ⟨4474608805259192027874445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23864580294715690815330373 4474608805259192027874445)
            ·
              refine ⟨1677978301972197010452917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4474608805259192027874445 1677978301972197010452917)
              ·
                refine ⟨157310465809893469729961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1677978301972197010452917 157310465809893469729961)
                ·
                  rfl

theorem cell21_2067937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 5].length) (baseStart_2067937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067937 prefixEnd_2067937 := by exact prefixLift 2067937
  have htrace : WordTrace (prefixWord ++ tailWord_2067937) baseStart_2067937 baseEnd_2067937 := by
    simpa [prefixWord, tailWord_2067937, baseEnd_2067937] using wordTrace_append hprefix tailTrace_2067937
  have hstable : (prefixWord ++ tailWord_2067937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067937).length < 2 ^ (prefixWord ++ tailWord_2067937).sum := by decide
  have hdescent : baseEnd_2067937 < baseStart_2067937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067988 : List Nat := [2, 4, 3, 1, 3, 1, 2, 5]
def baseStart_2067988 : Nat := 118140960795 + 2067988 * 2 ^ 59
def prefixEnd_2067988 : Nat := 4983230072969 + 3 ^ 40 * 2067988 * 2
def baseEnd_2067988 : Nat := 157314345441505217946593

theorem tailTrace_2067988 : CollatzResearch.WordTrace tailWord_2067988 prefixEnd_2067988 157314345441505217946593 := by
  unfold tailWord_2067988
  simp only [CollatzResearch.WordTrace]
  refine ⟨37712859416020067538538309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50283812554693423384717745 37712859416020067538538309)
  ·
    refine ⟨7071161140503762663475933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37712859416020067538538309 7071161140503762663475933)
    ·
      refine ⟨2651685427688910998803475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7071161140503762663475933 2651685427688910998803475)
      ·
        refine ⟨3977528141533366498205213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651685427688910998803475 3977528141533366498205213)
        ·
          refine ⟨1491573053075012436826955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3977528141533366498205213 1491573053075012436826955)
          ·
            refine ⟨2237359579612518655240433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491573053075012436826955 2237359579612518655240433)
            ·
              refine ⟨1678019684709388991430325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237359579612518655240433 1678019684709388991430325)
              ·
                refine ⟨157314345441505217946593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1678019684709388991430325 157314345441505217946593)
                ·
                  rfl

theorem cell21_2067988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_2067988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067988 prefixEnd_2067988 := by exact prefixLift 2067988
  have htrace : WordTrace (prefixWord ++ tailWord_2067988) baseStart_2067988 baseEnd_2067988 := by
    simpa [prefixWord, tailWord_2067988, baseEnd_2067988] using wordTrace_append hprefix tailTrace_2067988
  have hstable : (prefixWord ++ tailWord_2067988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067988).length < 2 ^ (prefixWord ++ tailWord_2067988).sum := by decide
  have hdescent : baseEnd_2067988 < baseStart_2067988 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2067996 : List Nat := [2, 2, 3, 1, 2, 1, 3, 7]
def baseStart_2067996 : Nat := 118140960795 + 2067996 * 2 ^ 59
def prefixEnd_2067996 : Nat := 4983230072969 + 3 ^ 40 * 2067996 * 2
def baseEnd_2067996 : Nat := 157314954011169805902143

theorem tailTrace_2067996 : CollatzResearch.WordTrace tailWord_2067996 prefixEnd_2067996 157314954011169805902143 := by
  unfold tailWord_2067996
  simp only [CollatzResearch.WordTrace]
  refine ⟨37713005308005576221683921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50284007077340768295578561 37713005308005576221683921)
  ·
    refine ⟨28284753981004182166262941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37713005308005576221683921 28284753981004182166262941)
    ·
      refine ⟨10606782742876568312348603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28284753981004182166262941 10606782742876568312348603)
      ·
        refine ⟨15910174114314852468522905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10606782742876568312348603 15910174114314852468522905)
        ·
          refine ⟨11932630585736139351392179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15910174114314852468522905 11932630585736139351392179)
          ·
            refine ⟨17898945878604209027088269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11932630585736139351392179 17898945878604209027088269)
            ·
              refine ⟨6712104704476578385158101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17898945878604209027088269 6712104704476578385158101)
              ·
                refine ⟨157314954011169805902143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6712104704476578385158101 157314954011169805902143)
                ·
                  rfl

theorem cell21_2067996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 7].length) (baseStart_2067996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2067996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2067996 prefixEnd_2067996 := by exact prefixLift 2067996
  have htrace : WordTrace (prefixWord ++ tailWord_2067996) baseStart_2067996 baseEnd_2067996 := by
    simpa [prefixWord, tailWord_2067996, baseEnd_2067996] using wordTrace_append hprefix tailTrace_2067996
  have hstable : (prefixWord ++ tailWord_2067996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2067996).length < 2 ^ (prefixWord ++ tailWord_2067996).sum := by decide
  have hdescent : baseEnd_2067996 < baseStart_2067996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2067996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068072 : List Nat := [2, 1, 4, 3, 1, 10]
def baseStart_2068072 : Nat := 118140960795 + 2068072 * 2 ^ 59
def prefixEnd_2068072 : Nat := 4983230072969 + 3 ^ 40 * 2068072 * 2
def baseEnd_2068072 : Nat := 17480081713664821275541

theorem tailTrace_2068072 : CollatzResearch.WordTrace tailWord_2068072 prefixEnd_2068072 17480081713664821275541 := by
  unfold tailWord_2068072
  simp only [CollatzResearch.WordTrace]
  refine ⟨37714391281867908711567235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50285855042490544948756313 37714391281867908711567235)
  ·
    refine ⟨56571586922801863067350853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37714391281867908711567235 56571586922801863067350853)
    ·
      refine ⟨10607172548025349325128285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56571586922801863067350853 10607172548025349325128285)
      ·
        refine ⟨3977689705509505996923107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10607172548025349325128285 3977689705509505996923107)
        ·
          refine ⟨5966534558264258995384661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3977689705509505996923107 5966534558264258995384661)
          ·
            refine ⟨17480081713664821275541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5966534558264258995384661 17480081713664821275541)
            ·
              rfl

theorem cell21_2068072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 10].length) (baseStart_2068072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068072 prefixEnd_2068072 := by exact prefixLift 2068072
  have htrace : WordTrace (prefixWord ++ tailWord_2068072) baseStart_2068072 baseEnd_2068072 := by
    simpa [prefixWord, tailWord_2068072, baseEnd_2068072] using wordTrace_append hprefix tailTrace_2068072
  have hstable : (prefixWord ++ tailWord_2068072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068072).length < 2 ^ (prefixWord ++ tailWord_2068072).sum := by decide
  have hdescent : baseEnd_2068072 < baseStart_2068072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068103 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 5]
def baseStart_2068103 : Nat := 118140960795 + 2068103 * 2 ^ 59
def prefixEnd_2068103 : Nat := 4983230072969 + 3 ^ 40 * 2068103 * 2
def baseEnd_2068103 : Nat := 471969280891301009422877

theorem tailTrace_2068103 : CollatzResearch.WordTrace tailWord_2068103 prefixEnd_2068103 471969280891301009422877 := by
  unfold tailWord_2068103
  simp only [CollatzResearch.WordTrace]
  refine ⟨75429913226623509717512963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50286608817749006478341975 75429913226623509717512963)
  ·
    refine ⟨113144869839935264576269445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75429913226623509717512963 113144869839935264576269445)
    ·
      refine ⟨21214663094987862108050521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113144869839935264576269445 21214663094987862108050521)
      ·
        refine ⟨15910997321240896581037891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21214663094987862108050521 15910997321240896581037891)
        ·
          refine ⟨23866495981861344871556837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15910997321240896581037891 23866495981861344871556837)
          ·
            refine ⟨4474967996599002163416907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23866495981861344871556837 4474967996599002163416907)
            ·
              refine ⟨6712451994898503245125361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4474967996599002163416907 6712451994898503245125361)
              ·
                refine ⟨5034338996173877433844021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6712451994898503245125361 5034338996173877433844021)
                ·
                  refine ⟨471969280891301009422877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5034338996173877433844021 471969280891301009422877)
                  ·
                    rfl

theorem cell21_2068103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 5].length) (baseStart_2068103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068103 prefixEnd_2068103 := by exact prefixLift 2068103
  have htrace : WordTrace (prefixWord ++ tailWord_2068103) baseStart_2068103 baseEnd_2068103 := by
    simpa [prefixWord, tailWord_2068103, baseEnd_2068103] using wordTrace_append hprefix tailTrace_2068103
  have hstable : (prefixWord ++ tailWord_2068103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068103).length < 2 ^ (prefixWord ++ tailWord_2068103).sum := by decide
  have hdescent : baseEnd_2068103 < baseStart_2068103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068120 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_2068120 : Nat := 118140960795 + 2068120 * 2 ^ 59
def prefixEnd_2068120 : Nat := 4983230072969 + 3 ^ 40 * 2068120 * 2
def baseEnd_2068120 : Nat := 471973160522912757639509

theorem tailTrace_2068120 : CollatzResearch.WordTrace tailWord_2068120 prefixEnd_2068120 471973160522912757639509 := by
  unfold tailWord_2068120
  simp only [CollatzResearch.WordTrace]
  refine ⟨37715266633780960810440907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50287022178374614413921209 37715266633780960810440907)
  ·
    refine ⟨56572899950671441215661361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37715266633780960810440907 56572899950671441215661361)
    ·
      refine ⟨42429674963003580911746021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56572899950671441215661361 42429674963003580911746021)
      ·
        refine ⟨7955564055563171420952379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42429674963003580911746021 7955564055563171420952379)
        ·
          refine ⟨11933346083344757131428569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955564055563171420952379 11933346083344757131428569)
          ·
            refine ⟨8950009562508567848571427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11933346083344757131428569 8950009562508567848571427)
            ·
              refine ⟨13425014343762851772857141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8950009562508567848571427 13425014343762851772857141)
              ·
                refine ⟨1258595094727767353705357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13425014343762851772857141 1258595094727767353705357)
                ·
                  refine ⟨471973160522912757639509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258595094727767353705357 471973160522912757639509)
                  ·
                    rfl

theorem cell21_2068120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_2068120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068120 prefixEnd_2068120 := by exact prefixLift 2068120
  have htrace : WordTrace (prefixWord ++ tailWord_2068120) baseStart_2068120 baseEnd_2068120 := by
    simpa [prefixWord, tailWord_2068120, baseEnd_2068120] using wordTrace_append hprefix tailTrace_2068120
  have hstable : (prefixWord ++ tailWord_2068120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068120).length < 2 ^ (prefixWord ++ tailWord_2068120).sum := by decide
  have hdescent : baseEnd_2068120 < baseStart_2068120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068131 : List Nat := [1, 1, 1, 4, 1, 1, 12]
def baseStart_2068131 : Nat := 118140960795 + 2068131 * 2 ^ 59
def prefixEnd_2068131 : Nat := 4983230072969 + 3 ^ 40 * 2068131 * 2
def baseEnd_2068131 : Nat := 52441741208086575884017

theorem tailTrace_2068131 : CollatzResearch.WordTrace tailWord_2068131 prefixEnd_2068131 52441741208086575884017 := by
  unfold tailWord_2068131
  simp only [CollatzResearch.WordTrace]
  refine ⟨75430934470522070499532247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50287289647014713666354831 75430934470522070499532247)
  ·
    refine ⟨113146401705783105749298371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75430934470522070499532247 113146401705783105749298371)
    ·
      refine ⟨169719602558674658623947557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113146401705783105749298371 169719602558674658623947557)
      ·
        refine ⟨31822425479751498491990167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 169719602558674658623947557 31822425479751498491990167)
        ·
          refine ⟨47733638219627247737985251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31822425479751498491990167 47733638219627247737985251)
          ·
            refine ⟨71600457329440871606977877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47733638219627247737985251 71600457329440871606977877)
            ·
              refine ⟨52441741208086575884017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 71600457329440871606977877 52441741208086575884017)
              ·
                rfl

theorem cell21_2068131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 12].length) (baseStart_2068131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068131 prefixEnd_2068131 := by exact prefixLift 2068131
  have htrace : WordTrace (prefixWord ++ tailWord_2068131) baseStart_2068131 baseEnd_2068131 := by
    simpa [prefixWord, tailWord_2068131, baseEnd_2068131] using wordTrace_append hprefix tailTrace_2068131
  have hstable : (prefixWord ++ tailWord_2068131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068131).length < 2 ^ (prefixWord ++ tailWord_2068131).sum := by decide
  have hdescent : baseEnd_2068131 < baseStart_2068131 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068151 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 4]
def baseStart_2068151 : Nat := 118140960795 + 2068151 * 2 ^ 59
def prefixEnd_2068151 : Nat := 4983230072969 + 3 ^ 40 * 2068151 * 2
def baseEnd_2068151 : Nat := 471980235145263592622779

theorem tailTrace_2068151 : CollatzResearch.WordTrace tailWord_2068151 prefixEnd_2068151 471980235145263592622779 := by
  unfold tailWord_2068151
  simp only [CollatzResearch.WordTrace]
  refine ⟨75431663930449613915260307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50287775953633075943506871 75431663930449613915260307)
  ·
    refine ⟨113147495895674420872890461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75431663930449613915260307 113147495895674420872890461)
    ·
      refine ⟨42430310960877907827333923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113147495895674420872890461 42430310960877907827333923)
      ·
        refine ⟨63645466441316861741000885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42430310960877907827333923 63645466441316861741000885)
        ·
          refine ⟨5966762478873455788218833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63645466441316861741000885 5966762478873455788218833)
          ·
            refine ⟨4475071859155091841164125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5966762478873455788218833 4475071859155091841164125)
            ·
              refine ⟨1678151947183159440436547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4475071859155091841164125 1678151947183159440436547)
              ·
                refine ⟨2517227920774739160654821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678151947183159440436547 2517227920774739160654821)
                ·
                  refine ⟨471980235145263592622779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517227920774739160654821 471980235145263592622779)
                  ·
                    rfl

theorem cell21_2068151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 4].length) (baseStart_2068151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068151 prefixEnd_2068151 := by exact prefixLift 2068151
  have htrace : WordTrace (prefixWord ++ tailWord_2068151) baseStart_2068151 baseEnd_2068151 := by
    simpa [prefixWord, tailWord_2068151, baseEnd_2068151] using wordTrace_append hprefix tailTrace_2068151
  have hstable : (prefixWord ++ tailWord_2068151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068151).length < 2 ^ (prefixWord ++ tailWord_2068151).sum := by decide
  have hdescent : baseEnd_2068151 < baseStart_2068151 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068210 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_2068210 : Nat := 118140960795 + 2068210 * 2 ^ 59
def prefixEnd_2068210 : Nat := 4983230072969 + 3 ^ 40 * 2068210 * 2
def baseEnd_2068210 : Nat := 471993699749092601139325

theorem tailTrace_2068210 : CollatzResearch.WordTrace tailWord_2068210 prefixEnd_2068210 471993699749092601139325 := by
  unfold tailWord_2068210
  simp only [CollatzResearch.WordTrace]
  refine ⟨18858453959308966747914521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50289210558157244661105389 18858453959308966747914521)
  ·
    refine ⟨14143840469481725060935891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18858453959308966747914521 14143840469481725060935891)
    ·
      refine ⟨21215760704222587591403837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14143840469481725060935891 21215760704222587591403837)
      ·
        refine ⟨7955910264083470346776439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21215760704222587591403837 7955910264083470346776439)
        ·
          refine ⟨11933865396125205520164659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7955910264083470346776439 11933865396125205520164659)
          ·
            refine ⟨17900798094187808280246989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11933865396125205520164659 17900798094187808280246989)
            ·
              refine ⟨6712799285320428105092621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17900798094187808280246989 6712799285320428105092621)
              ·
                refine ⟨2517299731995160539409733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6712799285320428105092621 2517299731995160539409733)
                ·
                  refine ⟨471993699749092601139325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517299731995160539409733 471993699749092601139325)
                  ·
                    rfl

theorem cell21_2068210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_2068210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068210 prefixEnd_2068210 := by exact prefixLift 2068210
  have htrace : WordTrace (prefixWord ++ tailWord_2068210) baseStart_2068210 baseEnd_2068210 := by
    simpa [prefixWord, tailWord_2068210, baseEnd_2068210] using wordTrace_append hprefix tailTrace_2068210
  have hstable : (prefixWord ++ tailWord_2068210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068210).length < 2 ^ (prefixWord ++ tailWord_2068210).sum := by decide
  have hdescent : baseEnd_2068210 < baseStart_2068210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068300 : List Nat := [2, 2, 1, 3, 4, 1, 8]
def baseStart_2068300 : Nat := 118140960795 + 2068300 * 2 ^ 59
def prefixEnd_2068300 : Nat := 4983230072969 + 3 ^ 40 * 2068300 * 2
def baseEnd_2068300 : Nat := 52446026552808049404349

theorem tailTrace_2068300 : CollatzResearch.WordTrace tailWord_2068300 prefixEnd_2068300 52446026552808049404349 := by
  unfold tailWord_2068300
  simp only [CollatzResearch.WordTrace]
  refine ⟨37718549203454906181217177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50291398937939874908289569 37718549203454906181217177)
  ·
    refine ⟨28288911902591179635912883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37718549203454906181217177 28288911902591179635912883)
    ·
      refine ⟨42433367853886769453869325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28288911902591179635912883 42433367853886769453869325)
      ·
        refine ⟨15912512945207538545200997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42433367853886769453869325 15912512945207538545200997)
        ·
          refine ⟨2983596177226413477225187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15912512945207538545200997 2983596177226413477225187)
          ·
            refine ⟨4475394265839620215837781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2983596177226413477225187 4475394265839620215837781)
            ·
              refine ⟨52446026552808049404349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4475394265839620215837781 52446026552808049404349)
              ·
                rfl

theorem cell21_2068300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 8].length) (baseStart_2068300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068300 prefixEnd_2068300 := by exact prefixLift 2068300
  have htrace : WordTrace (prefixWord ++ tailWord_2068300) baseStart_2068300 baseEnd_2068300 := by
    simpa [prefixWord, tailWord_2068300, baseEnd_2068300] using wordTrace_append hprefix tailTrace_2068300
  have hstable : (prefixWord ++ tailWord_2068300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068300).length < 2 ^ (prefixWord ++ tailWord_2068300).sum := by decide
  have hdescent : baseEnd_2068300 < baseStart_2068300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068334 : List Nat := [4, 1, 2, 3, 1, 3, 2, 5]
def baseStart_2068334 : Nat := 118140960795 + 2068334 * 2 ^ 59
def prefixEnd_2068334 : Nat := 4983230072969 + 3 ^ 40 * 2068334 * 2
def baseEnd_2068334 : Nat := 157340666079498647024135

theorem tailTrace_2068334 : CollatzResearch.WordTrace tailWord_2068334 prefixEnd_2068334 157340666079498647024135 := by
  unfold tailWord_2068334
  simp only [CollatzResearch.WordTrace]
  refine ⟨9429792311098329521146507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50292225659191090779448037 9429792311098329521146507)
  ·
    refine ⟨14144688466647494281719761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9429792311098329521146507 14144688466647494281719761)
    ·
      refine ⟨10608516349985620711289821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14144688466647494281719761 10608516349985620711289821)
      ·
        refine ⟨3978193631244607766733683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10608516349985620711289821 3978193631244607766733683)
        ·
          refine ⟨5967290446866911650100525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978193631244607766733683 5967290446866911650100525)
          ·
            refine ⟨2237733917575091868787697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5967290446866911650100525 2237733917575091868787697)
            ·
              refine ⟨1678300438181318901590773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2237733917575091868787697 1678300438181318901590773)
              ·
                refine ⟨157340666079498647024135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1678300438181318901590773 157340666079498647024135)
                ·
                  rfl

theorem cell21_2068334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_2068334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068334 prefixEnd_2068334 := by exact prefixLift 2068334
  have htrace : WordTrace (prefixWord ++ tailWord_2068334) baseStart_2068334 baseEnd_2068334 := by
    simpa [prefixWord, tailWord_2068334, baseEnd_2068334] using wordTrace_append hprefix tailTrace_2068334
  have hstable : (prefixWord ++ tailWord_2068334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068334).length < 2 ^ (prefixWord ++ tailWord_2068334).sum := by decide
  have hdescent : baseEnd_2068334 < baseStart_2068334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068407 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 3]
def baseStart_2068407 : Nat := 118140960795 + 2068407 * 2 ^ 59
def prefixEnd_2068407 : Nat := 4983230072969 + 3 ^ 40 * 2068407 * 2
def baseEnd_2068407 : Nat := 472038657833064036355589

theorem tailTrace_2068407 : CollatzResearch.WordTrace tailWord_2068407 prefixEnd_2068407 472038657833064036355589 := by
  unfold tailWord_2068407
  simp only [CollatzResearch.WordTrace]
  refine ⟨75441001017522169636579475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50294000678348113091052983 75441001017522169636579475)
  ·
    refine ⟨113161501526283254454869213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75441001017522169636579475 113161501526283254454869213)
    ·
      refine ⟨42435563072356220420575955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113161501526283254454869213 42435563072356220420575955)
      ·
        refine ⟨63653344608534330630863933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42435563072356220420575955 63653344608534330630863933)
        ·
          refine ⟨23870004228200373986573975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63653344608534330630863933 23870004228200373986573975)
          ·
            refine ⟨35805006342300560979860963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23870004228200373986573975 35805006342300560979860963)
            ·
              refine ⟨53707509513450841469791445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35805006342300560979860963 53707509513450841469791445)
              ·
                refine ⟨1258769754221504096948237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 53707509513450841469791445 1258769754221504096948237)
                ·
                  refine ⟨472038657833064036355589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258769754221504096948237 472038657833064036355589)
                  ·
                    rfl

theorem cell21_2068407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 3].length) (baseStart_2068407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068407 prefixEnd_2068407 := by exact prefixLift 2068407
  have htrace : WordTrace (prefixWord ++ tailWord_2068407) baseStart_2068407 baseEnd_2068407 := by
    simpa [prefixWord, tailWord_2068407, baseEnd_2068407] using wordTrace_append hprefix tailTrace_2068407
  have hstable : (prefixWord ++ tailWord_2068407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068407).length < 2 ^ (prefixWord ++ tailWord_2068407).sum := by decide
  have hdescent : baseEnd_2068407 < baseStart_2068407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068424 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 3]
def baseStart_2068424 : Nat := 118140960795 + 2068424 * 2 ^ 59
def prefixEnd_2068424 : Nat := 4983230072969 + 3 ^ 40 * 2068424 * 2
def baseEnd_2068424 : Nat := 472042537464675784572221

theorem tailTrace_2068424 : CollatzResearch.WordTrace tailWord_2068424 prefixEnd_2068424 472042537464675784572221 := by
  unfold tailWord_2068424
  simp only [CollatzResearch.WordTrace]
  refine ⟨37720810529230290769974163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50294414038973721026632217 37720810529230290769974163)
  ·
    refine ⟨56581215793845436154961245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37720810529230290769974163 56581215793845436154961245)
    ·
      refine ⟨21217955922692038558110467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56581215793845436154961245 21217955922692038558110467)
      ·
        refine ⟨31826933884038057837165701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21217955922692038558110467 31826933884038057837165701)
        ·
          refine ⟨5967550103257135844468569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31826933884038057837165701 5967550103257135844468569)
          ·
            refine ⟨4475662577442851883351427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5967550103257135844468569 4475662577442851883351427)
            ·
              refine ⟨6713493866164277825027141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4475662577442851883351427 6713493866164277825027141)
              ·
                refine ⟨1258780099905802092192589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6713493866164277825027141 1258780099905802092192589)
                ·
                  refine ⟨472042537464675784572221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258780099905802092192589 472042537464675784572221)
                  ·
                    rfl

theorem cell21_2068424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 3].length) (baseStart_2068424 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068424 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068424 prefixEnd_2068424 := by exact prefixLift 2068424
  have htrace : WordTrace (prefixWord ++ tailWord_2068424) baseStart_2068424 baseEnd_2068424 := by
    simpa [prefixWord, tailWord_2068424, baseEnd_2068424] using wordTrace_append hprefix tailTrace_2068424
  have hstable : (prefixWord ++ tailWord_2068424).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068424).length < 2 ^ (prefixWord ++ tailWord_2068424).sum := by decide
  have hdescent : baseEnd_2068424 < baseStart_2068424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068452 : List Nat := [2, 3, 1, 1, 1, 1, 7, 5]
def baseStart_2068452 : Nat := 118140960795 + 2068452 * 2 ^ 59
def prefixEnd_2068452 : Nat := 4983230072969 + 3 ^ 40 * 2068452 * 2
def baseEnd_2068452 : Nat := 157349642482051319368499

theorem tailTrace_2068452 : CollatzResearch.WordTrace tailWord_2068452 prefixEnd_2068452 157349642482051319368499 := by
  unfold tailWord_2068452
  simp only [CollatzResearch.WordTrace]
  refine ⟨37721321151179571160983805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50295094868239428214645073 37721321151179571160983805)
  ·
    refine ⟨14145495431692339185368927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37721321151179571160983805 14145495431692339185368927)
    ·
      refine ⟨21218243147538508778053391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14145495431692339185368927 21218243147538508778053391)
      ·
        refine ⟨31827364721307763167080087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21218243147538508778053391 31827364721307763167080087)
        ·
          refine ⟨47741047081961644750620131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31827364721307763167080087 47741047081961644750620131)
          ·
            refine ⟨71611570622942467125930197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47741047081961644750620131 71611570622942467125930197)
            ·
              refine ⟨1678396186475214073263989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 71611570622942467125930197 1678396186475214073263989)
              ·
                refine ⟨157349642482051319368499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1678396186475214073263989 157349642482051319368499)
                ·
                  rfl

theorem cell21_2068452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 5].length) (baseStart_2068452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068452 prefixEnd_2068452 := by exact prefixLift 2068452
  have htrace : WordTrace (prefixWord ++ tailWord_2068452) baseStart_2068452 baseEnd_2068452 := by
    simpa [prefixWord, tailWord_2068452, baseEnd_2068452] using wordTrace_append hprefix tailTrace_2068452
  have hstable : (prefixWord ++ tailWord_2068452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068452).length < 2 ^ (prefixWord ++ tailWord_2068452).sum := by decide
  have hdescent : baseEnd_2068452 < baseStart_2068452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068511 : List Nat := [1, 1, 2, 4, 1, 2, 3, 7]
def baseStart_2068511 : Nat := 118140960795 + 2068511 * 2 ^ 59
def prefixEnd_2068511 : Nat := 4983230072969 + 3 ^ 40 * 2068511 * 2
def baseEnd_2068511 : Nat := 157354130683327655540681

theorem tailTrace_2068511 : CollatzResearch.WordTrace tailWord_2068511 prefixEnd_2068511 157354130683327655540681 := by
  unfold tailWord_2068511
  simp only [CollatzResearch.WordTrace]
  refine ⟨75444794209145395398365387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50296529472763596932243591 75444794209145395398365387)
  ·
    refine ⟨113167191313718093097548081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75444794209145395398365387 113167191313718093097548081)
    ·
      refine ⟨84875393485288569823161061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113167191313718093097548081 84875393485288569823161061)
      ·
        refine ⟨15914136278491606841842699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 84875393485288569823161061 15914136278491606841842699)
        ·
          refine ⟨23871204417737410262764049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15914136278491606841842699 23871204417737410262764049)
          ·
            refine ⟨17903403313303057697073037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23871204417737410262764049 17903403313303057697073037)
            ·
              refine ⟨6713776242488646636402389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17903403313303057697073037 6713776242488646636402389)
              ·
                refine ⟨157354130683327655540681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6713776242488646636402389 157354130683327655540681)
                ·
                  rfl

theorem cell21_2068511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 7].length) (baseStart_2068511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068511 prefixEnd_2068511 := by exact prefixLift 2068511
  have htrace : WordTrace (prefixWord ++ tailWord_2068511) baseStart_2068511 baseEnd_2068511 := by
    simpa [prefixWord, tailWord_2068511, baseEnd_2068511] using wordTrace_append hprefix tailTrace_2068511
  have hstable : (prefixWord ++ tailWord_2068511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068511).length < 2 ^ (prefixWord ++ tailWord_2068511).sum := by decide
  have hdescent : baseEnd_2068511 < baseStart_2068511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068590 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_2068590 : Nat := 118140960795 + 2068590 * 2 ^ 59
def prefixEnd_2068590 : Nat := 4983230072969 + 3 ^ 40 * 2068590 * 2
def baseEnd_2068590 : Nat := 472080420926296384805215

theorem tailTrace_2068590 : CollatzResearch.WordTrace tailWord_2068590 prefixEnd_2068590 472080420926296384805215 := by
  unfold tailWord_2068590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9430959446982398986311403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50298450383906127926994149 9430959446982398986311403)
  ·
    refine ⟨14146439170473598479467105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9430959446982398986311403 14146439170473598479467105)
    ·
      refine ⟨10609829377855198859600329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14146439170473598479467105 10609829377855198859600329)
      ·
        refine ⟨7957372033391399144700247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10609829377855198859600329 7957372033391399144700247)
        ·
          refine ⟨11936058050087098717050371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957372033391399144700247 11936058050087098717050371)
          ·
            refine ⟨17904087075130648075575557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11936058050087098717050371 17904087075130648075575557)
            ·
              refine ⟨3357016326586996514170417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17904087075130648075575557 3357016326586996514170417)
              ·
                refine ⟨2517762244940247385627813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3357016326586996514170417 2517762244940247385627813)
                ·
                  refine ⟨472080420926296384805215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2517762244940247385627813 472080420926296384805215)
                  ·
                    rfl

theorem cell21_2068590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_2068590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068590 prefixEnd_2068590 := by exact prefixLift 2068590
  have htrace : WordTrace (prefixWord ++ tailWord_2068590) baseStart_2068590 baseEnd_2068590 := by
    simpa [prefixWord, tailWord_2068590, baseEnd_2068590] using wordTrace_append hprefix tailTrace_2068590
  have hstable : (prefixWord ++ tailWord_2068590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068590).length < 2 ^ (prefixWord ++ tailWord_2068590).sum := by decide
  have hdescent : baseEnd_2068590 < baseStart_2068590 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068604 : List Nat := [2, 2, 2, 1, 1, 6, 1, 6]
def baseStart_2068604 : Nat := 118140960795 + 2068604 * 2 ^ 59
def prefixEnd_2068604 : Nat := 4983230072969 + 3 ^ 40 * 2068604 * 2
def baseEnd_2068604 : Nat := 157361205305678490523951

theorem tailTrace_2068604 : CollatzResearch.WordTrace tailWord_2068604 prefixEnd_2068604 157361205305678490523951 := by
  unfold tailWord_2068604
  simp only [CollatzResearch.WordTrace]
  refine ⟨37724093098904236140750433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50298790798538981521000577 37724093098904236140750433)
  ·
    refine ⟨28293069824178177105562825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37724093098904236140750433 28293069824178177105562825)
    ·
      refine ⟨21219802368133632829172119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28293069824178177105562825 21219802368133632829172119)
      ·
        refine ⟨31829703552200449243758179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21219802368133632829172119 31829703552200449243758179)
        ·
          refine ⟨47744555328300673865637269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31829703552200449243758179 47744555328300673865637269)
          ·
            refine ⟨2238026031014094087451747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 47744555328300673865637269 2238026031014094087451747)
            ·
              refine ⟨3357039046521141131177621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238026031014094087451747 3357039046521141131177621)
              ·
                refine ⟨157361205305678490523951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3357039046521141131177621 157361205305678490523951)
                ·
                  rfl

theorem cell21_2068604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 6].length) (baseStart_2068604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068604 prefixEnd_2068604 := by exact prefixLift 2068604
  have htrace : WordTrace (prefixWord ++ tailWord_2068604) baseStart_2068604 baseEnd_2068604 := by
    simpa [prefixWord, tailWord_2068604, baseEnd_2068604] using wordTrace_append hprefix tailTrace_2068604
  have hstable : (prefixWord ++ tailWord_2068604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068604).length < 2 ^ (prefixWord ++ tailWord_2068604).sum := by decide
  have hdescent : baseEnd_2068604 < baseStart_2068604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068618 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_2068618 : Nat := 118140960795 + 2068618 * 2 ^ 59
def prefixEnd_2068618 : Nat := 4983230072969 + 3 ^ 40 * 2068618 * 2
def baseEnd_2068618 : Nat := 472086810907774558338491

theorem tailTrace_2068618 : CollatzResearch.WordTrace tailWord_2068618 prefixEnd_2068618 472086810907774558338491 := by
  unfold tailWord_2068618
  simp only [CollatzResearch.WordTrace]
  refine ⟨18862174204939438168127627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50299131213171835115007005 18862174204939438168127627)
  ·
    refine ⟨28293261307409157252191441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18862174204939438168127627 28293261307409157252191441)
    ·
      refine ⟨21219945980556867939143581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28293261307409157252191441 21219945980556867939143581)
      ·
        refine ⟨7957479742708825477178843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21219945980556867939143581 7957479742708825477178843)
        ·
          refine ⟨11936219614063238215768265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7957479742708825477178843 11936219614063238215768265)
          ·
            refine ⟨8952164710547428661826199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11936219614063238215768265 8952164710547428661826199)
            ·
              refine ⟨13428247065821142992739299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8952164710547428661826199 13428247065821142992739299)
              ·
                refine ⟨20142370598731714489108949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13428247065821142992739299 20142370598731714489108949)
                ·
                  refine ⟨472086810907774558338491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20142370598731714489108949 472086810907774558338491)
                  ·
                    rfl

theorem cell21_2068618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_2068618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068618 prefixEnd_2068618 := by exact prefixLift 2068618
  have htrace : WordTrace (prefixWord ++ tailWord_2068618) baseStart_2068618 baseEnd_2068618 := by
    simpa [prefixWord, tailWord_2068618, baseEnd_2068618] using wordTrace_append hprefix tailTrace_2068618
  have hstable : (prefixWord ++ tailWord_2068618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068618).length < 2 ^ (prefixWord ++ tailWord_2068618).sum := by decide
  have hdescent : baseEnd_2068618 < baseStart_2068618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068711 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 5]
def baseStart_2068711 : Nat := 118140960795 + 2068711 * 2 ^ 59
def prefixEnd_2068711 : Nat := 4983230072969 + 3 ^ 40 * 2068711 * 2
def baseEnd_2068711 : Nat := 472108034774827063288301

theorem tailTrace_2068711 : CollatzResearch.WordTrace tailWord_2068711 prefixEnd_2068711 472108034774827063288301 := by
  unfold tailWord_2068711
  simp only [CollatzResearch.WordTrace]
  refine ⟨75452088808420829555645987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50301392538947219703763991 75452088808420829555645987)
  ·
    refine ⟨113178133212631244333468981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75452088808420829555645987 113178133212631244333468981)
    ·
      refine ⟨10610449988684179156262717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113178133212631244333468981 10610449988684179156262717)
      ·
        refine ⟨3978918745756567183598519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10610449988684179156262717 3978918745756567183598519)
        ·
          refine ⟨5968378118634850775397779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3978918745756567183598519 5968378118634850775397779)
          ·
            refine ⟨8952567177952276163096669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5968378118634850775397779 8952567177952276163096669)
            ·
              refine ⟨3357212691732103561161251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8952567177952276163096669 3357212691732103561161251)
              ·
                refine ⟨5035819037598155341741877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3357212691732103561161251 5035819037598155341741877)
                ·
                  refine ⟨472108034774827063288301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5035819037598155341741877 472108034774827063288301)
                  ·
                    rfl

theorem cell21_2068711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_2068711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068711 prefixEnd_2068711 := by exact prefixLift 2068711
  have htrace : WordTrace (prefixWord ++ tailWord_2068711) baseStart_2068711 baseEnd_2068711 := by
    simpa [prefixWord, tailWord_2068711, baseEnd_2068711] using wordTrace_append hprefix tailTrace_2068711
  have hstable : (prefixWord ++ tailWord_2068711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068711).length < 2 ^ (prefixWord ++ tailWord_2068711).sum := by decide
  have hdescent : baseEnd_2068711 < baseStart_2068711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068762 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_2068762 : Nat := 118140960795 + 2068762 * 2 ^ 59
def prefixEnd_2068762 : Nat := 4983230072969 + 3 ^ 40 * 2068762 * 2
def baseEnd_2068762 : Nat := 472119673669662307938197

theorem tailTrace_2068762 : CollatzResearch.WordTrace tailWord_2068762 prefixEnd_2068762 472119673669662307938197 := by
  unfold tailWord_2068762
  simp only [CollatzResearch.WordTrace]
  refine ⟨18863487232809016316438135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50302632620824043510501693 18863487232809016316438135)
  ·
    refine ⟨28295230849213524474657203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18863487232809016316438135 28295230849213524474657203)
    ·
      refine ⟨42442846273820286711985805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28295230849213524474657203 42442846273820286711985805)
      ·
        refine ⟨15916067352682607516994677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42442846273820286711985805 15916067352682607516994677)
        ·
          refine ⟨1492131314313994454718251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15916067352682607516994677 1492131314313994454718251)
          ·
            refine ⟨2238196971470991682077377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492131314313994454718251 2238196971470991682077377)
            ·
              refine ⟨1678647728603243761558033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238196971470991682077377 1678647728603243761558033)
              ·
                refine ⟨1258985796452432821168525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1678647728603243761558033 1258985796452432821168525)
                ·
                  refine ⟨472119673669662307938197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1258985796452432821168525 472119673669662307938197)
                  ·
                    rfl

theorem cell21_2068762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_2068762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068762 prefixEnd_2068762 := by exact prefixLift 2068762
  have htrace : WordTrace (prefixWord ++ tailWord_2068762) baseStart_2068762 baseEnd_2068762 := by
    simpa [prefixWord, tailWord_2068762, baseEnd_2068762] using wordTrace_append hprefix tailTrace_2068762
  have hstable : (prefixWord ++ tailWord_2068762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068762).length < 2 ^ (prefixWord ++ tailWord_2068762).sum := by decide
  have hdescent : baseEnd_2068762 < baseStart_2068762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068773 : List Nat := [1, 3, 1, 2, 6, 1, 1, 6]
def baseStart_2068773 : Nat := 118140960795 + 2068773 * 2 ^ 59
def prefixEnd_2068773 : Nat := 4983230072969 + 3 ^ 40 * 2068773 * 2
def baseEnd_2068773 : Nat := 157374061339842911084947

theorem tailTrace_2068773 : CollatzResearch.WordTrace tailWord_2068773 prefixEnd_2068773 157374061339842911084947 := by
  unfold tailWord_2068773
  simp only [CollatzResearch.WordTrace]
  refine ⟨75454350134196214144402973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50302900089464142762935315 75454350134196214144402973)
  ·
    refine ⟨28295381300323580304151115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75454350134196214144402973 28295381300323580304151115)
    ·
      refine ⟨42443071950485370456226673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28295381300323580304151115 42443071950485370456226673)
      ·
        refine ⟨31832303962864027842170005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42443071950485370456226673 31832303962864027842170005)
        ·
          refine ⟨1492139248259251305101719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 31832303962864027842170005 1492139248259251305101719)
          ·
            refine ⟨2238208872388876957652579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492139248259251305101719 2238208872388876957652579)
            ·
              refine ⟨3357313308583315436478869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2238208872388876957652579 3357313308583315436478869)
              ·
                refine ⟨157374061339842911084947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3357313308583315436478869 157374061339842911084947)
                ·
                  rfl

theorem cell21_2068773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 6].length) (baseStart_2068773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068773 prefixEnd_2068773 := by exact prefixLift 2068773
  have htrace : WordTrace (prefixWord ++ tailWord_2068773) baseStart_2068773 baseEnd_2068773 := by
    simpa [prefixWord, tailWord_2068773, baseEnd_2068773] using wordTrace_append hprefix tailTrace_2068773
  have hstable : (prefixWord ++ tailWord_2068773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068773).length < 2 ^ (prefixWord ++ tailWord_2068773).sum := by decide
  have hdescent : baseEnd_2068773 < baseStart_2068773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068866 : List Nat := [3, 4, 2, 1, 3, 1, 7]
def baseStart_2068866 : Nat := 118140960795 + 2068866 * 2 ^ 59
def prefixEnd_2068866 : Nat := 4983230072969 + 3 ^ 40 * 2068866 * 2
def baseEnd_2068866 : Nat := 52460378654064582022739

theorem tailTrace_2068866 : CollatzResearch.WordTrace tailWord_2068866 prefixEnd_2068866 52460378654064582022739 := by
  unfold tailWord_2068866
  simp only [CollatzResearch.WordTrace]
  refine ⟨18864435530714822756884613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50305161415239527351692301 18864435530714822756884613)
  ·
    refine ⟨3537081662009029266915865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18864435530714822756884613 3537081662009029266915865)
    ·
      refine ⟨2652811246506771950186899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3537081662009029266915865 2652811246506771950186899)
      ·
        refine ⟨3979216869760157925280349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2652811246506771950186899 3979216869760157925280349)
        ·
          refine ⟨1492206326160059221980131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3979216869760157925280349 1492206326160059221980131)
          ·
            refine ⟨2238309489240088832970197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492206326160059221980131 2238309489240088832970197)
            ·
              refine ⟨52460378654064582022739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2238309489240088832970197 52460378654064582022739)
              ·
                rfl

theorem cell21_2068866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 7].length) (baseStart_2068866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068866 prefixEnd_2068866 := by exact prefixLift 2068866
  have htrace : WordTrace (prefixWord ++ tailWord_2068866) baseStart_2068866 baseEnd_2068866 := by
    simpa [prefixWord, tailWord_2068866, baseEnd_2068866] using wordTrace_append hprefix tailTrace_2068866
  have hstable : (prefixWord ++ tailWord_2068866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068866).length < 2 ^ (prefixWord ++ tailWord_2068866).sum := by decide
  have hdescent : baseEnd_2068866 < baseStart_2068866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068886 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2068886 : Nat := 118140960795 + 2068886 * 2 ^ 59
def prefixEnd_2068886 : Nat := 4983230072969 + 3 ^ 40 * 2068886 * 2
def baseEnd_2068886 : Nat := 472147972159065647871277

theorem tailTrace_2068886 : CollatzResearch.WordTrace tailWord_2068886 prefixEnd_2068886 472147972159065647871277 := by
  unfold tailWord_2068886
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716154473924177152704157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 50305647721857889628844341 4716154473924177152704157)
  ·
    refine ⟨1768557927721566432264059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4716154473924177152704157 1768557927721566432264059)
    ·
      refine ⟨2652836891582349648396089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1768557927721566432264059 2652836891582349648396089)
      ·
        refine ⟨1989627668686762236297067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2652836891582349648396089 1989627668686762236297067)
        ·
          refine ⟨2984441503030143354445601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1989627668686762236297067 2984441503030143354445601)
          ·
            refine ⟨2238331127272607515834201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2984441503030143354445601 2238331127272607515834201)
            ·
              refine ⟨1678748345454455636875651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2238331127272607515834201 1678748345454455636875651)
              ·
                refine ⟨2518122518181683455313477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1678748345454455636875651 2518122518181683455313477)
                ·
                  refine ⟨472147972159065647871277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518122518181683455313477 472147972159065647871277)
                  ·
                    rfl

theorem cell21_2068886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2068886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068886 prefixEnd_2068886 := by exact prefixLift 2068886
  have htrace : WordTrace (prefixWord ++ tailWord_2068886) baseStart_2068886 baseEnd_2068886 := by
    simpa [prefixWord, tailWord_2068886, baseEnd_2068886] using wordTrace_append hprefix tailTrace_2068886
  have hstable : (prefixWord ++ tailWord_2068886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068886).length < 2 ^ (prefixWord ++ tailWord_2068886).sum := by decide
  have hdescent : baseEnd_2068886 < baseStart_2068886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2068905 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 5]
def baseStart_2068905 : Nat := 118140960795 + 2068905 * 2 ^ 59
def prefixEnd_2068905 : Nat := 4983230072969 + 3 ^ 40 * 2068905 * 2
def baseEnd_2068905 : Nat := 472152308217925837054571

theorem tailTrace_2068905 : CollatzResearch.WordTrace tailWord_2068905 prefixEnd_2068905 472152308217925837054571 := by
  unfold tailWord_2068905
  simp only [CollatzResearch.WordTrace]
  refine ⟨75459164569718000688208169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50306109713145333792138779 75459164569718000688208169)
  ·
    refine ⟨56594373427288500516156127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75459164569718000688208169 56594373427288500516156127)
    ·
      refine ⟨84891560140932750774234191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56594373427288500516156127 84891560140932750774234191)
      ·
        refine ⟨127337340211399126161351287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84891560140932750774234191 127337340211399126161351287)
        ·
          refine ⟨191006010317098689242026931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127337340211399126161351287 191006010317098689242026931)
          ·
            refine ⟨286509015475648033863040397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191006010317098689242026931 286509015475648033863040397)
            ·
              refine ⟨107440880803368012698640149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286509015475648033863040397 107440880803368012698640149)
              ·
                refine ⟨5036291287657875595248757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 107440880803368012698640149 5036291287657875595248757)
                ·
                  refine ⟨472152308217925837054571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5036291287657875595248757 472152308217925837054571)
                  ·
                    rfl

theorem cell21_2068905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_2068905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2068905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2068905 prefixEnd_2068905 := by exact prefixLift 2068905
  have htrace : WordTrace (prefixWord ++ tailWord_2068905) baseStart_2068905 baseEnd_2068905 := by
    simpa [prefixWord, tailWord_2068905, baseEnd_2068905] using wordTrace_append hprefix tailTrace_2068905
  have hstable : (prefixWord ++ tailWord_2068905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2068905).length < 2 ^ (prefixWord ++ tailWord_2068905).sum := by decide
  have hdescent : baseEnd_2068905 < baseStart_2068905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2068905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069032 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_2069032 : Nat := 118140960795 + 2069032 * 2 ^ 59
def prefixEnd_2069032 : Nat := 4983230072969 + 3 ^ 40 * 2069032 * 2
def baseEnd_2069032 : Nat := 472181291348201838437645

theorem tailTrace_2069032 : CollatzResearch.WordTrace tailWord_2069032 prefixEnd_2069032 472181291348201838437645 := by
  unfold tailWord_2069032
  simp only [CollatzResearch.WordTrace]
  refine ⟨37731898320128950689040675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50309197760171934252054233 37731898320128950689040675)
  ·
    refine ⟨56597847480193426033561013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37731898320128950689040675 56597847480193426033561013)
    ·
      refine ⟨5306048201268133690646345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 56597847480193426033561013 5306048201268133690646345)
      ·
        refine ⟨3979536150951100267984759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5306048201268133690646345 3979536150951100267984759)
        ·
          refine ⟨5969304226426650401977139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979536150951100267984759 5969304226426650401977139)
          ·
            refine ⟨8953956339639975602965709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5969304226426650401977139 8953956339639975602965709)
            ·
              refine ⟨3357733627364990851112141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8953956339639975602965709 3357733627364990851112141)
              ·
                refine ⟨1259150110261871569167053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3357733627364990851112141 1259150110261871569167053)
                ·
                  refine ⟨472181291348201838437645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259150110261871569167053 472181291348201838437645)
                  ·
                    rfl

theorem cell21_2069032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_2069032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069032 prefixEnd_2069032 := by exact prefixLift 2069032
  have htrace : WordTrace (prefixWord ++ tailWord_2069032) baseStart_2069032 baseEnd_2069032 := by
    simpa [prefixWord, tailWord_2069032, baseEnd_2069032] using wordTrace_append hprefix tailTrace_2069032
  have hstable : (prefixWord ++ tailWord_2069032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069032).length < 2 ^ (prefixWord ++ tailWord_2069032).sum := by decide
  have hdescent : baseEnd_2069032 < baseStart_2069032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069150 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_2069150 : Nat := 118140960795 + 2069150 * 2 ^ 59
def prefixEnd_2069150 : Nat := 4983230072969 + 3 ^ 40 * 2069150 * 2
def baseEnd_2069150 : Nat := 472208220555859855470737

theorem tailTrace_2069150 : CollatzResearch.WordTrace tailWord_2069150 prefixEnd_2069150 472208220555859855470737 := by
  unfold tailWord_2069150
  simp only [CollatzResearch.WordTrace]
  refine ⟨9433512556728800941359613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 50312066969220271687251269 9433512556728800941359613)
  ·
    refine ⟨3537567208773300353009855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9433512556728800941359613 3537567208773300353009855)
    ·
      refine ⟨5306350813159950529514783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3537567208773300353009855 5306350813159950529514783)
      ·
        refine ⟨7959526219739925794272175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306350813159950529514783 7959526219739925794272175)
        ·
          refine ⟨11939289329609888691408263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7959526219739925794272175 11939289329609888691408263)
          ·
            refine ⟨17908933994414833037112395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11939289329609888691408263 17908933994414833037112395)
            ·
              refine ⟨26863400991622249555668593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17908933994414833037112395 26863400991622249555668593)
              ·
                refine ⟨20147550743716687166751445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26863400991622249555668593 20147550743716687166751445)
                ·
                  refine ⟨472208220555859855470737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20147550743716687166751445 472208220555859855470737)
                  ·
                    rfl

theorem cell21_2069150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_2069150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069150 prefixEnd_2069150 := by exact prefixLift 2069150
  have htrace : WordTrace (prefixWord ++ tailWord_2069150) baseStart_2069150 baseEnd_2069150 := by
    simpa [prefixWord, tailWord_2069150, baseEnd_2069150] using wordTrace_append hprefix tailTrace_2069150
  have hstable : (prefixWord ++ tailWord_2069150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069150).length < 2 ^ (prefixWord ++ tailWord_2069150).sum := by decide
  have hdescent : baseEnd_2069150 < baseStart_2069150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069178 : List Nat := [3, 1, 1, 1, 2, 3, 2, 8]
def baseStart_2069178 : Nat := 118140960795 + 2069178 * 2 ^ 59
def prefixEnd_2069178 : Nat := 4983230072969 + 3 ^ 40 * 2069178 * 2
def baseEnd_2069178 : Nat := 157404870179112676334671

theorem tailTrace_2069178 : CollatzResearch.WordTrace tailWord_2069178 prefixEnd_2069178 157404870179112676334671 := by
  unfold tailWord_2069178
  simp only [CollatzResearch.WordTrace]
  refine ⟨18867280424432242078224047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50312747798485978875264125 18867280424432242078224047)
  ·
    refine ⟨28300920636648363117336071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18867280424432242078224047 28300920636648363117336071)
    ·
      refine ⟨42451380954972544676004107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28300920636648363117336071 42451380954972544676004107)
      ·
        refine ⟨63677071432458817014006161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42451380954972544676004107 63677071432458817014006161)
        ·
          refine ⟨47757803574344112760504621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63677071432458817014006161 47757803574344112760504621)
          ·
            refine ⟨17909176340379042285189233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47757803574344112760504621 17909176340379042285189233)
            ·
              refine ⟨13431882255284281713891925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17909176340379042285189233 13431882255284281713891925)
              ·
                refine ⟨157404870179112676334671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13431882255284281713891925 157404870179112676334671)
                ·
                  rfl

theorem cell21_2069178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 8].length) (baseStart_2069178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069178 prefixEnd_2069178 := by exact prefixLift 2069178
  have htrace : WordTrace (prefixWord ++ tailWord_2069178) baseStart_2069178 baseEnd_2069178 := by
    simpa [prefixWord, tailWord_2069178, baseEnd_2069178] using wordTrace_append hprefix tailTrace_2069178
  have hstable : (prefixWord ++ tailWord_2069178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069178).length < 2 ^ (prefixWord ++ tailWord_2069178).sum := by decide
  have hdescent : baseEnd_2069178 < baseStart_2069178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069212 : List Nat := [2, 2, 5, 1, 1, 3, 7]
def baseStart_2069212 : Nat := 118140960795 + 2069212 * 2 ^ 59
def prefixEnd_2069212 : Nat := 4983230072969 + 3 ^ 40 * 2069212 * 2
def baseEnd_2069212 : Nat := 52469152200062391715253

theorem tailTrace_2069212 : CollatzResearch.WordTrace tailWord_2069212 prefixEnd_2069212 52469152200062391715253 := by
  unfold tailWord_2069212
  simp only [CollatzResearch.WordTrace]
  refine ⟨37735180889802896059816945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50313574519737194746422593 37735180889802896059816945)
  ·
    refine ⟨28301385667352172044862709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37735180889802896059816945 28301385667352172044862709)
    ·
      refine ⟨2653254906314266129205879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28301385667352172044862709 2653254906314266129205879)
      ·
        refine ⟨3979882359471399193808819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2653254906314266129205879 3979882359471399193808819)
        ·
          refine ⟨5969823539207098790713229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3979882359471399193808819 5969823539207098790713229)
          ·
            refine ⟨2238683827202662046517461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5969823539207098790713229 2238683827202662046517461)
            ·
              refine ⟨52469152200062391715253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2238683827202662046517461 52469152200062391715253)
              ·
                rfl

theorem cell21_2069212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 7].length) (baseStart_2069212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069212 prefixEnd_2069212 := by exact prefixLift 2069212
  have htrace : WordTrace (prefixWord ++ tailWord_2069212) baseStart_2069212 baseEnd_2069212 := by
    simpa [prefixWord, tailWord_2069212, baseEnd_2069212] using wordTrace_append hprefix tailTrace_2069212
  have hstable : (prefixWord ++ tailWord_2069212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069212).length < 2 ^ (prefixWord ++ tailWord_2069212).sum := by decide
  have hdescent : baseEnd_2069212 < baseStart_2069212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069240 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_2069240 : Nat := 118140960795 + 2069240 * 2 ^ 59
def prefixEnd_2069240 : Nat := 4983230072969 + 3 ^ 40 * 2069240 * 2
def baseEnd_2069240 : Nat := 472228759782039698970553

theorem tailTrace_2069240 : CollatzResearch.WordTrace tailWord_2069240 prefixEnd_2069240 472228759782039698970553 := by
  unfold tailWord_2069240
  simp only [CollatzResearch.WordTrace]
  refine ⟨37735691511752176450826587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50314255349002901934435449 37735691511752176450826587)
  ·
    refine ⟨56603537267628264676239881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37735691511752176450826587 56603537267628264676239881)
    ·
      refine ⟨42452652950721198507179911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56603537267628264676239881 42452652950721198507179911)
      ·
        refine ⟨63678979426081797760769867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42452652950721198507179911 63678979426081797760769867)
        ·
          refine ⟨95518469139122696641154801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63678979426081797760769867 95518469139122696641154801)
          ·
            refine ⟨71638851854342022480866101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95518469139122696641154801 71638851854342022480866101)
            ·
              refine ⟨6716142361344564607581197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71638851854342022480866101 6716142361344564607581197)
              ·
                refine ⟨2518553385504211727842949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6716142361344564607581197 2518553385504211727842949)
                ·
                  refine ⟨472228759782039698970553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518553385504211727842949 472228759782039698970553)
                  ·
                    rfl

theorem cell21_2069240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_2069240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069240 prefixEnd_2069240 := by exact prefixLift 2069240
  have htrace : WordTrace (prefixWord ++ tailWord_2069240) baseStart_2069240 baseEnd_2069240 := by
    simpa [prefixWord, tailWord_2069240, baseEnd_2069240] using wordTrace_append hprefix tailTrace_2069240
  have hstable : (prefixWord ++ tailWord_2069240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069240).length < 2 ^ (prefixWord ++ tailWord_2069240).sum := by decide
  have hdescent : baseEnd_2069240 < baseStart_2069240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069271 : List Nat := [1, 1, 3, 4, 4, 8]
def baseStart_2069271 : Nat := 118140960795 + 2069271 * 2 ^ 59
def prefixEnd_2069271 : Nat := 4983230072969 + 3 ^ 40 * 2069271 * 2
def baseEnd_2069271 : Nat := 17490216089051501257549

theorem tailTrace_2069271 : CollatzResearch.WordTrace tailWord_2069271 prefixEnd_2069271 17490216089051501257549 := by
  unfold tailWord_2069271
  simp only [CollatzResearch.WordTrace]
  refine ⟨75472513686392045196031667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50315009124261363464021111 75472513686392045196031667)
  ·
    refine ⟨113208770529588067794047501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75472513686392045196031667 113208770529588067794047501)
    ·
      refine ⟨42453288948595525422767813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113208770529588067794047501 42453288948595525422767813)
      ·
        refine ⟨7959991677861661016768965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42453288948595525422767813 7959991677861661016768965)
        ·
          refine ⟨1492498439599061440644181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7959991677861661016768965 1492498439599061440644181)
          ·
            refine ⟨17490216089051501257549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1492498439599061440644181 17490216089051501257549)
            ·
              rfl

theorem cell21_2069271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 8].length) (baseStart_2069271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069271 prefixEnd_2069271 := by exact prefixLift 2069271
  have htrace : WordTrace (prefixWord ++ tailWord_2069271) baseStart_2069271 baseEnd_2069271 := by
    simpa [prefixWord, tailWord_2069271, baseEnd_2069271] using wordTrace_append hprefix tailTrace_2069271
  have hstable : (prefixWord ++ tailWord_2069271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069271).length < 2 ^ (prefixWord ++ tailWord_2069271).sum := by decide
  have hdescent : baseEnd_2069271 < baseStart_2069271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069285 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 5]
def baseStart_2069285 : Nat := 118140960795 + 2069285 * 2 ^ 59
def prefixEnd_2069285 : Nat := 4983230072969 + 3 ^ 40 * 2069285 * 2
def baseEnd_2069285 : Nat := 472239029395129620720461

theorem tailTrace_2069285 : CollatzResearch.WordTrace tailWord_2069285 prefixEnd_2069285 472239029395129620720461 := by
  unfold tailWord_2069285
  simp only [CollatzResearch.WordTrace]
  refine ⟨75473024308341325587041309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50315349538894217058027539 75473024308341325587041309)
  ·
    refine ⟨28302384115627997095140491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75473024308341325587041309 28302384115627997095140491)
    ·
      refine ⟨42453576173441995642710737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28302384115627997095140491 42453576173441995642710737)
      ·
        refine ⟨31840182130081496732033053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42453576173441995642710737 31840182130081496732033053)
        ·
          refine ⟨11940068298780561274512395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31840182130081496732033053 11940068298780561274512395)
          ·
            refine ⟨17910102448170841911768593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11940068298780561274512395 17910102448170841911768593)
            ·
              refine ⟨13432576836128131433826445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17910102448170841911768593 13432576836128131433826445)
              ·
                refine ⟨5037216313548049287684917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13432576836128131433826445 5037216313548049287684917)
                ·
                  refine ⟨472239029395129620720461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5037216313548049287684917 472239029395129620720461)
                  ·
                    rfl

theorem cell21_2069285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_2069285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069285 prefixEnd_2069285 := by exact prefixLift 2069285
  have htrace : WordTrace (prefixWord ++ tailWord_2069285) baseStart_2069285 baseEnd_2069285 := by
    simpa [prefixWord, tailWord_2069285, baseEnd_2069285] using wordTrace_append hprefix tailTrace_2069285
  have hstable : (prefixWord ++ tailWord_2069285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069285).length < 2 ^ (prefixWord ++ tailWord_2069285).sum := by decide
  have hdescent : baseEnd_2069285 < baseStart_2069285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069330 : List Nat := [3, 2, 2, 1, 1, 2, 10]
def baseStart_2069330 : Nat := 118140960795 + 2069330 * 2 ^ 59
def prefixEnd_2069330 : Nat := 4983230072969 + 3 ^ 40 * 2069330 * 2
def baseEnd_2069330 : Nat := 52472144334246615830041

theorem tailTrace_2069330 : CollatzResearch.WordTrace tailWord_2069330 prefixEnd_2069330 52472144334246615830041 := by
  unfold tailWord_2069330
  simp only [CollatzResearch.WordTrace]
  refine ⟨18868666398294574568107361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50316443728785532181619629 18868666398294574568107361)
  ·
    refine ⟨14151499798720930926080521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18868666398294574568107361 14151499798720930926080521)
    ·
      refine ⟨10613624849040698194560391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14151499798720930926080521 10613624849040698194560391)
      ·
        refine ⟨15920437273561047291840587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10613624849040698194560391 15920437273561047291840587)
        ·
          refine ⟨23880655910341570937760881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15920437273561047291840587 23880655910341570937760881)
          ·
            refine ⟨17910491932756178203320661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23880655910341570937760881 17910491932756178203320661)
            ·
              refine ⟨52472144334246615830041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17910491932756178203320661 52472144334246615830041)
              ·
                rfl

theorem cell21_2069330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 10].length) (baseStart_2069330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069330 prefixEnd_2069330 := by exact prefixLift 2069330
  have htrace : WordTrace (prefixWord ++ tailWord_2069330) baseStart_2069330 baseEnd_2069330 := by
    simpa [prefixWord, tailWord_2069330, baseEnd_2069330] using wordTrace_append hprefix tailTrace_2069330
  have hstable : (prefixWord ++ tailWord_2069330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069330).length < 2 ^ (prefixWord ++ tailWord_2069330).sum := by decide
  have hdescent : baseEnd_2069330 < baseStart_2069330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069361 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 5]
def baseStart_2069361 : Nat := 118140960795 + 2069361 * 2 ^ 59
def prefixEnd_2069361 : Nat := 4983230072969 + 3 ^ 40 * 2069361 * 2
def baseEnd_2069361 : Nat := 472256373630570377453639

theorem tailTrace_2069361 : CollatzResearch.WordTrace tailWord_2069361 prefixEnd_2069361 472256373630570377453639 := by
  unfold tailWord_2069361
  simp only [CollatzResearch.WordTrace]
  refine ⟨75475796256065990566807937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50317197504043993711205291 75475796256065990566807937)
  ·
    refine ⟨56606847192049492925105953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75475796256065990566807937 56606847192049492925105953)
    ·
      refine ⟨42455135394037119693829465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56606847192049492925105953 42455135394037119693829465)
      ·
        refine ⟨31841351545527839770372099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42455135394037119693829465 31841351545527839770372099)
        ·
          refine ⟨47762027318291759655558149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31841351545527839770372099 47762027318291759655558149)
          ·
            refine ⟨8955380122179704935417153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47762027318291759655558149 8955380122179704935417153)
            ·
              refine ⟨6716535091634778701562865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8955380122179704935417153 6716535091634778701562865)
              ·
                refine ⟨5037401318726084026172149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6716535091634778701562865 5037401318726084026172149)
                ·
                  refine ⟨472256373630570377453639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5037401318726084026172149 472256373630570377453639)
                  ·
                    rfl

theorem cell21_2069361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_2069361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069361 prefixEnd_2069361 := by exact prefixLift 2069361
  have htrace : WordTrace (prefixWord ++ tailWord_2069361) baseStart_2069361 baseEnd_2069361 := by
    simpa [prefixWord, tailWord_2069361, baseEnd_2069361] using wordTrace_append hprefix tailTrace_2069361
  have hstable : (prefixWord ++ tailWord_2069361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069361).length < 2 ^ (prefixWord ++ tailWord_2069361).sum := by decide
  have hdescent : baseEnd_2069361 < baseStart_2069361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069375 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 6]
def baseStart_2069375 : Nat := 118140960795 + 2069375 * 2 ^ 59
def prefixEnd_2069375 : Nat := 4983230072969 + 3 ^ 40 * 2069375 * 2
def baseEnd_2069375 : Nat := 472259568621309464220277

theorem tailTrace_2069375 : CollatzResearch.WordTrace tailWord_2069375 prefixEnd_2069375 472259568621309464220277 := by
  unfold tailWord_2069375
  simp only [CollatzResearch.WordTrace]
  refine ⟨75476306878015270957817579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50317537918676847305211719 75476306878015270957817579)
  ·
    refine ⟨113214460317022906436726369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75476306878015270957817579 113214460317022906436726369)
    ·
      refine ⟨84910845237767179827544777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113214460317022906436726369 84910845237767179827544777)
      ·
        refine ⟨63683133928325384870658583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 84910845237767179827544777 63683133928325384870658583)
        ·
          refine ⟨95524700892488077305987875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63683133928325384870658583 95524700892488077305987875)
          ·
            refine ⟨143287051338732115958981813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95524700892488077305987875 143287051338732115958981813)
            ·
              refine ⟨13433161063006135871154545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 143287051338732115958981813 13433161063006135871154545)
              ·
                refine ⟨10074870797254601903365909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13433161063006135871154545 10074870797254601903365909)
                ·
                  refine ⟨472259568621309464220277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10074870797254601903365909 472259568621309464220277)
                  ·
                    rfl

theorem cell21_2069375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 6].length) (baseStart_2069375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069375 prefixEnd_2069375 := by exact prefixLift 2069375
  have htrace : WordTrace (prefixWord ++ tailWord_2069375) baseStart_2069375 baseEnd_2069375 := by
    simpa [prefixWord, tailWord_2069375, baseEnd_2069375] using wordTrace_append hprefix tailTrace_2069375
  have hstable : (prefixWord ++ tailWord_2069375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069375).length < 2 ^ (prefixWord ++ tailWord_2069375).sum := by decide
  have hdescent : baseEnd_2069375 < baseStart_2069375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069409 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 4]
def baseStart_2069409 : Nat := 118140960795 + 2069409 * 2 ^ 59
def prefixEnd_2069409 : Nat := 4983230072969 + 3 ^ 40 * 2069409 * 2
def baseEnd_2069409 : Nat := 472267327884532960653541

theorem tailTrace_2069409 : CollatzResearch.WordTrace tailWord_2069409 prefixEnd_2069409 472267327884532960653541 := by
  unfold tailWord_2069409
  simp only [CollatzResearch.WordTrace]
  refine ⟨75477546959892094764555281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50318364639928063176370187 75477546959892094764555281)
  ·
    refine ⟨56608160219919071073416461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75477546959892094764555281 56608160219919071073416461)
    ·
      refine ⟨21228060082469651652531173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56608160219919071073416461 21228060082469651652531173)
      ·
        refine ⟨3980261265463059684849595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21228060082469651652531173 3980261265463059684849595)
        ·
          refine ⟨5970391898194589527274393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980261265463059684849595 5970391898194589527274393)
          ·
            refine ⟨4477793923645942145455795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5970391898194589527274393 4477793923645942145455795)
            ·
              refine ⟨6716690885468913218183693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4477793923645942145455795 6716690885468913218183693)
              ·
                refine ⟨2518759082050842456818885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6716690885468913218183693 2518759082050842456818885)
                ·
                  refine ⟨472267327884532960653541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2518759082050842456818885 472267327884532960653541)
                  ·
                    rfl

theorem cell21_2069409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_2069409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069409 prefixEnd_2069409 := by exact prefixLift 2069409
  have htrace : WordTrace (prefixWord ++ tailWord_2069409) baseStart_2069409 baseEnd_2069409 := by
    simpa [prefixWord, tailWord_2069409, baseEnd_2069409] using wordTrace_append hprefix tailTrace_2069409
  have hstable : (prefixWord ++ tailWord_2069409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069409).length < 2 ^ (prefixWord ++ tailWord_2069409).sum := by decide
  have hdescent : baseEnd_2069409 < baseStart_2069409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069496 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 9]
def baseStart_2069496 : Nat := 118140960795 + 2069496 * 2 ^ 59
def prefixEnd_2069496 : Nat := 4983230072969 + 3 ^ 40 * 2069496 * 2
def baseEnd_2069496 : Nat := 472287182469840142703363

theorem tailTrace_2069496 : CollatzResearch.WordTrace tailWord_2069496 prefixEnd_2069496 472287182469840142703363 := by
  unfold tailWord_2069496
  simp only [CollatzResearch.WordTrace]
  refine ⟨37740360055288454311486171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50320480073717939081981561 37740360055288454311486171)
  ·
    refine ⟨56610540082932681467229257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37740360055288454311486171 56610540082932681467229257)
    ·
      refine ⟨42457905062199511100421943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56610540082932681467229257 42457905062199511100421943)
      ·
        refine ⟨63686857593299266650632915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42457905062199511100421943 63686857593299266650632915)
        ·
          refine ⟨95530286389948899975949373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63686857593299266650632915 95530286389948899975949373)
          ·
            refine ⟨35823857396230837490981015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95530286389948899975949373 35823857396230837490981015)
            ·
              refine ⟨53735786094346256236471523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35823857396230837490981015 53735786094346256236471523)
              ·
                refine ⟨80603679141519384354707285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53735786094346256236471523 80603679141519384354707285)
                ·
                  refine ⟨472287182469840142703363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80603679141519384354707285 472287182469840142703363)
                  ·
                    rfl

theorem cell21_2069496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 9].length) (baseStart_2069496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069496 prefixEnd_2069496 := by exact prefixLift 2069496
  have htrace : WordTrace (prefixWord ++ tailWord_2069496) baseStart_2069496 baseEnd_2069496 := by
    simpa [prefixWord, tailWord_2069496, baseEnd_2069496] using wordTrace_append hprefix tailTrace_2069496
  have hstable : (prefixWord ++ tailWord_2069496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069496).length < 2 ^ (prefixWord ++ tailWord_2069496).sum := by decide
  have hdescent : baseEnd_2069496 < baseStart_2069496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069533 : List Nat := [1, 4, 2, 2, 4, 1, 2, 5]
def baseStart_2069533 : Nat := 118140960795 + 2069533 * 2 ^ 59
def prefixEnd_2069533 : Nat := 4983230072969 + 3 ^ 40 * 2069533 * 2
def baseEnd_2069533 : Nat := 157431875457978766862207

theorem tailTrace_2069533 : CollatzResearch.WordTrace tailWord_2069533 prefixEnd_2069533 157431875457978766862207 := by
  unfold tailWord_2069533
  simp only [CollatzResearch.WordTrace]
  refine ⟨75482069611442863942069253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50321379740961909294712835 75482069611442863942069253)
  ·
    refine ⟨14152888052145536989137985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75482069611442863942069253 14152888052145536989137985)
    ·
      refine ⟨10614666039109152741853489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14152888052145536989137985 10614666039109152741853489)
      ·
        refine ⟨7960999529331864556390117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10614666039109152741853489 7960999529331864556390117)
        ·
          refine ⟨1492687411749724604323147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7960999529331864556390117 1492687411749724604323147)
          ·
            refine ⟨2239031117624586906484721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1492687411749724604323147 2239031117624586906484721)
            ·
              refine ⟨1679273338218440179863541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239031117624586906484721 1679273338218440179863541)
              ·
                refine ⟨157431875457978766862207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1679273338218440179863541 157431875457978766862207)
                ·
                  rfl

theorem cell21_2069533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 5].length) (baseStart_2069533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069533 prefixEnd_2069533 := by exact prefixLift 2069533
  have htrace : WordTrace (prefixWord ++ tailWord_2069533) baseStart_2069533 baseEnd_2069533 := by
    simpa [prefixWord, tailWord_2069533, baseEnd_2069533] using wordTrace_append hprefix tailTrace_2069533
  have hstable : (prefixWord ++ tailWord_2069533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069533).length < 2 ^ (prefixWord ++ tailWord_2069533).sum := by decide
  have hdescent : baseEnd_2069533 < baseStart_2069533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069682 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 3]
def baseStart_2069682 : Nat := 118140960795 + 2069682 * 2 ^ 59
def prefixEnd_2069682 : Nat := 4983230072969 + 3 ^ 40 * 2069682 * 2
def baseEnd_2069682 : Nat := 472329630203945152602983

theorem tailTrace_2069682 : CollatzResearch.WordTrace tailWord_2069682 prefixEnd_2069682 472329630203945152602983 := by
  unfold tailWord_2069682
  simp only [CollatzResearch.WordTrace]
  refine ⟨18871876021975765597310825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50325002725268708259495533 18871876021975765597310825)
  ·
    refine ⟨14153907016481824197983119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18871876021975765597310825 14153907016481824197983119)
    ·
      refine ⟨21230860524722736296974679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14153907016481824197983119 21230860524722736296974679)
      ·
        refine ⟨31846290787084104445462019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21230860524722736296974679 31846290787084104445462019)
        ·
          refine ⟨47769436180626156668193029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31846290787084104445462019 47769436180626156668193029)
          ·
            refine ⟨8956769283867404375286193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47769436180626156668193029 8956769283867404375286193)
            ·
              refine ⟨6717576962900553281464645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8956769283867404375286193 6717576962900553281464645)
              ·
                refine ⟨1259545680543853740274621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6717576962900553281464645 1259545680543853740274621)
                ·
                  refine ⟨472329630203945152602983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259545680543853740274621 472329630203945152602983)
                  ·
                    rfl

theorem cell21_2069682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 3].length) (baseStart_2069682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069682 prefixEnd_2069682 := by exact prefixLift 2069682
  have htrace : WordTrace (prefixWord ++ tailWord_2069682) baseStart_2069682 baseEnd_2069682 := by
    simpa [prefixWord, tailWord_2069682, baseEnd_2069682] using wordTrace_append hprefix tailTrace_2069682
  have hstable : (prefixWord ++ tailWord_2069682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069682).length < 2 ^ (prefixWord ++ tailWord_2069682).sum := by decide
  have hdescent : baseEnd_2069682 < baseStart_2069682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069769 : List Nat := [1, 2, 1, 1, 3, 3, 1, 9]
def baseStart_2069769 : Nat := 118140960795 + 2069769 * 2 ^ 59
def prefixEnd_2069769 : Nat := 4983230072969 + 3 ^ 40 * 2069769 * 2
def baseEnd_2069769 : Nat := 157449828263084111550935

theorem tailTrace_2069769 : CollatzResearch.WordTrace tailWord_2069769 prefixEnd_2069769 157449828263084111550935 := by
  unfold tailWord_2069769
  simp only [CollatzResearch.WordTrace]
  refine ⟨75490677238587876247660361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50327118159058584165106907 75490677238587876247660361)
  ·
    refine ⟨56618007928940907185745271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75490677238587876247660361 56618007928940907185745271)
    ·
      refine ⟨84927011893411360778617907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56618007928940907185745271 84927011893411360778617907)
      ·
        refine ⟨127390517840117041167926861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84927011893411360778617907 127390517840117041167926861)
        ·
          refine ⟨47771444190043890437972573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127390517840117041167926861 47771444190043890437972573)
          ·
            refine ⟨17914291571266458914239715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47771444190043890437972573 17914291571266458914239715)
            ·
              refine ⟨26871437356899688371359573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17914291571266458914239715 26871437356899688371359573)
              ·
                refine ⟨157449828263084111550935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26871437356899688371359573 157449828263084111550935)
                ·
                  rfl

theorem cell21_2069769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_2069769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069769 prefixEnd_2069769 := by exact prefixLift 2069769
  have htrace : WordTrace (prefixWord ++ tailWord_2069769) baseStart_2069769 baseEnd_2069769 := by
    simpa [prefixWord, tailWord_2069769, baseEnd_2069769] using wordTrace_append hprefix tailTrace_2069769
  have hstable : (prefixWord ++ tailWord_2069769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069769).length < 2 ^ (prefixWord ++ tailWord_2069769).sum := by decide
  have hdescent : baseEnd_2069769 < baseStart_2069769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069789 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 4]
def baseStart_2069789 : Nat := 118140960795 + 2069789 * 2 ^ 59
def prefixEnd_2069789 : Nat := 4983230072969 + 3 ^ 40 * 2069789 * 2
def baseEnd_2069789 : Nat := 472354049061736744319431

theorem tailTrace_2069789 : CollatzResearch.WordTrace tailWord_2069789 prefixEnd_2069789 472354049061736744319431 := by
  unfold tailWord_2069789
  simp only [CollatzResearch.WordTrace]
  refine ⟨75491406698515419663388421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50327604465676946442258947 75491406698515419663388421)
  ·
    refine ⟨14154638755971641186885329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75491406698515419663388421 14154638755971641186885329)
    ·
      refine ⟨10615979066978730890163997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14154638755971641186885329 10615979066978730890163997)
      ·
        refine ⟨3980992150117024083811499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10615979066978730890163997 3980992150117024083811499)
        ·
          refine ⟨5971488225175536125717249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3980992150117024083811499 5971488225175536125717249)
          ·
            refine ⟨4478616168881652094287937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5971488225175536125717249 4478616168881652094287937)
            ·
              refine ⟨3358962126661239070715953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4478616168881652094287937 3358962126661239070715953)
              ·
                refine ⟨2519221594995929303036965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3358962126661239070715953 2519221594995929303036965)
                ·
                  refine ⟨472354049061736744319431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519221594995929303036965 472354049061736744319431)
                  ·
                    rfl

theorem cell21_2069789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_2069789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069789 prefixEnd_2069789 := by exact prefixLift 2069789
  have htrace : WordTrace (prefixWord ++ tailWord_2069789) baseStart_2069789 baseEnd_2069789 := by
    simpa [prefixWord, tailWord_2069789, baseEnd_2069789] using wordTrace_append hprefix tailTrace_2069789
  have hstable : (prefixWord ++ tailWord_2069789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069789).length < 2 ^ (prefixWord ++ tailWord_2069789).sum := by decide
  have hdescent : baseEnd_2069789 < baseStart_2069789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069792 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 3]
def baseStart_2069792 : Nat := 118140960795 + 2069792 * 2 ^ 59
def prefixEnd_2069792 : Nat := 4983230072969 + 3 ^ 40 * 2069792 * 2
def baseEnd_2069792 : Nat := 472354733702609405769425

theorem tailTrace_2069792 : CollatzResearch.WordTrace tailWord_2069792 prefixEnd_2069792 472354733702609405769425 := by
  unfold tailWord_2069792
  simp only [CollatzResearch.WordTrace]
  refine ⟨37745758058752275587873815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50327677411669700783831753 37745758058752275587873815)
  ·
    refine ⟨56618637088128413381810723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37745758058752275587873815 56618637088128413381810723)
    ·
      refine ⟨84927955632192620072716085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56618637088128413381810723 84927955632192620072716085)
      ·
        refine ⟨7961995840518058131817133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84927955632192620072716085 7961995840518058131817133)
        ·
          refine ⟨2985748440194271799431425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7961995840518058131817133 2985748440194271799431425)
          ·
            refine ⟨2239311330145703849573569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2985748440194271799431425 2239311330145703849573569)
            ·
              refine ⟨1679483497609277887180177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239311330145703849573569 1679483497609277887180177)
              ·
                refine ⟨1259612623206958415385133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1679483497609277887180177 1259612623206958415385133)
                ·
                  refine ⟨472354733702609405769425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1259612623206958415385133 472354733702609405769425)
                  ·
                    rfl

theorem cell21_2069792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 3].length) (baseStart_2069792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069792 prefixEnd_2069792 := by exact prefixLift 2069792
  have htrace : WordTrace (prefixWord ++ tailWord_2069792) baseStart_2069792 baseEnd_2069792 := by
    simpa [prefixWord, tailWord_2069792, baseEnd_2069792] using wordTrace_append hprefix tailTrace_2069792
  have hstable : (prefixWord ++ tailWord_2069792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069792).length < 2 ^ (prefixWord ++ tailWord_2069792).sum := by decide
  have hdescent : baseEnd_2069792 < baseStart_2069792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069972 : List Nat := [2, 4, 1, 2, 4, 1, 1, 6]
def baseStart_2069972 : Nat := 118140960795 + 2069972 * 2 ^ 59
def prefixEnd_2069972 : Nat := 4983230072969 + 3 ^ 40 * 2069972 * 2
def baseEnd_2069972 : Nat := 157465270718323030923019

theorem tailTrace_2069972 : CollatzResearch.WordTrace tailWord_2069972 prefixEnd_2069972 157465270718323030923019 := by
  unfold tailWord_2069972
  simp only [CollatzResearch.WordTrace]
  refine ⟨37749040628426220958650085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50332054171234961278200113 37749040628426220958650085)
  ·
    refine ⟨7077945117829916429746891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37749040628426220958650085 7077945117829916429746891)
    ·
      refine ⟨10616917676744874644620337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7077945117829916429746891 10616917676744874644620337)
      ·
        refine ⟨7962688257558655983465253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10616917676744874644620337 7962688257558655983465253)
        ·
          refine ⟨1493004048292247996899735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7962688257558655983465253 1493004048292247996899735)
          ·
            refine ⟨2239506072438371995349603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493004048292247996899735 2239506072438371995349603)
            ·
              refine ⟨3359259108657557993024405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239506072438371995349603 3359259108657557993024405)
              ·
                refine ⟨157465270718323030923019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3359259108657557993024405 157465270718323030923019)
                ·
                  rfl

theorem cell21_2069972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 6].length) (baseStart_2069972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069972 prefixEnd_2069972 := by exact prefixLift 2069972
  have htrace : WordTrace (prefixWord ++ tailWord_2069972) baseStart_2069972 baseEnd_2069972 := by
    simpa [prefixWord, tailWord_2069972, baseEnd_2069972] using wordTrace_append hprefix tailTrace_2069972
  have hstable : (prefixWord ++ tailWord_2069972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069972).length < 2 ^ (prefixWord ++ tailWord_2069972).sum := by decide
  have hdescent : baseEnd_2069972 < baseStart_2069972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2069983 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 4]
def baseStart_2069983 : Nat := 118140960795 + 2069983 * 2 ^ 59
def prefixEnd_2069983 : Nat := 4983230072969 + 3 ^ 40 * 2069983 * 2
def baseEnd_2069983 : Nat := 472398322504835518085701

theorem tailTrace_2069983 : CollatzResearch.WordTrace tailWord_2069983 prefixEnd_2069983 472398322504835518085701 := by
  unfold tailWord_2069983
  simp only [CollatzResearch.WordTrace]
  refine ⟨75498482459812590795950603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50332321639875060530633735 75498482459812590795950603)
  ·
    refine ⟨113247723689718886193925905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75498482459812590795950603 113247723689718886193925905)
    ·
      refine ⟨84935792767289164645444429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113247723689718886193925905 84935792767289164645444429)
      ·
        refine ⟨31850922287733436742041661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 84935792767289164645444429 31850922287733436742041661)
        ·
          refine ⟨11944095857900038778265623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31850922287733436742041661 11944095857900038778265623)
          ·
            refine ⟨17916143786850058167398435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11944095857900038778265623 17916143786850058167398435)
            ·
              refine ⟨26874215680275087251097653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17916143786850058167398435 26874215680275087251097653)
              ·
                refine ⟨2519457720025789429790405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26874215680275087251097653 2519457720025789429790405)
                ·
                  refine ⟨472398322504835518085701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519457720025789429790405 472398322504835518085701)
                  ·
                    rfl

theorem cell21_2069983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_2069983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2069983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2069983 prefixEnd_2069983 := by exact prefixLift 2069983
  have htrace : WordTrace (prefixWord ++ tailWord_2069983) baseStart_2069983 baseEnd_2069983 := by
    simpa [prefixWord, tailWord_2069983, baseEnd_2069983] using wordTrace_append hprefix tailTrace_2069983
  have hstable : (prefixWord ++ tailWord_2069983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2069983).length < 2 ^ (prefixWord ++ tailWord_2069983).sum := by decide
  have hdescent : baseEnd_2069983 < baseStart_2069983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2069983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070017 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 4]
def baseStart_2070017 : Nat := 118140960795 + 2070017 * 2 ^ 59
def prefixEnd_2070017 : Nat := 4983230072969 + 3 ^ 40 * 2070017 * 2
def baseEnd_2070017 : Nat := 472406081768059014518965

theorem tailTrace_2070017 : CollatzResearch.WordTrace tailWord_2070017 prefixEnd_2070017 472406081768059014518965 := by
  unfold tailWord_2070017
  simp only [CollatzResearch.WordTrace]
  refine ⟨75499722541689414602688305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50333148361126276401792203 75499722541689414602688305)
  ·
    refine ⟨56624791906267060952016229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75499722541689414602688305 56624791906267060952016229)
    ·
      refine ⟨10617148482425073928503043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56624791906267060952016229 10617148482425073928503043)
      ·
        refine ⟨15925722723637610892754565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10617148482425073928503043 15925722723637610892754565)
        ·
          refine ⟨2986073010682052042391481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15925722723637610892754565 2986073010682052042391481)
          ·
            refine ⟨2239554758011539031793611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2986073010682052042391481 2239554758011539031793611)
            ·
              refine ⟨3359332137017308547690417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2239554758011539031793611 3359332137017308547690417)
              ·
                refine ⟨2519499102762981410767813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3359332137017308547690417 2519499102762981410767813)
                ·
                  refine ⟨472406081768059014518965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519499102762981410767813 472406081768059014518965)
                  ·
                    rfl

theorem cell21_2070017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_2070017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070017 prefixEnd_2070017 := by exact prefixLift 2070017
  have htrace : WordTrace (prefixWord ++ tailWord_2070017) baseStart_2070017 baseEnd_2070017 := by
    simpa [prefixWord, tailWord_2070017, baseEnd_2070017] using wordTrace_append hprefix tailTrace_2070017
  have hstable : (prefixWord ++ tailWord_2070017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070017).length < 2 ^ (prefixWord ++ tailWord_2070017).sum := by decide
  have hdescent : baseEnd_2070017 < baseStart_2070017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070073 : List Nat := [1, 2, 1, 5, 1, 2, 9]
def baseStart_2070073 : Nat := 118140960795 + 2070073 * 2 ^ 59
def prefixEnd_2070073 : Nat := 4983230072969 + 3 ^ 40 * 2070073 * 2
def baseEnd_2070073 : Nat := 52490984636779484620613

theorem tailTrace_2070073 : CollatzResearch.WordTrace tailWord_2070073 prefixEnd_2070073 52490984636779484620613 := by
  unfold tailWord_2070073
  simp only [CollatzResearch.WordTrace]
  refine ⟨75501765029486536166726873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50334510019657690777817915 75501765029486536166726873)
  ·
    refine ⟨56626323772114902125045155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75501765029486536166726873 56626323772114902125045155)
    ·
      refine ⟨84939485658172353187567733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56626323772114902125045155 84939485658172353187567733)
      ·
        refine ⟨7963076780453658111334475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 84939485658172353187567733 7963076780453658111334475)
        ·
          refine ⟨11944615170680487167001713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7963076780453658111334475 11944615170680487167001713)
          ·
            refine ⟨8958461378010365375251285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11944615170680487167001713 8958461378010365375251285)
            ·
              refine ⟨52490984636779484620613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8958461378010365375251285 52490984636779484620613)
              ·
                rfl

theorem cell21_2070073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 9].length) (baseStart_2070073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070073 prefixEnd_2070073 := by exact prefixLift 2070073
  have htrace : WordTrace (prefixWord ++ tailWord_2070073) baseStart_2070073 baseEnd_2070073 := by
    simpa [prefixWord, tailWord_2070073, baseEnd_2070073] using wordTrace_append hprefix tailTrace_2070073
  have hstable : (prefixWord ++ tailWord_2070073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070073).length < 2 ^ (prefixWord ++ tailWord_2070073).sum := by decide
  have hdescent : baseEnd_2070073 < baseStart_2070073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070093 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2070093 : Nat := 118140960795 + 2070093 * 2 ^ 59
def prefixEnd_2070093 : Nat := 4983230072969 + 3 ^ 40 * 2070093 * 2
def baseEnd_2070093 : Nat := 472423426003499771252143

theorem tailTrace_2070093 : CollatzResearch.WordTrace tailWord_2070093 prefixEnd_2070093 472423426003499771252143 := by
  unfold tailWord_2070093
  simp only [CollatzResearch.WordTrace]
  refine ⟨75502494489414079582454933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50334996326276053054969955 75502494489414079582454933)
  ·
    refine ⟨3539179429191284980427575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 75502494489414079582454933 3539179429191284980427575)
    ·
      refine ⟨5308769143786927470641363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539179429191284980427575 5308769143786927470641363)
      ·
        refine ⟨7963153715680391205962045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308769143786927470641363 7963153715680391205962045)
        ·
          refine ⟨2986182643380146702235767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7963153715680391205962045 2986182643380146702235767)
          ·
            refine ⟨4479273965070220053353651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986182643380146702235767 4479273965070220053353651)
            ·
              refine ⟨6718910947605330080030477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479273965070220053353651 6718910947605330080030477)
              ·
                refine ⟨2519591605351998780011429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6718910947605330080030477 2519591605351998780011429)
                ·
                  refine ⟨472423426003499771252143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519591605351998780011429 472423426003499771252143)
                  ·
                    rfl

theorem cell21_2070093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2070093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070093 prefixEnd_2070093 := by exact prefixLift 2070093
  have htrace : WordTrace (prefixWord ++ tailWord_2070093) baseStart_2070093 baseEnd_2070093 := by
    simpa [prefixWord, tailWord_2070093, baseEnd_2070093] using wordTrace_append hprefix tailTrace_2070093
  have hstable : (prefixWord ++ tailWord_2070093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070093).length < 2 ^ (prefixWord ++ tailWord_2070093).sum := by decide
  have hdescent : baseEnd_2070093 < baseStart_2070093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070225 : List Nat := [1, 2, 2, 1, 2, 5, 1, 7]
def baseStart_2070225 : Nat := 118140960795 + 2070225 * 2 ^ 59
def prefixEnd_2070225 : Nat := 4983230072969 + 3 ^ 40 * 2070225 * 2
def baseEnd_2070225 : Nat := 157484516733965625017291

theorem tailTrace_2070225 : CollatzResearch.WordTrace tailWord_2070225 prefixEnd_2070225 157484516733965625017291 := by
  unfold tailWord_2070225
  simp only [CollatzResearch.WordTrace]
  refine ⟨75507308924935866126260129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50338205949957244084173419 75507308924935866126260129)
  ·
    refine ⟨56630481693701899594695097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75507308924935866126260129 56630481693701899594695097)
    ·
      refine ⟨42472861270276424696021323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56630481693701899594695097 42472861270276424696021323)
      ·
        refine ⟨63709291905414637044031985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42472861270276424696021323 63709291905414637044031985)
        ·
          refine ⟨47781968929060977783023989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63709291905414637044031985 47781968929060977783023989)
          ·
            refine ⟨4479559587099466667158499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 47781968929060977783023989 4479559587099466667158499)
            ·
              refine ⟨6719339380649200000737749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4479559587099466667158499 6719339380649200000737749)
              ·
                refine ⟨157484516733965625017291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6719339380649200000737749 157484516733965625017291)
                ·
                  rfl

theorem cell21_2070225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 7].length) (baseStart_2070225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070225 prefixEnd_2070225 := by exact prefixLift 2070225
  have htrace : WordTrace (prefixWord ++ tailWord_2070225) baseStart_2070225 baseEnd_2070225 := by
    simpa [prefixWord, tailWord_2070225, baseEnd_2070225] using wordTrace_append hprefix tailTrace_2070225
  have hstable : (prefixWord ++ tailWord_2070225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070225).length < 2 ^ (prefixWord ++ tailWord_2070225).sum := by decide
  have hdescent : baseEnd_2070225 < baseStart_2070225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070346 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_2070346 : Nat := 118140960795 + 2070346 * 2 ^ 59
def prefixEnd_2070346 : Nat := 4983230072969 + 3 ^ 40 * 2070346 * 2
def baseEnd_2070346 : Nat := 472481164050427553534959

theorem tailTrace_2070346 : CollatzResearch.WordTrace tailWord_2070346 prefixEnd_2070346 472481164050427553534959 := by
  unfold tailWord_2070346
  simp only [CollatzResearch.WordTrace]
  refine ⟨18877930539374375947853723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50341148104998335860943261 18877930539374375947853723)
  ·
    refine ⟨28316895809061563921780585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18877930539374375947853723 28316895809061563921780585)
    ·
      refine ⟨21237671856796172941335439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28316895809061563921780585 21237671856796172941335439)
      ·
        refine ⟨31856507785194259412003159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21237671856796172941335439 31856507785194259412003159)
        ·
          refine ⟨47784761677791389118004739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31856507785194259412003159 47784761677791389118004739)
          ·
            refine ⟨71677142516687083677007109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47784761677791389118004739 71677142516687083677007109)
            ·
              refine ⟨13439464221878828189438833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71677142516687083677007109 13439464221878828189438833)
              ·
                refine ⟨10079598166409121142079125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13439464221878828189438833 10079598166409121142079125)
                ·
                  refine ⟨472481164050427553534959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10079598166409121142079125 472481164050427553534959)
                  ·
                    rfl

theorem cell21_2070346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_2070346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070346 prefixEnd_2070346 := by exact prefixLift 2070346
  have htrace : WordTrace (prefixWord ++ tailWord_2070346) baseStart_2070346 baseEnd_2070346 := by
    simpa [prefixWord, tailWord_2070346, baseEnd_2070346] using wordTrace_append hprefix tailTrace_2070346
  have hstable : (prefixWord ++ tailWord_2070346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070346).length < 2 ^ (prefixWord ++ tailWord_2070346).sum := by decide
  have hdescent : baseEnd_2070346 < baseStart_2070346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070380 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 4]
def baseStart_2070380 : Nat := 118140960795 + 2070380 * 2 ^ 59
def prefixEnd_2070380 : Nat := 4983230072969 + 3 ^ 40 * 2070380 * 2
def baseEnd_2070380 : Nat := 472488923313651049968223

theorem tailTrace_2070380 : CollatzResearch.WordTrace tailWord_2070380 prefixEnd_2070380 472488923313651049968223 := by
  unfold tailWord_2070380
  simp only [CollatzResearch.WordTrace]
  refine ⟨37756481119687163799076297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50341974826249551732101729 37756481119687163799076297)
  ·
    refine ⟨28317360839765372849307223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37756481119687163799076297 28317360839765372849307223)
    ·
      refine ⟨42476041259648059273960835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28317360839765372849307223 42476041259648059273960835)
      ·
        refine ⟨63714061889472088910941253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42476041259648059273960835 63714061889472088910941253)
        ·
          refine ⟨11946386604276016670801485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63714061889472088910941253 11946386604276016670801485)
          ·
            refine ⟨4479894976603506251550557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11946386604276016670801485 4479894976603506251550557)
            ·
              refine ⟨1679960616226314844331459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4479894976603506251550557 1679960616226314844331459)
              ·
                refine ⟨2519940924339472266497189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679960616226314844331459 2519940924339472266497189)
                ·
                  refine ⟨472488923313651049968223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2519940924339472266497189 472488923313651049968223)
                  ·
                    rfl

theorem cell21_2070380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_2070380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070380 prefixEnd_2070380 := by exact prefixLift 2070380
  have htrace : WordTrace (prefixWord ++ tailWord_2070380) baseStart_2070380 baseEnd_2070380 := by
    simpa [prefixWord, tailWord_2070380, baseEnd_2070380] using wordTrace_append hprefix tailTrace_2070380
  have hstable : (prefixWord ++ tailWord_2070380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070380).length < 2 ^ (prefixWord ++ tailWord_2070380).sum := by decide
  have hdescent : baseEnd_2070380 < baseStart_2070380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070453 : List Nat := [1, 3, 3, 2, 1, 2, 2, 7]
def baseStart_2070453 : Nat := 118140960795 + 2070453 * 2 ^ 59
def prefixEnd_2070453 : Nat := 4983230072969 + 3 ^ 40 * 2070453 * 2
def baseEnd_2070453 : Nat := 157501860969406381750469

theorem tailTrace_2070453 : CollatzResearch.WordTrace tailWord_2070453 prefixEnd_2070453 157501860969406381750469 := by
  unfold tailWord_2070453
  simp only [CollatzResearch.WordTrace]
  refine ⟨75515624768109861065560013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50343749845406574043706675 75515624768109861065560013)
  ·
    refine ⟨28318359288041197899585005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75515624768109861065560013 28318359288041197899585005)
    ·
      refine ⟨10619384733015449212344377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28318359288041197899585005 10619384733015449212344377)
      ·
        refine ⟨7964538549761586909258283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10619384733015449212344377 7964538549761586909258283)
        ·
          refine ⟨11946807824642380363887425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964538549761586909258283 11946807824642380363887425)
          ·
            refine ⟨8960105868481785272915569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11946807824642380363887425 8960105868481785272915569)
            ·
              refine ⟨6720079401361338954686677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8960105868481785272915569 6720079401361338954686677)
              ·
                refine ⟨157501860969406381750469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6720079401361338954686677 157501860969406381750469)
                ·
                  rfl

theorem cell21_2070453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_2070453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070453 prefixEnd_2070453 := by exact prefixLift 2070453
  have htrace : WordTrace (prefixWord ++ tailWord_2070453) baseStart_2070453 baseEnd_2070453 := by
    simpa [prefixWord, tailWord_2070453, baseEnd_2070453] using wordTrace_append hprefix tailTrace_2070453
  have hstable : (prefixWord ++ tailWord_2070453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070453).length < 2 ^ (prefixWord ++ tailWord_2070453).sum := by decide
  have hdescent : baseEnd_2070453 < baseStart_2070453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070484 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2070484 : Nat := 118140960795 + 2070484 * 2 ^ 59
def prefixEnd_2070484 : Nat := 4983230072969 + 3 ^ 40 * 2070484 * 2
def baseEnd_2070484 : Nat := 472512657530569980234677

theorem tailTrace_2070484 : CollatzResearch.WordTrace tailWord_2070484 prefixEnd_2070484 472512657530569980234677 := by
  unfold tailWord_2070484
  simp only [CollatzResearch.WordTrace]
  refine ⟨37758377715498776679969253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50344503620665035573292337 37758377715498776679969253)
  ·
    refine ⟨7079695821656020627494235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37758377715498776679969253 7079695821656020627494235)
    ·
      refine ⟨10619543732484030941241353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7079695821656020627494235 10619543732484030941241353)
      ·
        refine ⟨7964657799363023205931015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10619543732484030941241353 7964657799363023205931015)
        ·
          refine ⟨11946986699044534808896523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964657799363023205931015 11946986699044534808896523)
          ·
            refine ⟨17920480048566802213344785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11946986699044534808896523 17920480048566802213344785)
            ·
              refine ⟨13440360036425101660008589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17920480048566802213344785 13440360036425101660008589)
              ·
                refine ⟨5040135013659413122503221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13440360036425101660008589 5040135013659413122503221)
                ·
                  refine ⟨472512657530569980234677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5040135013659413122503221 472512657530569980234677)
                  ·
                    rfl

theorem cell21_2070484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2070484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070484 prefixEnd_2070484 := by exact prefixLift 2070484
  have htrace : WordTrace (prefixWord ++ tailWord_2070484) baseStart_2070484 baseEnd_2070484 := by
    simpa [prefixWord, tailWord_2070484, baseEnd_2070484] using wordTrace_append hprefix tailTrace_2070484
  have hstable : (prefixWord ++ tailWord_2070484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070484).length < 2 ^ (prefixWord ++ tailWord_2070484).sum := by decide
  have hdescent : baseEnd_2070484 < baseStart_2070484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070512 : List Nat := [2, 1, 1, 1, 3, 2, 2, 9]
def baseStart_2070512 : Nat := 118140960795 + 2070512 * 2 ^ 59
def prefixEnd_2070512 : Nat := 4983230072969 + 3 ^ 40 * 2070512 * 2
def baseEnd_2070512 : Nat := 157506349170682717922651

theorem tailTrace_2070512 : CollatzResearch.WordTrace tailWord_2070512 prefixEnd_2070512 157506349170682717922651 := by
  unfold tailWord_2070512
  simp only [CollatzResearch.WordTrace]
  refine ⟨37758888337448057070978895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50345184449930742761305193 37758888337448057070978895)
  ·
    refine ⟨56638332506172085606468343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37758888337448057070978895 56638332506172085606468343)
    ·
      refine ⟨84957498759258128409702515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56638332506172085606468343 84957498759258128409702515)
      ·
        refine ⟨127436248138887192614553773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 84957498759258128409702515 127436248138887192614553773)
        ·
          refine ⟨47788593052082697230457665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127436248138887192614553773 47788593052082697230457665)
          ·
            refine ⟨35841444789062022922843249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47788593052082697230457665 35841444789062022922843249)
            ·
              refine ⟨26881083591796517192132437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35841444789062022922843249 26881083591796517192132437)
              ·
                refine ⟨157506349170682717922651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26881083591796517192132437 157506349170682717922651)
                ·
                  rfl

theorem cell21_2070512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_2070512 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070512 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070512 prefixEnd_2070512 := by exact prefixLift 2070512
  have htrace : WordTrace (prefixWord ++ tailWord_2070512) baseStart_2070512 baseEnd_2070512 := by
    simpa [prefixWord, tailWord_2070512, baseEnd_2070512] using wordTrace_append hprefix tailTrace_2070512
  have hstable : (prefixWord ++ tailWord_2070512).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070512).length < 2 ^ (prefixWord ++ tailWord_2070512).sum := by decide
  have hdescent : baseEnd_2070512 < baseStart_2070512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070532 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_2070532 : Nat := 118140960795 + 2070532 * 2 ^ 59
def prefixEnd_2070532 : Nat := 4983230072969 + 3 ^ 40 * 2070532 * 2
def baseEnd_2070532 : Nat := 472523611784532563434579

theorem tailTrace_2070532 : CollatzResearch.WordTrace tailWord_2070532 prefixEnd_2070532 472523611784532563434579 := by
  unfold tailWord_2070532
  simp only [CollatzResearch.WordTrace]
  refine ⟨37759253067411828778842925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50345670756549105038457233 37759253067411828778842925)
  ·
    refine ⟨14159719900279435792066097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37759253067411828778842925 14159719900279435792066097)
    ·
      refine ⟨10619789925209576844049573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14159719900279435792066097 10619789925209576844049573)
      ·
        refine ⟨1991210610976795658259295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10619789925209576844049573 1991210610976795658259295)
        ·
          refine ⟨2986815916465193487388943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1991210610976795658259295 2986815916465193487388943)
          ·
            refine ⟨4480223874697790231083415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2986815916465193487388943 4480223874697790231083415)
            ·
              refine ⟨6720335812046685346625123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480223874697790231083415 6720335812046685346625123)
              ·
                refine ⟨10080503718070028019937685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6720335812046685346625123 10080503718070028019937685)
                ·
                  refine ⟨472523611784532563434579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10080503718070028019937685 472523611784532563434579)
                  ·
                    rfl

theorem cell21_2070532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_2070532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070532 prefixEnd_2070532 := by exact prefixLift 2070532
  have htrace : WordTrace (prefixWord ++ tailWord_2070532) baseStart_2070532 baseEnd_2070532 := by
    simpa [prefixWord, tailWord_2070532, baseEnd_2070532] using wordTrace_append hprefix tailTrace_2070532
  have hstable : (prefixWord ++ tailWord_2070532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070532).length < 2 ^ (prefixWord ++ tailWord_2070532).sum := by decide
  have hdescent : baseEnd_2070532 < baseStart_2070532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070577 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 3]
def baseStart_2070577 : Nat := 118140960795 + 2070577 * 2 ^ 59
def prefixEnd_2070577 : Nat := 4983230072969 + 3 ^ 40 * 2070577 * 2
def baseEnd_2070577 : Nat := 472533881397622485184487

theorem tailTrace_2070577 : CollatzResearch.WordTrace tailWord_2070577 prefixEnd_2070577 472533881397622485184487 := by
  unfold tailWord_2070577
  simp only [CollatzResearch.WordTrace]
  refine ⟨75520147419660630243073985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50346764946440420162049323 75520147419660630243073985)
  ·
    refine ⟨56640110564745472682305489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75520147419660630243073985 56640110564745472682305489)
    ·
      refine ⟨42480082923559104511729117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56640110564745472682305489 42480082923559104511729117)
      ·
        refine ⟨15930031096334664191898419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42480082923559104511729117 15930031096334664191898419)
        ·
          refine ⟨23895046644501996287847629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15930031096334664191898419 23895046644501996287847629)
          ·
            refine ⟨8960642491688248607942861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23895046644501996287847629 8960642491688248607942861)
            ·
              refine ⟨3360240934383093227978573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8960642491688248607942861 3360240934383093227978573)
              ·
                refine ⟨1260090350393659960491965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3360240934383093227978573 1260090350393659960491965)
                ·
                  refine ⟨472533881397622485184487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260090350393659960491965 472533881397622485184487)
                  ·
                    rfl

theorem cell21_2070577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_2070577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070577 prefixEnd_2070577 := by exact prefixLift 2070577
  have htrace : WordTrace (prefixWord ++ tailWord_2070577) baseStart_2070577 baseEnd_2070577 := by
    simpa [prefixWord, tailWord_2070577, baseEnd_2070577] using wordTrace_append hprefix tailTrace_2070577
  have hstable : (prefixWord ++ tailWord_2070577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070577).length < 2 ^ (prefixWord ++ tailWord_2070577).sum := by decide
  have hdescent : baseEnd_2070577 < baseStart_2070577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070653 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 3]
def baseStart_2070653 : Nat := 118140960795 + 2070653 * 2 ^ 59
def prefixEnd_2070653 : Nat := 4983230072969 + 3 ^ 40 * 2070653 * 2
def baseEnd_2070653 : Nat := 472551225633063241917665

theorem tailTrace_2070653 : CollatzResearch.WordTrace tailWord_2070653 prefixEnd_2070653 472551225633063241917665 := by
  unfold tailWord_2070653
  simp only [CollatzResearch.WordTrace]
  refine ⟨75522919367385295222840613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 50348612911590196815227075 75522919367385295222840613)
  ·
    refine ⟨14160547381384742854282615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75522919367385295222840613 14160547381384742854282615)
    ·
      refine ⟨21240821072077114281423923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14160547381384742854282615 21240821072077114281423923)
      ·
        refine ⟨31861231608115671422135885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21240821072077114281423923 31861231608115671422135885)
        ·
          refine ⟨11947961853043376783300957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31861231608115671422135885 11947961853043376783300957)
          ·
            refine ⟨4480485694891266293737859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11947961853043376783300957 4480485694891266293737859)
            ·
              refine ⟨6720728542336899440606789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4480485694891266293737859 6720728542336899440606789)
              ·
                refine ⟨1260136601688168645113773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6720728542336899440606789 1260136601688168645113773)
                ·
                  refine ⟨472551225633063241917665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260136601688168645113773 472551225633063241917665)
                  ·
                    rfl

theorem cell21_2070653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_2070653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070653 prefixEnd_2070653 := by exact prefixLift 2070653
  have htrace : WordTrace (prefixWord ++ tailWord_2070653) baseStart_2070653 baseEnd_2070653 := by
    simpa [prefixWord, tailWord_2070653, baseEnd_2070653] using wordTrace_append hprefix tailTrace_2070653
  have hstable : (prefixWord ++ tailWord_2070653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070653).length < 2 ^ (prefixWord ++ tailWord_2070653).sum := by decide
  have hdescent : baseEnd_2070653 < baseStart_2070653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070698 : List Nat := [3, 1, 5, 1, 2, 1, 8]
def baseStart_2070698 : Nat := 118140960795 + 2070698 * 2 ^ 59
def prefixEnd_2070698 : Nat := 4983230072969 + 3 ^ 40 * 2070698 * 2
def baseEnd_2070698 : Nat := 52506832805128129296397

theorem tailTrace_2070698 : CollatzResearch.WordTrace tailWord_2070698 prefixEnd_2070698 52506832805128129296397 := by
  unfold tailWord_2070698
  simp only [CollatzResearch.WordTrace]
  refine ⟨18881140163055566977057187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 50349707101481511938819165 18881140163055566977057187)
  ·
    refine ⟨28321710244583350465585781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18881140163055566977057187 28321710244583350465585781)
    ·
      refine ⟨2655160335429689106148667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28321710244583350465585781 2655160335429689106148667)
      ·
        refine ⟨3982740503144533659223001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2655160335429689106148667 3982740503144533659223001)
        ·
          refine ⟨2987055377358400244417251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3982740503144533659223001 2987055377358400244417251)
          ·
            refine ⟨4480583066037600366625877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2987055377358400244417251 4480583066037600366625877)
            ·
              refine ⟨52506832805128129296397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4480583066037600366625877 52506832805128129296397)
              ·
                rfl

theorem cell21_2070698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 8].length) (baseStart_2070698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070698 prefixEnd_2070698 := by exact prefixLift 2070698
  have htrace : WordTrace (prefixWord ++ tailWord_2070698) baseStart_2070698 baseEnd_2070698 := by
    simpa [prefixWord, tailWord_2070698, baseEnd_2070698] using wordTrace_append hprefix tailTrace_2070698
  have hstable : (prefixWord ++ tailWord_2070698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070698).length < 2 ^ (prefixWord ++ tailWord_2070698).sum := by decide
  have hdescent : baseEnd_2070698 < baseStart_2070698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070712 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_2070712 : Nat := 118140960795 + 2070712 * 2 ^ 59
def prefixEnd_2070712 : Nat := 4983230072969 + 3 ^ 40 * 2070712 * 2
def baseEnd_2070712 : Nat := 472564690236892250434211

theorem tailTrace_2070712 : CollatzResearch.WordTrace tailWord_2070712 prefixEnd_2070712 472564690236892250434211 := by
  unfold tailWord_2070712
  simp only [CollatzResearch.WordTrace]
  refine ⟨37762535637085774149619195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50350047516114365532825593 37762535637085774149619195)
  ·
    refine ⟨56643803455628661224428793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37762535637085774149619195 56643803455628661224428793)
    ·
      refine ⟨42482852591721495918321595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56643803455628661224428793 42482852591721495918321595)
      ·
        refine ⟨63724278887582243877482393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42482852591721495918321595 63724278887582243877482393)
        ·
          refine ⟨47793209165686682908111795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63724278887582243877482393 47793209165686682908111795)
          ·
            refine ⟨71689813748530024362167693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47793209165686682908111795 71689813748530024362167693)
            ·
              refine ⟨26883680155698759135812885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71689813748530024362167693 26883680155698759135812885)
              ·
                refine ⟨1260172507298379334491229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26883680155698759135812885 1260172507298379334491229)
                ·
                  refine ⟨472564690236892250434211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1260172507298379334491229 472564690236892250434211)
                  ·
                    rfl

theorem cell21_2070712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_2070712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070712 prefixEnd_2070712 := by exact prefixLift 2070712
  have htrace : WordTrace (prefixWord ++ tailWord_2070712) baseStart_2070712 baseEnd_2070712 := by
    simpa [prefixWord, tailWord_2070712, baseEnd_2070712] using wordTrace_append hprefix tailTrace_2070712
  have hstable : (prefixWord ++ tailWord_2070712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070712).length < 2 ^ (prefixWord ++ tailWord_2070712).sum := by decide
  have hdescent : baseEnd_2070712 < baseStart_2070712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2070732 : List Nat := [2, 2, 1, 6, 2, 1, 2, 5]
def baseStart_2070732 : Nat := 118140960795 + 2070732 * 2 ^ 59
def prefixEnd_2070732 : Nat := 4983230072969 + 3 ^ 40 * 2070732 * 2
def baseEnd_2070732 : Nat := 157523084836458886700279

theorem tailTrace_2070732 : CollatzResearch.WordTrace tailWord_2070732 prefixEnd_2070732 157523084836458886700279 := by
  unfold tailWord_2070732
  simp only [CollatzResearch.WordTrace]
  refine ⟨37762900367049545857483225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 50350533822732727809977633 37762900367049545857483225)
  ·
    refine ⟨28322175275287159393112419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37762900367049545857483225 28322175275287159393112419)
    ·
      refine ⟨42483262912930739089668629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28322175275287159393112419 42483262912930739089668629)
      ·
        refine ⟨1991402949043628394828217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 42483262912930739089668629 1991402949043628394828217)
        ·
          refine ⟨1493552211782721296121163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1991402949043628394828217 1493552211782721296121163)
          ·
            refine ⟨2240328317674081944181745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493552211782721296121163 2240328317674081944181745)
            ·
              refine ⟨1680246238255561458136309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2240328317674081944181745 1680246238255561458136309)
              ·
                refine ⟨157523084836458886700279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1680246238255561458136309 157523084836458886700279)
                ·
                  rfl

theorem cell21_2070732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 5].length) (baseStart_2070732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_2070732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_2070732 prefixEnd_2070732 := by exact prefixLift 2070732
  have htrace : WordTrace (prefixWord ++ tailWord_2070732) baseStart_2070732 baseEnd_2070732 := by
    simpa [prefixWord, tailWord_2070732, baseEnd_2070732] using wordTrace_append hprefix tailTrace_2070732
  have hstable : (prefixWord ++ tailWord_2070732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2070732).length < 2 ^ (prefixWord ++ tailWord_2070732).sum := by decide
  have hdescent : baseEnd_2070732 < baseStart_2070732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2070732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
