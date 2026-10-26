import V185TrunkScan23Chunk0168

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_999747 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 3]
def baseStart_999747 : Nat := 118140960795 + 999747 * 2 ^ 59
def prefixEnd_999747 : Nat := 4983230072969 + 3 ^ 40 * 999747 * 2
def baseEnd_999747 : Nat := 513350743890605218964753

theorem tailTrace_999747 : CollatzResearch.WordTrace tailWord_999747 prefixEnd_999747 513350743890605218964753 := by
  unfold tailWord_999747
  simp only [CollatzResearch.WordTrace]
  refine ⟨36463768709094837039149495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24309179139396558026099663 36463768709094837039149495)
  ·
    refine ⟨54695653063642255558724243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36463768709094837039149495 54695653063642255558724243)
    ·
      refine ⟨82043479595463383338086365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54695653063642255558724243 82043479595463383338086365)
      ·
        refine ⟨30766304848298768751782387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82043479595463383338086365 30766304848298768751782387)
        ·
          refine ⟨46149457272448153127673581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30766304848298768751782387 46149457272448153127673581)
          ·
            refine ⟨17306046477168057422877593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46149457272448153127673581 17306046477168057422877593)
            ·
              refine ⟨12979534857876043067158195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17306046477168057422877593 12979534857876043067158195)
              ·
                refine ⟨19469302286814064600737293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12979534857876043067158195 19469302286814064600737293)
                ·
                  refine ⟨7300988357555274225276485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19469302286814064600737293 7300988357555274225276485)
                  ·
                    refine ⟨1368935317041613917239341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7300988357555274225276485 1368935317041613917239341)
                    ·
                      refine ⟨513350743890605218964753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1368935317041613917239341 513350743890605218964753)
                      ·
                        rfl

theorem cell23_999747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_999747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999747 prefixEnd_999747 := by exact prefixLift 999747
  have htrace : WordTrace (prefixWord ++ tailWord_999747) baseStart_999747 baseEnd_999747 := by
    simpa [prefixWord, tailWord_999747, baseEnd_999747] using wordTrace_append hprefix tailTrace_999747
  have hstable : (prefixWord ++ tailWord_999747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999747).length < 2 ^ (prefixWord ++ tailWord_999747).sum := by decide
  have hdescent : baseEnd_999747 < baseStart_999747 := by decide
  rcases family_descends (prefixWord ++ tailWord_999747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999784 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 6]
def baseStart_999784 : Nat := 118140960795 + 999784 * 2 ^ 59
def prefixEnd_999784 : Nat := 4983230072969 + 3 ^ 40 * 999784 * 2
def baseEnd_999784 : Nat := 57041082519424619355787

theorem tailTrace_999784 : CollatzResearch.WordTrace tailWord_999784 prefixEnd_999784 57041082519424619355787 := by
  unfold tailWord_999784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18232559104980396179123203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24310078806640528238830937 18232559104980396179123203)
  ·
    refine ⟨27348838657470594268684805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18232559104980396179123203 27348838657470594268684805)
    ·
      refine ⟨5127907248275736425378401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27348838657470594268684805 5127907248275736425378401)
      ·
        refine ⟨3845930436206802319033801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5127907248275736425378401 3845930436206802319033801)
        ·
          refine ⟨2884447827155101739275351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3845930436206802319033801 2884447827155101739275351)
          ·
            refine ⟨4326671740732652608913027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2884447827155101739275351 4326671740732652608913027)
            ·
              refine ⟨6490007611098978913369541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4326671740732652608913027 6490007611098978913369541)
              ·
                refine ⟨1216876427081058546256789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6490007611098978913369541 1216876427081058546256789)
                ·
                  refine ⟨57041082519424619355787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1216876427081058546256789 57041082519424619355787)
                  ·
                    rfl

theorem cell23_999784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 6].length) (baseStart_999784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999784 prefixEnd_999784 := by exact prefixLift 999784
  have htrace : WordTrace (prefixWord ++ tailWord_999784) baseStart_999784 baseEnd_999784 := by
    simpa [prefixWord, tailWord_999784, baseEnd_999784] using wordTrace_append hprefix tailTrace_999784
  have hstable : (prefixWord ++ tailWord_999784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999784).length < 2 ^ (prefixWord ++ tailWord_999784).sum := by decide
  have hdescent : baseEnd_999784 < baseStart_999784 := by decide
  rcases family_descends (prefixWord ++ tailWord_999784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999788 : List Nat := [2, 2, 1, 1, 6, 1, 1, 4, 1, 4]
def baseStart_999788 : Nat := 118140960795 + 999788 * 2 ^ 59
def prefixEnd_999788 : Nat := 4983230072969 + 3 ^ 40 * 999788 * 2
def baseEnd_999788 : Nat := 171123932199146519517355

theorem tailTrace_999788 : CollatzResearch.WordTrace tailWord_999788 prefixEnd_999788 171123932199146519517355 := by
  unfold tailWord_999788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18232632050973150520696009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24310176067964200694261345 18232632050973150520696009)
  ·
    refine ⟨13674474038229862890522007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18232632050973150520696009 13674474038229862890522007)
    ·
      refine ⟨20511711057344794335783011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13674474038229862890522007 20511711057344794335783011)
      ·
        refine ⟨30767566586017191503674517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20511711057344794335783011 30767566586017191503674517)
        ·
          refine ⟨1442229683719555851734743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 30767566586017191503674517 1442229683719555851734743)
          ·
            refine ⟨2163344525579333777602115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442229683719555851734743 2163344525579333777602115)
            ·
              refine ⟨3245016788369000666403173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163344525579333777602115 3245016788369000666403173)
              ·
                refine ⟨608440647819187624950595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3245016788369000666403173 608440647819187624950595)
                ·
                  refine ⟨912660971728781437425893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608440647819187624950595 912660971728781437425893)
                  ·
                    refine ⟨171123932199146519517355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 912660971728781437425893 171123932199146519517355)
                    ·
                      rfl

theorem cell23_999788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 4, 1, 4].length) (baseStart_999788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999788 prefixEnd_999788 := by exact prefixLift 999788
  have htrace : WordTrace (prefixWord ++ tailWord_999788) baseStart_999788 baseEnd_999788 := by
    simpa [prefixWord, tailWord_999788, baseEnd_999788] using wordTrace_append hprefix tailTrace_999788
  have hstable : (prefixWord ++ tailWord_999788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999788).length < 2 ^ (prefixWord ++ tailWord_999788).sum := by decide
  have hdescent : baseEnd_999788 < baseStart_999788 := by decide
  rcases family_descends (prefixWord ++ tailWord_999788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999831 : List Nat := [1, 1, 3, 3, 1, 1, 6, 1, 1, 5]
def baseStart_999831 : Nat := 118140960795 + 999831 * 2 ^ 59
def prefixEnd_999831 : Nat := 4983230072969 + 3 ^ 40 * 999831 * 2
def baseEnd_999831 : Nat := 171131292088527630104789

theorem tailTrace_999831 : CollatzResearch.WordTrace tailWord_999831 prefixEnd_999831 171131292088527630104789 := by
  unfold tailWord_999831
  simp only [CollatzResearch.WordTrace]
  refine ⟨36466832440790519385207347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24311221627193679590138231 36466832440790519385207347)
  ·
    refine ⟨54700248661185779077811021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36466832440790519385207347 54700248661185779077811021)
    ·
      refine ⟨20512593247944667154179133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54700248661185779077811021 20512593247944667154179133)
      ·
        refine ⟨7692222467979250182817175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20512593247944667154179133 7692222467979250182817175)
        ·
          refine ⟨11538333701968875274225763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7692222467979250182817175 11538333701968875274225763)
          ·
            refine ⟨17307500552953312911338645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11538333701968875274225763 17307500552953312911338645)
            ·
              refine ⟨811289088419686542718999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 17307500552953312911338645 811289088419686542718999)
              ·
                refine ⟨1216933632629529814078499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811289088419686542718999 1216933632629529814078499)
                ·
                  refine ⟨1825400448944294721117749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216933632629529814078499 1825400448944294721117749)
                  ·
                    refine ⟨171131292088527630104789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1825400448944294721117749 171131292088527630104789)
                    ·
                      rfl

theorem cell23_999831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_999831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999831 prefixEnd_999831 := by exact prefixLift 999831
  have htrace : WordTrace (prefixWord ++ tailWord_999831) baseStart_999831 baseEnd_999831 := by
    simpa [prefixWord, tailWord_999831, baseEnd_999831] using wordTrace_append hprefix tailTrace_999831
  have hstable : (prefixWord ++ tailWord_999831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999831).length < 2 ^ (prefixWord ++ tailWord_999831).sum := by decide
  have hdescent : baseEnd_999831 < baseStart_999831 := by decide
  rcases family_descends (prefixWord ++ tailWord_999831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999868 : List Nat := [2, 2, 2, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_999868 : Nat := 118140960795 + 999868 * 2 ^ 59
def prefixEnd_999868 : Nat := 4983230072969 + 3 ^ 40 * 999868 * 2
def baseEnd_999868 : Nat := 513412875049799245551697

theorem tailTrace_999868 : CollatzResearch.WordTrace tailWord_999868 prefixEnd_999868 513412875049799245551697 := by
  unfold tailWord_999868
  simp only [CollatzResearch.WordTrace]
  refine ⟨18234090970828237352152129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24312121294437649802869505 18234090970828237352152129)
  ·
    refine ⟨13675568228121178014114097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18234090970828237352152129 13675568228121178014114097)
    ·
      refine ⟨10256676171090883510585573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13675568228121178014114097 10256676171090883510585573)
      ·
        refine ⟨1923126782079540658234795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10256676171090883510585573 1923126782079540658234795)
        ·
          refine ⟨2884690173119310987352193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1923126782079540658234795 2884690173119310987352193)
          ·
            refine ⟨2163517629839483240514145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884690173119310987352193 2163517629839483240514145)
            ·
              refine ⟨1622638222379612430385609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2163517629839483240514145 1622638222379612430385609)
              ·
                refine ⟨1216978666784709322789207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622638222379612430385609 1216978666784709322789207)
                ·
                  refine ⟨1825468000177063984183811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1216978666784709322789207 1825468000177063984183811)
                  ·
                    refine ⟨2738202000265595976275717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1825468000177063984183811 2738202000265595976275717)
                    ·
                      refine ⟨513412875049799245551697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2738202000265595976275717 513412875049799245551697)
                      ·
                        rfl

theorem cell23_999868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_999868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999868 prefixEnd_999868 := by exact prefixLift 999868
  have htrace : WordTrace (prefixWord ++ tailWord_999868) baseStart_999868 baseEnd_999868 := by
    simpa [prefixWord, tailWord_999868, baseEnd_999868] using wordTrace_append hprefix tailTrace_999868
  have hstable : (prefixWord ++ tailWord_999868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999868).length < 2 ^ (prefixWord ++ tailWord_999868).sum := by decide
  have hdescent : baseEnd_999868 < baseStart_999868 := by decide
  rcases family_descends (prefixWord ++ tailWord_999868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999877 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 6]
def baseStart_999877 : Nat := 118140960795 + 999877 * 2 ^ 59
def prefixEnd_999877 : Nat := 4983230072969 + 3 ^ 40 * 999877 * 2
def baseEnd_999877 : Nat := 513417496375689710339155

theorem tailTrace_999877 : CollatzResearch.WordTrace tailWord_999877 prefixEnd_999877 513417496375689710339155 := by
  unfold tailWord_999877
  simp only [CollatzResearch.WordTrace]
  refine ⟨36468510198623869241381885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24312340132415912827587923 36468510198623869241381885)
  ·
    refine ⟨13675691324483950965518207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36468510198623869241381885 13675691324483950965518207)
    ·
      refine ⟨20513536986725926448277311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13675691324483950965518207 20513536986725926448277311)
      ·
        refine ⟨30770305480088889672415967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20513536986725926448277311 30770305480088889672415967)
        ·
          refine ⟨46155458220133334508623951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30770305480088889672415967 46155458220133334508623951)
          ·
            refine ⟨69233187330200001762935927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46155458220133334508623951 69233187330200001762935927)
            ·
              refine ⟨103849780995300002644403891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69233187330200001762935927 103849780995300002644403891)
              ·
                refine ⟨155774671492950003966605837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103849780995300002644403891 155774671492950003966605837)
                ·
                  refine ⟨58415501809856251487477189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 155774671492950003966605837 58415501809856251487477189)
                  ·
                    refine ⟨10952906589348047153901973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58415501809856251487477189 10952906589348047153901973)
                    ·
                      refine ⟨513417496375689710339155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10952906589348047153901973 513417496375689710339155)
                      ·
                        rfl

theorem cell23_999877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_999877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999877 prefixEnd_999877 := by exact prefixLift 999877
  have htrace : WordTrace (prefixWord ++ tailWord_999877) baseStart_999877 baseEnd_999877 := by
    simpa [prefixWord, tailWord_999877, baseEnd_999877] using wordTrace_append hprefix tailTrace_999877
  have hstable : (prefixWord ++ tailWord_999877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999877).length < 2 ^ (prefixWord ++ tailWord_999877).sum := by decide
  have hdescent : baseEnd_999877 < baseStart_999877 := by decide
  rcases family_descends (prefixWord ++ tailWord_999877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999887 : List Nat := [1, 1, 2, 1, 1, 4, 1, 2, 1, 9]
def baseStart_999887 : Nat := 118140960795 + 999887 * 2 ^ 59
def prefixEnd_999887 : Nat := 4983230072969 + 3 ^ 40 * 999887 * 2
def baseEnd_999887 : Nat := 171140877060744890404703

theorem tailTrace_999887 : CollatzResearch.WordTrace tailWord_999887 prefixEnd_999887 171140877060744890404703 := by
  unfold tailWord_999887
  simp only [CollatzResearch.WordTrace]
  refine ⟨36468874928587640949245915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24312583285725093966163943 36468874928587640949245915)
  ·
    refine ⟨54703312392881461423868873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36468874928587640949245915 54703312392881461423868873)
    ·
      refine ⟨41027484294661096067901655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54703312392881461423868873 41027484294661096067901655)
      ·
        refine ⟨61541226441991644101852483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41027484294661096067901655 61541226441991644101852483)
        ·
          refine ⟨92311839662987466152778725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61541226441991644101852483 92311839662987466152778725)
          ·
            refine ⟨17308469936810149903646011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92311839662987466152778725 17308469936810149903646011)
            ·
              refine ⟨25962704905215224855469017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17308469936810149903646011 25962704905215224855469017)
              ·
                refine ⟨19472028678911418641601763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25962704905215224855469017 19472028678911418641601763)
                ·
                  refine ⟨29208043018367127962402645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19472028678911418641601763 29208043018367127962402645)
                  ·
                    refine ⟨171140877060744890404703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29208043018367127962402645 171140877060744890404703)
                    ·
                      rfl

theorem cell23_999887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_999887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999887 prefixEnd_999887 := by exact prefixLift 999887
  have htrace : WordTrace (prefixWord ++ tailWord_999887) baseStart_999887 baseEnd_999887 := by
    simpa [prefixWord, tailWord_999887, baseEnd_999887] using wordTrace_append hprefix tailTrace_999887
  have hstable : (prefixWord ++ tailWord_999887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999887).length < 2 ^ (prefixWord ++ tailWord_999887).sum := by decide
  have hdescent : baseEnd_999887 < baseStart_999887 := by decide
  rcases family_descends (prefixWord ++ tailWord_999887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999922 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_999922 : Nat := 118140960795 + 999922 * 2 ^ 59
def prefixEnd_999922 : Nat := 4983230072969 + 3 ^ 40 * 999922 * 2
def baseEnd_999922 : Nat := 513440603005142034276449

theorem tailTrace_999922 : CollatzResearch.WordTrace tailWord_999922 prefixEnd_999922 513440603005142034276449 := by
  unfold tailWord_999922
  simp only [CollatzResearch.WordTrace]
  refine ⟨9117537870865210481692505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24313434322307227951180013 9117537870865210481692505)
  ·
    refine ⟨6838153403148907861269379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9117537870865210481692505 6838153403148907861269379)
    ·
      refine ⟨10257230104723361791904069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6838153403148907861269379 10257230104723361791904069)
      ·
        refine ⟨1923230644635630335982013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10257230104723361791904069 1923230644635630335982013)
        ·
          refine ⟨721211491738361375993255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1923230644635630335982013 721211491738361375993255)
          ·
            refine ⟨1081817237607542063989883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721211491738361375993255 1081817237607542063989883)
            ·
              refine ⟨1622725856411313095984825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1081817237607542063989883 1622725856411313095984825)
              ·
                refine ⟨1217044392308484821988619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1622725856411313095984825 1217044392308484821988619)
                ·
                  refine ⟨1825566588462727232982929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217044392308484821988619 1825566588462727232982929)
                  ·
                    refine ⟨1369174941347045424737197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1825566588462727232982929 1369174941347045424737197)
                    ·
                      refine ⟨513440603005142034276449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1369174941347045424737197 513440603005142034276449)
                      ·
                        rfl

theorem cell23_999922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_999922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999922 prefixEnd_999922 := by exact prefixLift 999922
  have htrace : WordTrace (prefixWord ++ tailWord_999922) baseStart_999922 baseEnd_999922 := by
    simpa [prefixWord, tailWord_999922, baseEnd_999922] using wordTrace_append hprefix tailTrace_999922
  have hstable : (prefixWord ++ tailWord_999922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999922).length < 2 ^ (prefixWord ++ tailWord_999922).sum := by decide
  have hdescent : baseEnd_999922 < baseStart_999922 := by decide
  rcases family_descends (prefixWord ++ tailWord_999922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999941 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 3, 4, 2]
def baseStart_999941 : Nat := 118140960795 + 999941 * 2 ^ 59
def prefixEnd_999941 : Nat := 4983230072969 + 3 ^ 40 * 999941 * 2
def baseEnd_999941 : Nat := 513450359137577459938861

theorem tailTrace_999941 : CollatzResearch.WordTrace tailWord_999941 prefixEnd_999941 513450359137577459938861 := by
  unfold tailWord_999941
  simp only [CollatzResearch.WordTrace]
  refine ⟨36470844470392008171711677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24313896313594672114474451 36470844470392008171711677)
  ·
    refine ⟨13676566676397003064391879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36470844470392008171711677 13676566676397003064391879)
    ·
      refine ⟨20514850014595504596587819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13676566676397003064391879 20514850014595504596587819)
      ·
        refine ⟨30772275021893256894881729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20514850014595504596587819 30772275021893256894881729)
        ·
          refine ⟨23079206266419942671161297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30772275021893256894881729 23079206266419942671161297)
          ·
            refine ⟨17309404699814957003370973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23079206266419942671161297 17309404699814957003370973)
            ·
              refine ⟨6491026762430608876264115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17309404699814957003370973 6491026762430608876264115)
              ·
                refine ⟨9736540143645913314396173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491026762430608876264115 9736540143645913314396173)
                ·
                  refine ⟨3651202553867217492898565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9736540143645913314396173 3651202553867217492898565)
                  ·
                    refine ⟨684600478850103279918481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3651202553867217492898565 684600478850103279918481)
                    ·
                      refine ⟨513450359137577459938861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684600478850103279918481 513450359137577459938861)
                      ·
                        rfl

theorem cell23_999941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 4, 2].length) (baseStart_999941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999941 prefixEnd_999941 := by exact prefixLift 999941
  have htrace : WordTrace (prefixWord ++ tailWord_999941) baseStart_999941 baseEnd_999941 := by
    simpa [prefixWord, tailWord_999941, baseEnd_999941] using wordTrace_append hprefix tailTrace_999941
  have hstable : (prefixWord ++ tailWord_999941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999941).length < 2 ^ (prefixWord ++ tailWord_999941).sum := by decide
  have hdescent : baseEnd_999941 < baseStart_999941 := by decide
  rcases family_descends (prefixWord ++ tailWord_999941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_999971 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4]
def baseStart_999971 : Nat := 118140960795 + 999971 * 2 ^ 59
def prefixEnd_999971 : Nat := 4983230072969 + 3 ^ 40 * 999971 * 2
def baseEnd_999971 : Nat := 513465763557212342563723

theorem tailTrace_999971 : CollatzResearch.WordTrace tailWord_999971 prefixEnd_999971 513465763557212342563723 := by
  unfold tailWord_999971
  simp only [CollatzResearch.WordTrace]
  refine ⟨36471938660283323295303767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24314625773522215530202511 36471938660283323295303767)
  ·
    refine ⟨54707907990424984942955651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36471938660283323295303767 54707907990424984942955651)
    ·
      refine ⟨82061861985637477414433477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54707907990424984942955651 82061861985637477414433477)
      ·
        refine ⟨15386599122307027015206277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82061861985637477414433477 15386599122307027015206277)
        ·
          refine ⟨2884987335432567565351177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15386599122307027015206277 2884987335432567565351177)
          ·
            refine ⟨2163740501574425674013383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2884987335432567565351177 2163740501574425674013383)
            ·
              refine ⟨3245610752361638511020075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2163740501574425674013383 3245610752361638511020075)
              ·
                refine ⟨4868416128542457766530113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3245610752361638511020075 4868416128542457766530113)
                ·
                  refine ⟨3651312096406843324897585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4868416128542457766530113 3651312096406843324897585)
                  ·
                    refine ⟨2738484072305132493673189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3651312096406843324897585 2738484072305132493673189)
                    ·
                      refine ⟨513465763557212342563723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2738484072305132493673189 513465763557212342563723)
                      ·
                        rfl

theorem cell23_999971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_999971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_999971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_999971 prefixEnd_999971 := by exact prefixLift 999971
  have htrace : WordTrace (prefixWord ++ tailWord_999971) baseStart_999971 baseEnd_999971 := by
    simpa [prefixWord, tailWord_999971, baseEnd_999971] using wordTrace_append hprefix tailTrace_999971
  have hstable : (prefixWord ++ tailWord_999971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_999971).length < 2 ^ (prefixWord ++ tailWord_999971).sum := by decide
  have hdescent : baseEnd_999971 < baseStart_999971 := by decide
  rcases family_descends (prefixWord ++ tailWord_999971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000066 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1000066 : Nat := 118140960795 + 1000066 * 2 ^ 59
def prefixEnd_1000066 : Nat := 4983230072969 + 3 ^ 40 * 1000066 * 2
def baseEnd_1000066 : Nat := 57057171579932163430643

theorem tailTrace_1000066 : CollatzResearch.WordTrace tailWord_1000066 prefixEnd_1000066 57057171579932163430643 := by
  unfold tailWord_1000066
  simp only [CollatzResearch.WordTrace]
  refine ⟨9118850898734788630003013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24316935729959436346674701 9118850898734788630003013)
  ·
    refine ⟨1709784543512772868125565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9118850898734788630003013 1709784543512772868125565)
    ·
      refine ⟨641169203817289825547087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1709784543512772868125565 641169203817289825547087)
      ·
        refine ⟨961753805725934738320631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 641169203817289825547087 961753805725934738320631)
        ·
          refine ⟨1442630708588902107480947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 961753805725934738320631 1442630708588902107480947)
          ·
            refine ⟨2163946062883353161221421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1442630708588902107480947 2163946062883353161221421)
            ·
              refine ⟨811479773581257435458033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2163946062883353161221421 811479773581257435458033)
              ·
                refine ⟨608609830185943076593525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 811479773581257435458033 608609830185943076593525)
                ·
                  refine ⟨57057171579932163430643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 608609830185943076593525 57057171579932163430643)
                  ·
                    rfl

theorem cell23_1000066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1000066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000066 prefixEnd_1000066 := by exact prefixLift 1000066
  have htrace : WordTrace (prefixWord ++ tailWord_1000066) baseStart_1000066 baseEnd_1000066 := by
    simpa [prefixWord, tailWord_1000066, baseEnd_1000066] using wordTrace_append hprefix tailTrace_1000066
  have hstable : (prefixWord ++ tailWord_1000066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000066).length < 2 ^ (prefixWord ++ tailWord_1000066).sum := by decide
  have hdescent : baseEnd_1000066 < baseStart_1000066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000068 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_1000068 : Nat := 118140960795 + 1000068 * 2 ^ 59
def prefixEnd_1000068 : Nat := 4983230072969 + 3 ^ 40 * 1000068 * 2
def baseEnd_1000068 : Nat := 513515571180698463050777

theorem tailTrace_1000068 : CollatzResearch.WordTrace tailWord_1000068 prefixEnd_1000068 513515571180698463050777 := by
  unfold tailWord_1000068
  simp only [CollatzResearch.WordTrace]
  refine ⟨18237738270465954430792429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24316984360621272574389905 18237738270465954430792429)
  ·
    refine ⟨6839151851424732911547161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18237738270465954430792429 6839151851424732911547161)
    ·
      refine ⟨5129363888568549683660371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6839151851424732911547161 5129363888568549683660371)
      ·
        refine ⟨7694045832852824525490557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5129363888568549683660371 7694045832852824525490557)
        ·
          refine ⟨2885267187319809197058959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7694045832852824525490557 2885267187319809197058959)
          ·
            refine ⟨4327900780979713795588439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885267187319809197058959 4327900780979713795588439)
            ·
              refine ⟨6491851171469570693382659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4327900780979713795588439 6491851171469570693382659)
              ·
                refine ⟨9737776757204356040073989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6491851171469570693382659 9737776757204356040073989)
                ·
                  refine ⟨1825833141975816757513873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9737776757204356040073989 1825833141975816757513873)
                  ·
                    refine ⟨1369374856481862568135405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1825833141975816757513873 1369374856481862568135405)
                    ·
                      refine ⟨513515571180698463050777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1369374856481862568135405 513515571180698463050777)
                      ·
                        rfl

theorem cell23_1000068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_1000068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000068 prefixEnd_1000068 := by exact prefixLift 1000068
  have htrace : WordTrace (prefixWord ++ tailWord_1000068) baseStart_1000068 baseEnd_1000068 := by
    simpa [prefixWord, tailWord_1000068, baseEnd_1000068] using wordTrace_append hprefix tailTrace_1000068
  have hstable : (prefixWord ++ tailWord_1000068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000068).length < 2 ^ (prefixWord ++ tailWord_1000068).sum := by decide
  have hdescent : baseEnd_1000068 < baseStart_1000068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000071 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 6]
def baseStart_1000071 : Nat := 118140960795 + 1000071 * 2 ^ 59
def prefixEnd_1000071 : Nat := 4983230072969 + 3 ^ 40 * 1000071 * 2
def baseEnd_1000071 : Nat := 57057456846962439034807

theorem tailTrace_1000071 : CollatzResearch.WordTrace tailWord_1000071 prefixEnd_1000071 57057456846962439034807 := by
  unfold tailWord_1000071
  simp only [CollatzResearch.WordTrace]
  refine ⟨36475585959921040373944067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24317057306614026915962711 36475585959921040373944067)
  ·
    refine ⟨54713378939881560560916101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36475585959921040373944067 54713378939881560560916101)
    ·
      refine ⟨10258758551227792605171769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54713378939881560560916101 10258758551227792605171769)
      ·
        refine ⟨7694068913420844453878827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10258758551227792605171769 7694068913420844453878827)
        ·
          refine ⟨11541103370131266680818241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7694068913420844453878827 11541103370131266680818241)
          ·
            refine ⟨8655827527598450010613681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11541103370131266680818241 8655827527598450010613681)
            ·
              refine ⟨6491870645698837507960261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8655827527598450010613681 6491870645698837507960261)
              ·
                refine ⟨1217225746068532032742549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6491870645698837507960261 1217225746068532032742549)
                ·
                  refine ⟨57057456846962439034807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1217225746068532032742549 57057456846962439034807)
                  ·
                    rfl

theorem cell23_1000071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 6].length) (baseStart_1000071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000071 prefixEnd_1000071 := by exact prefixLift 1000071
  have htrace : WordTrace (prefixWord ++ tailWord_1000071) baseStart_1000071 baseEnd_1000071 := by
    simpa [prefixWord, tailWord_1000071, baseEnd_1000071] using wordTrace_append hprefix tailTrace_1000071
  have hstable : (prefixWord ++ tailWord_1000071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000071).length < 2 ^ (prefixWord ++ tailWord_1000071).sum := by decide
  have hdescent : baseEnd_1000071 < baseStart_1000071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000125 : List Nat := [1, 4, 1, 2, 1, 3, 2, 2, 2, 3, 2]
def baseStart_1000125 : Nat := 118140960795 + 1000125 * 2 ^ 59
def prefixEnd_1000125 : Nat := 4983230072969 + 3 ^ 40 * 1000125 * 2
def baseEnd_1000125 : Nat := 513544839578004740038015

theorem tailTrace_1000125 : CollatzResearch.WordTrace tailWord_1000125 prefixEnd_1000125 513544839578004740038015 := by
  unfold tailWord_1000125
  simp only [CollatzResearch.WordTrace]
  refine ⟨36477555501725407596409829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24318370334483605064273219 36477555501725407596409829)
  ·
    refine ⟨6839541656573513924326843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36477555501725407596409829 6839541656573513924326843)
    ·
      refine ⟨10259312484860270886490265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6839541656573513924326843 10259312484860270886490265)
      ·
        refine ⟨7694484363645203164867699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10259312484860270886490265 7694484363645203164867699)
        ·
          refine ⟨11541726545467804747301549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7694484363645203164867699 11541726545467804747301549)
          ·
            refine ⟨4328147454550426780238081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11541726545467804747301549 4328147454550426780238081)
            ·
              refine ⟨3246110590912820085178561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4328147454550426780238081 3246110590912820085178561)
              ·
                refine ⟨2434582943184615063883921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3246110590912820085178561 2434582943184615063883921)
                ·
                  refine ⟨1825937207388461297912941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2434582943184615063883921 1825937207388461297912941)
                  ·
                    refine ⟨684726452770672986717353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1825937207388461297912941 684726452770672986717353)
                    ·
                      refine ⟨513544839578004740038015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684726452770672986717353 513544839578004740038015)
                      ·
                        rfl

theorem cell23_1000125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_1000125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000125 prefixEnd_1000125 := by exact prefixLift 1000125
  have htrace : WordTrace (prefixWord ++ tailWord_1000125) baseStart_1000125 baseEnd_1000125 := by
    simpa [prefixWord, tailWord_1000125, baseEnd_1000125] using wordTrace_append hprefix tailTrace_1000125
  have hstable : (prefixWord ++ tailWord_1000125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000125).length < 2 ^ (prefixWord ++ tailWord_1000125).sum := by decide
  have hdescent : baseEnd_1000125 < baseStart_1000125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000138 : List Nat := [3, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4]
def baseStart_1000138 : Nat := 118140960795 + 1000138 * 2 ^ 59
def prefixEnd_1000138 : Nat := 4983230072969 + 3 ^ 40 * 1000138 * 2
def baseEnd_1000138 : Nat := 513551514826513189175455

theorem tailTrace_1000138 : CollatzResearch.WordTrace tailWord_1000138 prefixEnd_1000138 513551514826513189175455 := by
  unfold tailWord_1000138
  simp only [CollatzResearch.WordTrace]
  refine ⟨9119507412669577704158267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24318686433785540544422045 9119507412669577704158267)
  ·
    refine ⟨13679261119004366556237401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9119507412669577704158267 13679261119004366556237401)
    ·
      refine ⟨10259445839253274917178051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13679261119004366556237401 10259445839253274917178051)
      ·
        refine ⟨15389168758879912375767077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10259445839253274917178051 15389168758879912375767077)
        ·
          refine ⟨2885469142289983570456327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15389168758879912375767077 2885469142289983570456327)
          ·
            refine ⟨4328203713434975355684491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2885469142289983570456327 4328203713434975355684491)
            ·
              refine ⟨6492305570152463033526737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328203713434975355684491 6492305570152463033526737)
              ·
                refine ⟨4869229177614347275145053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6492305570152463033526737 4869229177614347275145053)
                ·
                  refine ⟨1825960941605380228179395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4869229177614347275145053 1825960941605380228179395)
                  ·
                    refine ⟨2738941412408070342269093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1825960941605380228179395 2738941412408070342269093)
                    ·
                      refine ⟨513551514826513189175455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2738941412408070342269093 513551514826513189175455)
                      ·
                        rfl

theorem cell23_1000138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_1000138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000138 prefixEnd_1000138 := by exact prefixLift 1000138
  have htrace : WordTrace (prefixWord ++ tailWord_1000138) baseStart_1000138 baseEnd_1000138 := by
    simpa [prefixWord, tailWord_1000138, baseEnd_1000138] using wordTrace_append hprefix tailTrace_1000138
  have hstable : (prefixWord ++ tailWord_1000138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000138).length < 2 ^ (prefixWord ++ tailWord_1000138).sum := by decide
  have hdescent : baseEnd_1000138 < baseStart_1000138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000175 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 3]
def baseStart_1000175 : Nat := 118140960795 + 1000175 * 2 ^ 59
def prefixEnd_1000175 : Nat := 4983230072969 + 3 ^ 40 * 1000175 * 2
def baseEnd_1000175 : Nat := 513570513610729544412785

theorem tailTrace_1000175 : CollatzResearch.WordTrace tailWord_1000175 prefixEnd_1000175 513570513610729544412785 := by
  unfold tailWord_1000175
  simp only [CollatzResearch.WordTrace]
  refine ⟨36479379151544266135729979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24319586101029510757153319 36479379151544266135729979)
  ·
    refine ⟨54719068727316399203594969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36479379151544266135729979 54719068727316399203594969)
    ·
      refine ⟨41039301545487299402696227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54719068727316399203594969 41039301545487299402696227)
      ·
        refine ⟨61558952318230949104044341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41039301545487299402696227 61558952318230949104044341)
        ·
          refine ⟨5771151779834151478504157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 61558952318230949104044341 5771151779834151478504157)
          ·
            refine ⟨2164181917437806804439059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5771151779834151478504157 2164181917437806804439059)
            ·
              refine ⟨3246272876156710206658589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2164181917437806804439059 3246272876156710206658589)
              ·
                refine ⟨1217352328558766327496971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3246272876156710206658589 1217352328558766327496971)
                ·
                  refine ⟨1826028492838149491245457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217352328558766327496971 1826028492838149491245457)
                  ·
                    refine ⟨1369521369628612118434093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1826028492838149491245457 1369521369628612118434093)
                    ·
                      refine ⟨513570513610729544412785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1369521369628612118434093 513570513610729544412785)
                      ·
                        rfl

theorem cell23_1000175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 3].length) (baseStart_1000175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000175 prefixEnd_1000175 := by exact prefixLift 1000175
  have htrace : WordTrace (prefixWord ++ tailWord_1000175) baseStart_1000175 baseEnd_1000175 := by
    simpa [prefixWord, tailWord_1000175, baseEnd_1000175] using wordTrace_append hprefix tailTrace_1000175
  have hstable : (prefixWord ++ tailWord_1000175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000175).length < 2 ^ (prefixWord ++ tailWord_1000175).sum := by decide
  have hdescent : baseEnd_1000175 < baseStart_1000175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000232 : List Nat := [2, 1, 5, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_1000232 : Nat := 118140960795 + 1000232 * 2 ^ 59
def prefixEnd_1000232 : Nat := 4983230072969 + 3 ^ 40 * 1000232 * 2
def baseEnd_1000232 : Nat := 513599782008035821400023

theorem tailTrace_1000232 : CollatzResearch.WordTrace tailWord_1000232 prefixEnd_1000232 513599782008035821400023 := by
  unfold tailWord_1000232
  simp only [CollatzResearch.WordTrace]
  refine ⟨18240729056168882435277475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24320972074891843247036633 18240729056168882435277475)
  ·
    refine ⟨27361093584253323652916213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18240729056168882435277475 27361093584253323652916213)
    ·
      refine ⟨2565102523523749092460895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27361093584253323652916213 2565102523523749092460895)
      ·
        refine ⟨3847653785285623638691343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565102523523749092460895 3847653785285623638691343)
        ·
          refine ⟨5771480677928435458037015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3847653785285623638691343 5771480677928435458037015)
          ·
            refine ⟨8657221016892653187055523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5771480677928435458037015 8657221016892653187055523)
            ·
              refine ⟨12985831525338979780583285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8657221016892653187055523 12985831525338979780583285)
              ·
                refine ⟨1217421705500529354429683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12985831525338979780583285 1217421705500529354429683)
                ·
                  refine ⟨1826132558250794031644525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217421705500529354429683 1826132558250794031644525)
                  ·
                    refine ⟨684799709344047761866697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1826132558250794031644525 684799709344047761866697)
                    ·
                      refine ⟨513599782008035821400023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684799709344047761866697 513599782008035821400023)
                      ·
                        rfl

theorem cell23_1000232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_1000232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000232 prefixEnd_1000232 := by exact prefixLift 1000232
  have htrace : WordTrace (prefixWord ++ tailWord_1000232) baseStart_1000232 baseEnd_1000232 := by
    simpa [prefixWord, tailWord_1000232, baseEnd_1000232] using wordTrace_append hprefix tailTrace_1000232
  have hstable : (prefixWord ++ tailWord_1000232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000232).length < 2 ^ (prefixWord ++ tailWord_1000232).sum := by decide
  have hdescent : baseEnd_1000232 < baseStart_1000232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000248 : List Nat := [2, 1, 2, 1, 3, 2, 2, 1, 2, 4, 3]
def baseStart_1000248 : Nat := 118140960795 + 1000248 * 2 ^ 59
def prefixEnd_1000248 : Nat := 4983230072969 + 3 ^ 40 * 1000248 * 2
def baseEnd_1000248 : Nat := 513607997698507758799949

theorem tailTrace_1000248 : CollatzResearch.WordTrace tailWord_1000248 prefixEnd_1000248 513607997698507758799949 := by
  unfold tailWord_1000248
  simp only [CollatzResearch.WordTrace]
  refine ⟨18241020840139899801568699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24321361120186533068758265 18241020840139899801568699)
  ·
    refine ⟨27361531260209849702353049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18241020840139899801568699 27361531260209849702353049)
    ·
      refine ⟨20521148445157387276764787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27361531260209849702353049 20521148445157387276764787)
      ·
        refine ⟨30781722667736080915147181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20521148445157387276764787 30781722667736080915147181)
        ·
          refine ⟨11543146000401030343180193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30781722667736080915147181 11543146000401030343180193)
          ·
            refine ⟨8657359500300772757385145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11543146000401030343180193 8657359500300772757385145)
            ·
              refine ⟨6493019625225579568038859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8657359500300772757385145 6493019625225579568038859)
              ·
                refine ⟨9739529437838369352058289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493019625225579568038859 9739529437838369352058289)
                ·
                  refine ⟨7304647078378777014043717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9739529437838369352058289 7304647078378777014043717)
                  ·
                    refine ⟨1369621327196020690133197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7304647078378777014043717 1369621327196020690133197)
                    ·
                      refine ⟨513607997698507758799949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1369621327196020690133197 513607997698507758799949)
                      ·
                        rfl

theorem cell23_1000248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_1000248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000248 prefixEnd_1000248 := by exact prefixLift 1000248
  have htrace : WordTrace (prefixWord ++ tailWord_1000248) baseStart_1000248 baseEnd_1000248 := by
    simpa [prefixWord, tailWord_1000248, baseEnd_1000248] using wordTrace_append hprefix tailTrace_1000248
  have hstable : (prefixWord ++ tailWord_1000248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000248).length < 2 ^ (prefixWord ++ tailWord_1000248).sum := by decide
  have hdescent : baseEnd_1000248 < baseStart_1000248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000271 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 8]
def baseStart_1000271 : Nat := 118140960795 + 1000271 * 2 ^ 59
def prefixEnd_1000271 : Nat := 4983230072969 + 3 ^ 40 * 1000271 * 2
def baseEnd_1000271 : Nat := 513619807753561168812343

theorem tailTrace_1000271 : CollatzResearch.WordTrace tailWord_1000271 prefixEnd_1000271 513619807753561168812343 := by
  unfold tailWord_1000271
  simp only [CollatzResearch.WordTrace]
  refine ⟨36482880559196474531224667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24321920372797649687483111 36482880559196474531224667)
  ·
    refine ⟨54724320838794711796837001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36482880559196474531224667 54724320838794711796837001)
    ·
      refine ⟨41043240629096033847627751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54724320838794711796837001 41043240629096033847627751)
      ·
        refine ⟨61564860943644050771441627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41043240629096033847627751 61564860943644050771441627)
        ·
          refine ⟨92347291415466076157162441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61564860943644050771441627 92347291415466076157162441)
          ·
            refine ⟨69260468561599557117871831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92347291415466076157162441 69260468561599557117871831)
            ·
              refine ⟨103890702842399335676807747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69260468561599557117871831 103890702842399335676807747)
              ·
                refine ⟨155836054263599003515211621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 103890702842399335676807747 155836054263599003515211621)
                ·
                  refine ⟨29219260174424813159102179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155836054263599003515211621 29219260174424813159102179)
                  ·
                    refine ⟨43828890261637219738653269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29219260174424813159102179 43828890261637219738653269)
                    ·
                      refine ⟨513619807753561168812343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43828890261637219738653269 513619807753561168812343)
                      ·
                        rfl

theorem cell23_1000271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_1000271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000271 prefixEnd_1000271 := by exact prefixLift 1000271
  have htrace : WordTrace (prefixWord ++ tailWord_1000271) baseStart_1000271 baseEnd_1000271 := by
    simpa [prefixWord, tailWord_1000271, baseEnd_1000271] using wordTrace_append hprefix tailTrace_1000271
  have hstable : (prefixWord ++ tailWord_1000271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000271).length < 2 ^ (prefixWord ++ tailWord_1000271).sum := by decide
  have hdescent : baseEnd_1000271 < baseStart_1000271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000305 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 2, 5, 2]
def baseStart_1000305 : Nat := 118140960795 + 1000305 * 2 ^ 59
def prefixEnd_1000305 : Nat := 4983230072969 + 3 ^ 40 * 1000305 * 2
def baseEnd_1000305 : Nat := 513637266095814035787187

theorem tailTrace_1000305 : CollatzResearch.WordTrace tailWord_1000305 prefixEnd_1000305 513637266095814035787187 := by
  unfold tailWord_1000305
  simp only [CollatzResearch.WordTrace]
  refine ⟨36484120641073298337962369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24322747094048865558641579 36484120641073298337962369)
  ·
    refine ⟨27363090480804973753471777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36484120641073298337962369 27363090480804973753471777)
    ·
      refine ⟨20522317860603730315103833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27363090480804973753471777 20522317860603730315103833)
      ·
        refine ⟨15391738395452797736327875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20522317860603730315103833 15391738395452797736327875)
        ·
          refine ⟨23087607593179196604491813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15391738395452797736327875 23087607593179196604491813)
          ·
            refine ⟨4328926423721099363342215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23087607593179196604491813 4328926423721099363342215)
            ·
              refine ⟨6493389635581649045013323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4328926423721099363342215 6493389635581649045013323)
              ·
                refine ⟨9740084453372473567519985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6493389635581649045013323 9740084453372473567519985)
                ·
                  refine ⟨7305063340029355175639989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9740084453372473567519985 7305063340029355175639989)
                  ·
                    refine ⟨684849688127752047716249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7305063340029355175639989 684849688127752047716249)
                    ·
                      refine ⟨513637266095814035787187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684849688127752047716249 513637266095814035787187)
                      ·
                        rfl

theorem cell23_1000305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_1000305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000305 prefixEnd_1000305 := by exact prefixLift 1000305
  have htrace : WordTrace (prefixWord ++ tailWord_1000305) baseStart_1000305 baseEnd_1000305 := by
    simpa [prefixWord, tailWord_1000305, baseEnd_1000305] using wordTrace_append hprefix tailTrace_1000305
  have hstable : (prefixWord ++ tailWord_1000305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000305).length < 2 ^ (prefixWord ++ tailWord_1000305).sum := by decide
  have hdescent : baseEnd_1000305 < baseStart_1000305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000355 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 3]
def baseStart_1000355 : Nat := 118140960795 + 1000355 * 2 ^ 59
def prefixEnd_1000355 : Nat := 4983230072969 + 3 ^ 40 * 1000355 * 2
def baseEnd_1000355 : Nat := 513662940128538840161957

theorem tailTrace_1000355 : CollatzResearch.WordTrace tailWord_1000355 prefixEnd_1000355 513662940128538840161957 := by
  unfold tailWord_1000355
  simp only [CollatzResearch.WordTrace]
  refine ⟨36485944290892156877282519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24323962860594771251521679 36485944290892156877282519)
  ·
    refine ⟨54728916436338235315923779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36485944290892156877282519 54728916436338235315923779)
    ·
      refine ⟨82093374654507352973885669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54728916436338235315923779 82093374654507352973885669)
      ·
        refine ⟨15392507747720128682603563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82093374654507352973885669 15392507747720128682603563)
        ·
          refine ⟨23088761621580193023905345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15392507747720128682603563 23088761621580193023905345)
          ·
            refine ⟨17316571216185144767929009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23088761621580193023905345 17316571216185144767929009)
            ·
              refine ⟨12987428412138858575946757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17316571216185144767929009 12987428412138858575946757)
              ·
                refine ⟨2435142827276035982990017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12987428412138858575946757 2435142827276035982990017)
                ·
                  refine ⟨1826357120457026987242513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2435142827276035982990017 1826357120457026987242513)
                  ·
                    refine ⟨1369767840342770240431885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1826357120457026987242513 1369767840342770240431885)
                    ·
                      refine ⟨513662940128538840161957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1369767840342770240431885 513662940128538840161957)
                      ·
                        rfl

theorem cell23_1000355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 3].length) (baseStart_1000355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000355 prefixEnd_1000355 := by exact prefixLift 1000355
  have htrace : WordTrace (prefixWord ++ tailWord_1000355) baseStart_1000355 baseEnd_1000355 := by
    simpa [prefixWord, tailWord_1000355, baseEnd_1000355] using wordTrace_append hprefix tailTrace_1000355
  have hstable : (prefixWord ++ tailWord_1000355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000355).length < 2 ^ (prefixWord ++ tailWord_1000355).sum := by decide
  have hdescent : baseEnd_1000355 < baseStart_1000355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000378 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6]
def baseStart_1000378 : Nat := 118140960795 + 1000378 * 2 ^ 59
def prefixEnd_1000378 : Nat := 4983230072969 + 3 ^ 40 * 1000378 * 2
def baseEnd_1000378 : Nat := 513674750183592250174351

theorem tailTrace_1000378 : CollatzResearch.WordTrace tailWord_1000378 prefixEnd_1000378 513674750183592250174351 := by
  unfold tailWord_1000378
  simp only [CollatzResearch.WordTrace]
  refine ⟨9121695792452207951342447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24324522113205887870246525 9121695792452207951342447)
  ·
    refine ⟨13682543688678311927013671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9121695792452207951342447 13682543688678311927013671)
    ·
      refine ⟨20523815533017467890520507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13682543688678311927013671 20523815533017467890520507)
      ·
        refine ⟨30785723299526201835780761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20523815533017467890520507 30785723299526201835780761)
        ·
          refine ⟨23089292474644651376835571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30785723299526201835780761 23089292474644651376835571)
          ·
            refine ⟨34633938711966977065253357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23089292474644651376835571 34633938711966977065253357)
            ·
              refine ⟨12987727016987616399470009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34633938711966977065253357 12987727016987616399470009)
              ·
                refine ⟨9740795262740712299602507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12987727016987616399470009 9740795262740712299602507)
                ·
                  refine ⟨14611192894111068449403761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9740795262740712299602507 14611192894111068449403761)
                  ·
                    refine ⟨10958394670583301337052821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14611192894111068449403761 10958394670583301337052821)
                    ·
                      refine ⟨513674750183592250174351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10958394670583301337052821 513674750183592250174351)
                      ·
                        rfl

theorem cell23_1000378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_1000378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000378 prefixEnd_1000378 := by exact prefixLift 1000378
  have htrace : WordTrace (prefixWord ++ tailWord_1000378) baseStart_1000378 baseEnd_1000378 := by
    simpa [prefixWord, tailWord_1000378, baseEnd_1000378] using wordTrace_append hprefix tailTrace_1000378
  have hstable : (prefixWord ++ tailWord_1000378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000378).length < 2 ^ (prefixWord ++ tailWord_1000378).sum := by decide
  have hdescent : baseEnd_1000378 < baseStart_1000378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000459 : List Nat := [1, 1, 1, 1, 6, 3, 3, 1, 1, 1, 4]
def baseStart_1000459 : Nat := 118140960795 + 1000459 * 2 ^ 59
def prefixEnd_1000459 : Nat := 4983230072969 + 3 ^ 40 * 1000459 * 2
def baseEnd_1000459 : Nat := 513716342116606433261479

theorem tailTrace_1000459 : CollatzResearch.WordTrace tailWord_1000459 prefixEnd_1000459 513716342116606433261479 := by
  unfold tailWord_1000459
  simp only [CollatzResearch.WordTrace]
  refine ⟨36489737482515382639068431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24326491655010255092712287 36489737482515382639068431)
  ·
    refine ⟨54734606223773073958602647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36489737482515382639068431 54734606223773073958602647)
    ·
      refine ⟨82101909335659610937903971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54734606223773073958602647 82101909335659610937903971)
      ·
        refine ⟨123152864003489416406855957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82101909335659610937903971 123152864003489416406855957)
        ·
          refine ⟨5772790500163566394071373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123152864003489416406855957 5772790500163566394071373)
          ·
            refine ⟨2164796437561337397776765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5772790500163566394071373 2164796437561337397776765)
            ·
              refine ⟨811798664085501524166287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2164796437561337397776765 811798664085501524166287)
              ·
                refine ⟨1217697996128252286249431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811798664085501524166287 1217697996128252286249431)
                ·
                  refine ⟨1826546994192378429374147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217697996128252286249431 1826546994192378429374147)
                  ·
                    refine ⟨2739820491288567644061221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1826546994192378429374147 2739820491288567644061221)
                    ·
                      refine ⟨513716342116606433261479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2739820491288567644061221 513716342116606433261479)
                      ·
                        rfl

theorem cell23_1000459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 3, 1, 1, 1, 4].length) (baseStart_1000459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000459 prefixEnd_1000459 := by exact prefixLift 1000459
  have htrace : WordTrace (prefixWord ++ tailWord_1000459) baseStart_1000459 baseEnd_1000459 := by
    simpa [prefixWord, tailWord_1000459, baseEnd_1000459] using wordTrace_append hprefix tailTrace_1000459
  have hstable : (prefixWord ++ tailWord_1000459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000459).length < 2 ^ (prefixWord ++ tailWord_1000459).sum := by decide
  have hdescent : baseEnd_1000459 < baseStart_1000459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000462 : List Nat := [4, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5]
def baseStart_1000462 : Nat := 118140960795 + 1000462 * 2 ^ 59
def prefixEnd_1000462 : Nat := 4983230072969 + 3 ^ 40 * 1000462 * 2
def baseEnd_1000462 : Nat := 513717882558569921523965

theorem tailTrace_1000462 : CollatzResearch.WordTrace tailWord_1000462 prefixEnd_1000462 513717882558569921523965 := by
  unfold tailWord_1000462
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561230862688064268928455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24326564601003009434285093 4561230862688064268928455)
  ·
    refine ⟨6841846294032096403392683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4561230862688064268928455 6841846294032096403392683)
    ·
      refine ⟨10262769441048144605089025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6841846294032096403392683 10262769441048144605089025)
      ·
        refine ⟨7697077080786108453816769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10262769441048144605089025 7697077080786108453816769)
        ·
          refine ⟨5772807810589581340362577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7697077080786108453816769 5772807810589581340362577)
          ·
            refine ⟨4329605857942186005271933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5772807810589581340362577 4329605857942186005271933)
            ·
              refine ⟨1623602196728319751976975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4329605857942186005271933 1623602196728319751976975)
              ·
                refine ⟨2435403295092479627965463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623602196728319751976975 2435403295092479627965463)
                ·
                  refine ⟨3653104942638719441948195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435403295092479627965463 3653104942638719441948195)
                  ·
                    refine ⟨5479657413958079162922293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3653104942638719441948195 5479657413958079162922293)
                    ·
                      refine ⟨513717882558569921523965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5479657413958079162922293 513717882558569921523965)
                      ·
                        rfl

theorem cell23_1000462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_1000462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000462 prefixEnd_1000462 := by exact prefixLift 1000462
  have htrace : WordTrace (prefixWord ++ tailWord_1000462) baseStart_1000462 baseEnd_1000462 := by
    simpa [prefixWord, tailWord_1000462, baseEnd_1000462] using wordTrace_append hprefix tailTrace_1000462
  have hstable : (prefixWord ++ tailWord_1000462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000462).length < 2 ^ (prefixWord ++ tailWord_1000462).sum := by decide
  have hdescent : baseEnd_1000462 < baseStart_1000462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000469 : List Nat := [1, 3, 2, 1, 4, 2, 2, 2, 2, 4]
def baseStart_1000469 : Nat := 118140960795 + 1000469 * 2 ^ 59
def prefixEnd_1000469 : Nat := 4983230072969 + 3 ^ 40 * 1000469 * 2
def baseEnd_1000469 : Nat := 171240492307717131378811

theorem tailTrace_1000469 : CollatzResearch.WordTrace tailWord_1000469 prefixEnd_1000469 171240492307717131378811 := by
  unfold tailWord_1000469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36490102212479154346932461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24326734808319436231288307 36490102212479154346932461)
  ·
    refine ⟨13683788329679682880099673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36490102212479154346932461 13683788329679682880099673)
    ·
      refine ⟨10262841247259762160074755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13683788329679682880099673 10262841247259762160074755)
      ·
        refine ⟨15394261870889643240112133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10262841247259762160074755 15394261870889643240112133)
        ·
          refine ⟨2886424100791808107521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15394261870889643240112133 2886424100791808107521025)
          ·
            refine ⟨2164818075593856080640769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886424100791808107521025 2164818075593856080640769)
            ·
              refine ⟨1623613556695392060480577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164818075593856080640769 1623613556695392060480577)
              ·
                refine ⟨1217710167521544045360433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1623613556695392060480577 1217710167521544045360433)
                ·
                  refine ⟨913282625641158034020325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1217710167521544045360433 913282625641158034020325)
                  ·
                    refine ⟨171240492307717131378811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913282625641158034020325 171240492307717131378811)
                    ·
                      rfl

theorem cell23_1000469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2, 4].length) (baseStart_1000469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000469 prefixEnd_1000469 := by exact prefixLift 1000469
  have htrace : WordTrace (prefixWord ++ tailWord_1000469) baseStart_1000469 baseEnd_1000469 := by
    simpa [prefixWord, tailWord_1000469, baseEnd_1000469] using wordTrace_append hprefix tailTrace_1000469
  have hstable : (prefixWord ++ tailWord_1000469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000469).length < 2 ^ (prefixWord ++ tailWord_1000469).sum := by decide
  have hdescent : baseEnd_1000469 < baseStart_1000469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000482 : List Nat := [3, 3, 1, 1, 1, 5, 1, 8]
def baseStart_1000482 : Nat := 118140960795 + 1000482 * 2 ^ 59
def prefixEnd_1000482 : Nat := 4983230072969 + 3 ^ 40 * 1000482 * 2
def baseEnd_1000482 : Nat := 19026968598950364565699

theorem tailTrace_1000482 : CollatzResearch.WordTrace tailWord_1000482 prefixEnd_1000482 19026968598950364565699 := by
  unfold tailWord_1000482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9122644090358014391788925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24327050907621371711437133 9122644090358014391788925)
  ·
    refine ⟨3420991533884255396920847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9122644090358014391788925 3420991533884255396920847)
    ·
      refine ⟨5131487300826383095381271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3420991533884255396920847 5131487300826383095381271)
      ·
        refine ⟨7697230951239574643071907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5131487300826383095381271 7697230951239574643071907)
        ·
          refine ⟨11545846426859361964607861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7697230951239574643071907 11545846426859361964607861)
          ·
            refine ⟨1082423102518065184181987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11545846426859361964607861 1082423102518065184181987)
            ·
              refine ⟨1623634653777097776272981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082423102518065184181987 1623634653777097776272981)
              ·
                refine ⟨19026968598950364565699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1623634653777097776272981 19026968598950364565699)
                ·
                  rfl

theorem cell23_1000482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 8].length) (baseStart_1000482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000482 prefixEnd_1000482 := by exact prefixLift 1000482
  have htrace : WordTrace (prefixWord ++ tailWord_1000482) baseStart_1000482 baseEnd_1000482 := by
    simpa [prefixWord, tailWord_1000482, baseEnd_1000482] using wordTrace_append hprefix tailTrace_1000482
  have hstable : (prefixWord ++ tailWord_1000482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000482).length < 2 ^ (prefixWord ++ tailWord_1000482).sum := by decide
  have hdescent : baseEnd_1000482 < baseStart_1000482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000492 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 3]
def baseStart_1000492 : Nat := 118140960795 + 1000492 * 2 ^ 59
def prefixEnd_1000492 : Nat := 4983230072969 + 3 ^ 40 * 1000492 * 2
def baseEnd_1000492 : Nat := 513733286978204804148827

theorem tailTrace_1000492 : CollatzResearch.WordTrace tailWord_1000492 prefixEnd_1000492 513733286978204804148827 := by
  unfold tailWord_1000492
  simp only [CollatzResearch.WordTrace]
  refine ⟨18245470545697914637509865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24327294060930552850013153 18245470545697914637509865)
  ·
    refine ⟨13684102909273435978132399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18245470545697914637509865 13684102909273435978132399)
    ·
      refine ⟨20526154363910153967198599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13684102909273435978132399 20526154363910153967198599)
      ·
        refine ⟨30789231545865230950797899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20526154363910153967198599 30789231545865230950797899)
        ·
          refine ⟨46183847318797846426196849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30789231545865230950797899 46183847318797846426196849)
          ·
            refine ⟨34637885489098384819647637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46183847318797846426196849 34637885489098384819647637)
            ·
              refine ⟨1623650882301486788420983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 34637885489098384819647637 1623650882301486788420983)
              ·
                refine ⟨2435476323452230182631475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1623650882301486788420983 2435476323452230182631475)
                ·
                  refine ⟨3653214485178345273947213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2435476323452230182631475 3653214485178345273947213)
                  ·
                    refine ⟨1369955431941879477730205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3653214485178345273947213 1369955431941879477730205)
                    ·
                      refine ⟨513733286978204804148827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1369955431941879477730205 513733286978204804148827)
                      ·
                        rfl

theorem cell23_1000492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 3].length) (baseStart_1000492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000492 prefixEnd_1000492 := by exact prefixLift 1000492
  have htrace : WordTrace (prefixWord ++ tailWord_1000492) baseStart_1000492 baseEnd_1000492 := by
    simpa [prefixWord, tailWord_1000492, baseEnd_1000492] using wordTrace_append hprefix tailTrace_1000492
  have hstable : (prefixWord ++ tailWord_1000492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000492).length < 2 ^ (prefixWord ++ tailWord_1000492).sum := by decide
  have hdescent : baseEnd_1000492 < baseStart_1000492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000510 : List Nat := [4, 2, 1, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_1000510 : Nat := 118140960795 + 1000510 * 2 ^ 59
def prefixEnd_1000510 : Nat := 4983230072969 + 3 ^ 40 * 1000510 * 2
def baseEnd_1000510 : Nat := 513742529629985733723745

theorem tailTrace_1000510 : CollatzResearch.WordTrace tailWord_1000510 prefixEnd_1000510 513742529629985733723745 := by
  unfold tailWord_1000510
  simp only [CollatzResearch.WordTrace]
  refine ⟨4561449700666327293646873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24327731736887078899449989 4561449700666327293646873)
  ·
    refine ⟨3421087275499745470235155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4561449700666327293646873 3421087275499745470235155)
    ·
      refine ⟨5131630913249618205352733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421087275499745470235155 5131630913249618205352733)
      ·
        refine ⟨1924361592468606827007275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5131630913249618205352733 1924361592468606827007275)
        ·
          refine ⟨2886542388702910240510913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924361592468606827007275 2886542388702910240510913)
          ·
            refine ⟨2164906791527182680383185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2886542388702910240510913 2164906791527182680383185)
            ·
              refine ⟨1623680093645387010287389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2164906791527182680383185 1623680093645387010287389)
              ·
                refine ⟨608880035117020128857771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1623680093645387010287389 608880035117020128857771)
                ·
                  refine ⟨913320052675530193286657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 608880035117020128857771 913320052675530193286657)
                  ·
                    refine ⟨684990039506647644964993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 913320052675530193286657 684990039506647644964993)
                    ·
                      refine ⟨513742529629985733723745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 684990039506647644964993 513742529629985733723745)
                      ·
                        rfl

theorem cell23_1000510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_1000510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000510 prefixEnd_1000510 := by exact prefixLift 1000510
  have htrace : WordTrace (prefixWord ++ tailWord_1000510) baseStart_1000510 baseEnd_1000510 := by
    simpa [prefixWord, tailWord_1000510, baseEnd_1000510] using wordTrace_append hprefix tailTrace_1000510
  have hstable : (prefixWord ++ tailWord_1000510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000510).length < 2 ^ (prefixWord ++ tailWord_1000510).sum := by decide
  have hdescent : baseEnd_1000510 < baseStart_1000510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000513 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1000513 : Nat := 118140960795 + 1000513 * 2 ^ 59
def prefixEnd_1000513 : Nat := 4983230072969 + 3 ^ 40 * 1000513 * 2
def baseEnd_1000513 : Nat := 513744070071949221986231

theorem tailTrace_1000513 : CollatzResearch.WordTrace tailWord_1000513 prefixEnd_1000513 513744070071949221986231 := by
  unfold tailWord_1000513
  simp only [CollatzResearch.WordTrace]
  refine ⟨36491707024319749861534193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24327804682879833241022795 36491707024319749861534193)
  ·
    refine ⟨27368780268239812396150645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36491707024319749861534193 27368780268239812396150645)
    ·
      refine ⟨2565823150147482412139123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27368780268239812396150645 2565823150147482412139123)
      ·
        refine ⟨3848734725221223618208685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2565823150147482412139123 3848734725221223618208685)
        ·
          refine ⟨1443275521957958856828257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3848734725221223618208685 1443275521957958856828257)
          ·
            refine ⟨1082456641468469142621193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1443275521957958856828257 1082456641468469142621193)
            ·
              refine ⟨811842481101351856965895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082456641468469142621193 811842481101351856965895)
              ·
                refine ⟨1217763721652027785448843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811842481101351856965895 1217763721652027785448843)
                ·
                  refine ⟨1826645582478041678173265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1217763721652027785448843 1826645582478041678173265)
                  ·
                    refine ⟨1369984186858531258629949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1826645582478041678173265 1369984186858531258629949)
                    ·
                      refine ⟨513744070071949221986231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1369984186858531258629949 513744070071949221986231)
                      ·
                        rfl

theorem cell23_1000513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1000513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000513 prefixEnd_1000513 := by exact prefixLift 1000513
  have htrace : WordTrace (prefixWord ++ tailWord_1000513) baseStart_1000513 baseEnd_1000513 := by
    simpa [prefixWord, tailWord_1000513, baseEnd_1000513] using wordTrace_append hprefix tailTrace_1000513
  have hstable : (prefixWord ++ tailWord_1000513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000513).length < 2 ^ (prefixWord ++ tailWord_1000513).sum := by decide
  have hdescent : baseEnd_1000513 < baseStart_1000513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000535 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1000535 : Nat := 118140960795 + 1000535 * 2 ^ 59
def prefixEnd_1000535 : Nat := 4983230072969 + 3 ^ 40 * 1000535 * 2
def baseEnd_1000535 : Nat := 513755366646348135911129

theorem tailTrace_1000535 : CollatzResearch.WordTrace tailWord_1000535 prefixEnd_1000535 513755366646348135911129 := by
  unfold tailWord_1000535
  simp only [CollatzResearch.WordTrace]
  refine ⟨36492509430240047618835059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24328339620160031745890039 36492509430240047618835059)
  ·
    refine ⟨54738764145360071428252589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36492509430240047618835059 54738764145360071428252589)
    ·
      refine ⟨20527036554510026785594721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54738764145360071428252589 20527036554510026785594721)
      ·
        refine ⟨15395277415882520089196041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20527036554510026785594721 15395277415882520089196041)
        ·
          refine ⟨11546458061911890066897031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15395277415882520089196041 11546458061911890066897031)
          ·
            refine ⟨17319687092867835100345547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11546458061911890066897031 17319687092867835100345547)
            ·
              refine ⟨25979530639301752650518321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17319687092867835100345547 25979530639301752650518321)
              ·
                refine ⟨19484647979476314487888741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25979530639301752650518321 19484647979476314487888741)
                ·
                  refine ⟨3653371496151808966479139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19484647979476314487888741 3653371496151808966479139)
                  ·
                    refine ⟨5480057244227713449718709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3653371496151808966479139 5480057244227713449718709)
                    ·
                      refine ⟨513755366646348135911129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5480057244227713449718709 513755366646348135911129)
                      ·
                        rfl

theorem cell23_1000535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1000535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000535 prefixEnd_1000535 := by exact prefixLift 1000535
  have htrace : WordTrace (prefixWord ++ tailWord_1000535) baseStart_1000535 baseEnd_1000535 := by
    simpa [prefixWord, tailWord_1000535, baseEnd_1000535] using wordTrace_append hprefix tailTrace_1000535
  have hstable : (prefixWord ++ tailWord_1000535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000535).length < 2 ^ (prefixWord ++ tailWord_1000535).sum := by decide
  have hdescent : baseEnd_1000535 < baseStart_1000535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000566 : List Nat := [5, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_1000566 : Nat := 118140960795 + 1000566 * 2 ^ 59
def prefixEnd_1000566 : Nat := 4983230072969 + 3 ^ 40 * 1000566 * 2
def baseEnd_1000566 : Nat := 513771284546637514623487

theorem tailTrace_1000566 : CollatzResearch.WordTrace tailWord_1000566 prefixEnd_1000566 513771284546637514623487 := by
  unfold tailWord_1000566
  simp only [CollatzResearch.WordTrace]
  refine ⟨2280852505820483744575847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24329093395418493275475701 2280852505820483744575847)
  ·
    refine ⟨3421278758730725616863771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2280852505820483744575847 3421278758730725616863771)
    ·
      refine ⟨5131918138096088425295657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421278758730725616863771 5131918138096088425295657)
      ·
        refine ⟨3848938603572066318971743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5131918138096088425295657 3848938603572066318971743)
        ·
          refine ⟨5773407905358099478457615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3848938603572066318971743 5773407905358099478457615)
          ·
            refine ⟨8660111858037149217686423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5773407905358099478457615 8660111858037149217686423)
            ·
              refine ⟨12990167787055723826529635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8660111858037149217686423 12990167787055723826529635)
              ·
                refine ⟨19485251680583585739794453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12990167787055723826529635 19485251680583585739794453)
                ·
                  refine ⟨913371172527355581552865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19485251680583585739794453 913371172527355581552865)
                  ·
                    refine ⟨685028379395516686164649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 913371172527355581552865 685028379395516686164649)
                    ·
                      refine ⟨513771284546637514623487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685028379395516686164649 513771284546637514623487)
                      ·
                        rfl

theorem cell23_1000566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_1000566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000566 prefixEnd_1000566 := by exact prefixLift 1000566
  have htrace : WordTrace (prefixWord ++ tailWord_1000566) baseStart_1000566 baseEnd_1000566 := by
    simpa [prefixWord, tailWord_1000566, baseEnd_1000566] using wordTrace_append hprefix tailTrace_1000566
  have hstable : (prefixWord ++ tailWord_1000566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000566).length < 2 ^ (prefixWord ++ tailWord_1000566).sum := by decide
  have hdescent : baseEnd_1000566 < baseStart_1000566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000595 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7]
def baseStart_1000595 : Nat := 118140960795 + 1000595 * 2 ^ 59
def prefixEnd_1000595 : Nat := 4983230072969 + 3 ^ 40 * 1000595 * 2
def baseEnd_1000595 : Nat := 513786175485617901160853

theorem tailTrace_1000595 : CollatzResearch.WordTrace tailWord_1000595 prefixEnd_1000595 513786175485617901160853 := by
  unfold tailWord_1000595
  simp only [CollatzResearch.WordTrace]
  refine ⟨36494697810022677866019239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24329798540015118577346159 36494697810022677866019239)
  ·
    refine ⟨54742046715034016799028859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36494697810022677866019239 54742046715034016799028859)
    ·
      refine ⟨82113070072551025198543289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54742046715034016799028859 82113070072551025198543289)
      ·
        refine ⟨61584802554413268898907467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82113070072551025198543289 61584802554413268898907467)
        ·
          refine ⟨92377203831619903348361201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61584802554413268898907467 92377203831619903348361201)
          ·
            refine ⟨69282902873714927511270901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92377203831619903348361201 69282902873714927511270901)
            ·
              refine ⟨6495272144410774454181647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69282902873714927511270901 6495272144410774454181647)
              ·
                refine ⟨9742908216616161681272471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6495272144410774454181647 9742908216616161681272471)
                ·
                  refine ⟨14614362324924242521908707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9742908216616161681272471 14614362324924242521908707)
                  ·
                    refine ⟨21921543487386363782863061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14614362324924242521908707 21921543487386363782863061)
                    ·
                      refine ⟨513786175485617901160853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21921543487386363782863061 513786175485617901160853)
                      ·
                        rfl

theorem cell23_1000595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 7].length) (baseStart_1000595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000595 prefixEnd_1000595 := by exact prefixLift 1000595
  have htrace : WordTrace (prefixWord ++ tailWord_1000595) baseStart_1000595 baseEnd_1000595 := by
    simpa [prefixWord, tailWord_1000595, baseEnd_1000595] using wordTrace_append hprefix tailTrace_1000595
  have hstable : (prefixWord ++ tailWord_1000595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000595).length < 2 ^ (prefixWord ++ tailWord_1000595).sum := by decide
  have hdescent : baseEnd_1000595 < baseStart_1000595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000600 : List Nat := [2, 1, 2, 4, 2, 3, 2, 1, 2, 2, 2]
def baseStart_1000600 : Nat := 118140960795 + 1000600 * 2 ^ 59
def prefixEnd_1000600 : Nat := 4983230072969 + 3 ^ 40 * 1000600 * 2
def baseEnd_1000600 : Nat := 513788742888890381598331

theorem tailTrace_1000600 : CollatzResearch.WordTrace tailWord_1000600 prefixEnd_1000600 513788742888890381598331 := by
  unfold tailWord_1000600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18247440087502281859975627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24329920116669709146634169 18247440087502281859975627)
  ·
    refine ⟨27371160131253422789963441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18247440087502281859975627 27371160131253422789963441)
    ·
      refine ⟨20528370098440067092472581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27371160131253422789963441 20528370098440067092472581)
      ·
        refine ⟨3849069393457512579838609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20528370098440067092472581 3849069393457512579838609)
        ·
          refine ⟨2886802045093134434878957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3849069393457512579838609 2886802045093134434878957)
          ·
            refine ⟨1082550766909925413079609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2886802045093134434878957 1082550766909925413079609)
            ·
              refine ⟨811913075182444059809707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1082550766909925413079609 811913075182444059809707)
              ·
                refine ⟨1217869612773666089714561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811913075182444059809707 1217869612773666089714561)
                ·
                  refine ⟨913402209580249567285921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1217869612773666089714561 913402209580249567285921)
                  ·
                    refine ⟨685051657185187175464441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 913402209580249567285921 685051657185187175464441)
                    ·
                      refine ⟨513788742888890381598331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685051657185187175464441 513788742888890381598331)
                      ·
                        rfl

theorem cell23_1000600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_1000600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000600 prefixEnd_1000600 := by exact prefixLift 1000600
  have htrace : WordTrace (prefixWord ++ tailWord_1000600) baseStart_1000600 baseEnd_1000600 := by
    simpa [prefixWord, tailWord_1000600, baseEnd_1000600] using wordTrace_append hprefix tailTrace_1000600
  have hstable : (prefixWord ++ tailWord_1000600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000600).length < 2 ^ (prefixWord ++ tailWord_1000600).sum := by decide
  have hdescent : baseEnd_1000600 < baseStart_1000600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000632 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 7, 4]
def baseStart_1000632 : Nat := 118140960795 + 1000632 * 2 ^ 59
def prefixEnd_1000632 : Nat := 4983230072969 + 3 ^ 40 * 1000632 * 2
def baseEnd_1000632 : Nat := 171268391423278085466061

theorem tailTrace_1000632 : CollatzResearch.WordTrace tailWord_1000632 prefixEnd_1000632 171268391423278085466061 := by
  unfold tailWord_1000632
  simp only [CollatzResearch.WordTrace]
  refine ⟨18248023655444316592558075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24330698207259088790077433 18248023655444316592558075)
  ·
    refine ⟨27372035483166474888837113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18248023655444316592558075 27372035483166474888837113)
    ·
      refine ⟨20529026612374856166627835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27372035483166474888837113 20529026612374856166627835)
      ·
        refine ⟨30793539918562284249941753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20529026612374856166627835 30793539918562284249941753)
        ·
          refine ⟨23095154938921713187456315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30793539918562284249941753 23095154938921713187456315)
          ·
            refine ⟨34642732408382569781184473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23095154938921713187456315 34642732408382569781184473)
            ·
              refine ⟨25982049306286927335888355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34642732408382569781184473 25982049306286927335888355)
              ·
                refine ⟨38973073959430391003832533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25982049306286927335888355 38973073959430391003832533)
                ·
                  refine ⟨913431420924149789152325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38973073959430391003832533 913431420924149789152325)
                  ·
                    refine ⟨171268391423278085466061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913431420924149789152325 171268391423278085466061)
                    ·
                      rfl

theorem cell23_1000632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 4].length) (baseStart_1000632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000632 prefixEnd_1000632 := by exact prefixLift 1000632
  have htrace : WordTrace (prefixWord ++ tailWord_1000632) baseStart_1000632 baseEnd_1000632 := by
    simpa [prefixWord, tailWord_1000632, baseEnd_1000632] using wordTrace_append hprefix tailTrace_1000632
  have hstable : (prefixWord ++ tailWord_1000632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000632).length < 2 ^ (prefixWord ++ tailWord_1000632).sum := by decide
  have hdescent : baseEnd_1000632 < baseStart_1000632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000689 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 3]
def baseStart_1000689 : Nat := 118140960795 + 1000689 * 2 ^ 59
def prefixEnd_1000689 : Nat := 4983230072969 + 3 ^ 40 * 1000689 * 2
def baseEnd_1000689 : Nat := 513834442667140533385421

theorem tailTrace_1000689 : CollatzResearch.WordTrace tailWord_1000689 prefixEnd_1000689 513834442667140533385421 := by
  unfold tailWord_1000689
  simp only [CollatzResearch.WordTrace]
  refine ⟨36498126271682131919941121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24332084181121421279960747 36498126271682131919941121)
  ·
    refine ⟨27373594703761598939955841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36498126271682131919941121 27373594703761598939955841)
    ·
      refine ⟨20530196027821199204966881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27373594703761598939955841 20530196027821199204966881)
      ·
        refine ⟨15397647020865899403725161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20530196027821199204966881 15397647020865899403725161)
        ·
          refine ⟨11548235265649424552793871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15397647020865899403725161 11548235265649424552793871)
          ·
            refine ⟨17322352898474136829190807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11548235265649424552793871 17322352898474136829190807)
            ·
              refine ⟨25983529347711205243786211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17322352898474136829190807 25983529347711205243786211)
              ·
                refine ⟨38975294021566807865679317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25983529347711205243786211 38975294021566807865679317)
                ·
                  refine ⟨913483453630472059351859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 38975294021566807865679317 913483453630472059351859)
                  ·
                    refine ⟨1370225180445708089027789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 913483453630472059351859 1370225180445708089027789)
                    ·
                      refine ⟨513834442667140533385421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1370225180445708089027789 513834442667140533385421)
                      ·
                        rfl

theorem cell23_1000689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_1000689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000689 prefixEnd_1000689 := by exact prefixLift 1000689
  have htrace : WordTrace (prefixWord ++ tailWord_1000689) baseStart_1000689 baseEnd_1000689 := by
    simpa [prefixWord, tailWord_1000689, baseEnd_1000689] using wordTrace_append hprefix tailTrace_1000689
  have hstable : (prefixWord ++ tailWord_1000689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000689).length < 2 ^ (prefixWord ++ tailWord_1000689).sum := by decide
  have hdescent : baseEnd_1000689 < baseStart_1000689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000734 : List Nat := [4, 3, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1000734 : Nat := 118140960795 + 1000734 * 2 ^ 59
def prefixEnd_1000734 : Nat := 4983230072969 + 3 ^ 40 * 1000734 * 2
def baseEnd_1000734 : Nat := 171285849765530952440905

theorem tailTrace_1000734 : CollatzResearch.WordTrace tailWord_1000734 prefixEnd_1000734 171285849765530952440905 := by
  unfold tailWord_1000734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562470944564888075666157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24333178371012736403552837 4562470944564888075666157)
  ·
    refine ⟨1710926604211833028374809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4562470944564888075666157 1710926604211833028374809)
    ·
      refine ⟨1283194953158874771281107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1710926604211833028374809 1283194953158874771281107)
      ·
        refine ⟨1924792429738312156921661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1283194953158874771281107 1924792429738312156921661)
        ·
          refine ⟨721797161151867058845623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1924792429738312156921661 721797161151867058845623)
          ·
            refine ⟨1082695741727800588268435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721797161151867058845623 1082695741727800588268435)
            ·
              refine ⟨1624043612591700882402653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082695741727800588268435 1624043612591700882402653)
              ·
                refine ⟨609016354721887830900995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1624043612591700882402653 609016354721887830900995)
                ·
                  refine ⟨913524532082831746351493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609016354721887830900995 913524532082831746351493)
                  ·
                    refine ⟨171285849765530952440905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913524532082831746351493 171285849765530952440905)
                    ·
                      rfl

theorem cell23_1000734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1000734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000734 prefixEnd_1000734 := by exact prefixLift 1000734
  have htrace : WordTrace (prefixWord ++ tailWord_1000734) baseStart_1000734 baseEnd_1000734 := by
    simpa [prefixWord, tailWord_1000734, baseEnd_1000734] using wordTrace_append hprefix tailTrace_1000734
  have hstable : (prefixWord ++ tailWord_1000734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000734).length < 2 ^ (prefixWord ++ tailWord_1000734).sum := by decide
  have hdescent : baseEnd_1000734 < baseStart_1000734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000739 : List Nat := [1, 1, 1, 4, 2, 3, 1, 2, 4, 4]
def baseStart_1000739 : Nat := 118140960795 + 1000739 * 2 ^ 59
def prefixEnd_1000739 : Nat := 4983230072969 + 3 ^ 40 * 1000739 * 2
def baseEnd_1000739 : Nat := 171286705566621779253397

theorem tailTrace_1000739 : CollatzResearch.WordTrace tailWord_1000739 prefixEnd_1000739 171286705566621779253397 := by
  unfold tailWord_1000739
  simp only [CollatzResearch.WordTrace]
  refine ⟨36499949921500990459261271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24333299947667326972840847 36499949921500990459261271)
  ·
    refine ⟨54749924882251485688891907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36499949921500990459261271 54749924882251485688891907)
    ·
      refine ⟨82124887323377228533337861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54749924882251485688891907 82124887323377228533337861)
      ·
        refine ⟨15398416373133230350000849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82124887323377228533337861 15398416373133230350000849)
        ·
          refine ⟨11548812279849922762500637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15398416373133230350000849 11548812279849922762500637)
          ·
            refine ⟨4330804604943721035937739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11548812279849922762500637 4330804604943721035937739)
            ·
              refine ⟨6496206907415581553906609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330804604943721035937739 6496206907415581553906609)
              ·
                refine ⟨4872155180561686165429957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6496206907415581553906609 4872155180561686165429957)
                ·
                  refine ⟨913529096355316156018117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4872155180561686165429957 913529096355316156018117)
                  ·
                    refine ⟨171286705566621779253397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913529096355316156018117 171286705566621779253397)
                    ·
                      rfl

theorem cell23_1000739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4, 4].length) (baseStart_1000739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000739 prefixEnd_1000739 := by exact prefixLift 1000739
  have htrace : WordTrace (prefixWord ++ tailWord_1000739) baseStart_1000739 baseEnd_1000739 := by
    simpa [prefixWord, tailWord_1000739, baseEnd_1000739] using wordTrace_append hprefix tailTrace_1000739
  have hstable : (prefixWord ++ tailWord_1000739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000739).length < 2 ^ (prefixWord ++ tailWord_1000739).sum := by decide
  have hdescent : baseEnd_1000739 < baseStart_1000739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000756 : List Nat := [2, 5, 1, 1, 1, 1, 1, 3, 4, 4]
def baseStart_1000756 : Nat := 118140960795 + 1000756 * 2 ^ 59
def prefixEnd_1000756 : Nat := 4983230072969 + 3 ^ 40 * 1000756 * 2
def baseEnd_1000756 : Nat := 171289615290330590415871

theorem tailTrace_1000756 : CollatzResearch.WordTrace tailWord_1000756 prefixEnd_1000756 171289615290330590415871 := by
  unfold tailWord_1000756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18250284981219701181315061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24333713308292934908420081 18250284981219701181315061)
  ·
    refine ⟨1710964216989346985748287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18250284981219701181315061 1710964216989346985748287)
    ·
      refine ⟨2566446325484020478622431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1710964216989346985748287 2566446325484020478622431)
      ·
        refine ⟨3849669488226030717933647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2566446325484020478622431 3849669488226030717933647)
        ·
          refine ⟨5774504232339046076900471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849669488226030717933647 5774504232339046076900471)
          ·
            refine ⟨8661756348508569115350707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774504232339046076900471 8661756348508569115350707)
            ·
              refine ⟨12992634522762853673026061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8661756348508569115350707 12992634522762853673026061)
              ·
                refine ⟨4872237946036070127384773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12992634522762853673026061 4872237946036070127384773)
                ·
                  refine ⟨913544614881763148884645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4872237946036070127384773 913544614881763148884645)
                  ·
                    refine ⟨171289615290330590415871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913544614881763148884645 171289615290330590415871)
                    ·
                      rfl

theorem cell23_1000756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_1000756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000756 prefixEnd_1000756 := by exact prefixLift 1000756
  have htrace : WordTrace (prefixWord ++ tailWord_1000756) baseStart_1000756 baseEnd_1000756 := by
    simpa [prefixWord, tailWord_1000756, baseEnd_1000756] using wordTrace_append hprefix tailTrace_1000756
  have hstable : (prefixWord ++ tailWord_1000756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000756).length < 2 ^ (prefixWord ++ tailWord_1000756).sum := by decide
  have hdescent : baseEnd_1000756 < baseStart_1000756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000766 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_1000766 : Nat := 118140960795 + 1000766 * 2 ^ 59
def prefixEnd_1000766 : Nat := 4983230072969 + 3 ^ 40 * 1000766 * 2
def baseEnd_1000766 : Nat := 513873980677536732122567

theorem tailTrace_1000766 : CollatzResearch.WordTrace tailWord_1000766 prefixEnd_1000766 513873980677536732122567 := by
  unfold tailWord_1000766
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562616836550396758811769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24333956461602116046996101 4562616836550396758811769)
  ·
    refine ⟨3421962627412797569108827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4562616836550396758811769 3421962627412797569108827)
    ·
      refine ⟨5132943941119196353663241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3421962627412797569108827 5132943941119196353663241)
      ·
        refine ⟨3849707955839397265247431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5132943941119196353663241 3849707955839397265247431)
        ·
          refine ⟨5774561933759095897871147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3849707955839397265247431 5774561933759095897871147)
          ·
            refine ⟨8661842900638643846806721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5774561933759095897871147 8661842900638643846806721)
            ·
              refine ⟨6496382175478982885105041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8661842900638643846806721 6496382175478982885105041)
              ·
                refine ⟨4872286631609237163828781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6496382175478982885105041 4872286631609237163828781)
                ·
                  refine ⟨1827107486853463936435793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4872286631609237163828781 1827107486853463936435793)
                  ·
                    refine ⟨1370330615140097952326845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827107486853463936435793 1370330615140097952326845)
                    ·
                      refine ⟨513873980677536732122567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1370330615140097952326845 513873980677536732122567)
                      ·
                        rfl

theorem cell23_1000766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_1000766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000766 prefixEnd_1000766 := by exact prefixLift 1000766
  have htrace : WordTrace (prefixWord ++ tailWord_1000766) baseStart_1000766 baseEnd_1000766 := by
    simpa [prefixWord, tailWord_1000766, baseEnd_1000766] using wordTrace_append hprefix tailTrace_1000766
  have hstable : (prefixWord ++ tailWord_1000766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000766).length < 2 ^ (prefixWord ++ tailWord_1000766).sum := by decide
  have hdescent : baseEnd_1000766 < baseStart_1000766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000769 : List Nat := [1, 2, 5, 2, 1, 1, 1, 10]
def baseStart_1000769 : Nat := 118140960795 + 1000769 * 2 ^ 59
def prefixEnd_1000769 : Nat := 4983230072969 + 3 ^ 40 * 1000769 * 2
def baseEnd_1000769 : Nat := 19032426708129637792039

theorem tailTrace_1000769 : CollatzResearch.WordTrace tailWord_1000769 prefixEnd_1000769 19032426708129637792039 := by
  unfold tailWord_1000769
  simp only [CollatzResearch.WordTrace]
  refine ⟨36501044111392305582853361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24334029407594870388568907 36501044111392305582853361)
  ·
    refine ⟨27375783083544229187140021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36501044111392305582853361 27375783083544229187140021)
    ·
      refine ⟨2566479664082271486294377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27375783083544229187140021 2566479664082271486294377)
      ·
        refine ⟨1924859748061703614720783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2566479664082271486294377 1924859748061703614720783)
        ·
          refine ⟨2887289622092555422081175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1924859748061703614720783 2887289622092555422081175)
          ·
            refine ⟨4330934433138833133121763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2887289622092555422081175 4330934433138833133121763)
            ·
              refine ⟨6496401649708249699682645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4330934433138833133121763 6496401649708249699682645)
              ·
                refine ⟨19032426708129637792039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 6496401649708249699682645 19032426708129637792039)
                ·
                  rfl

theorem cell23_1000769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 10].length) (baseStart_1000769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000769 prefixEnd_1000769 := by exact prefixLift 1000769
  have htrace : WordTrace (prefixWord ++ tailWord_1000769) baseStart_1000769 baseEnd_1000769 := by
    simpa [prefixWord, tailWord_1000769, baseEnd_1000769] using wordTrace_append hprefix tailTrace_1000769
  have hstable : (prefixWord ++ tailWord_1000769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000769).length < 2 ^ (prefixWord ++ tailWord_1000769).sum := by decide
  have hdescent : baseEnd_1000769 < baseStart_1000769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000813 : List Nat := [1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1000813 : Nat := 118140960795 + 1000813 * 2 ^ 59
def prefixEnd_1000813 : Nat := 4983230072969 + 3 ^ 40 * 1000813 * 2
def baseEnd_1000813 : Nat := 513898114268298048234851

theorem tailTrace_1000813 : CollatzResearch.WordTrace tailWord_1000813 prefixEnd_1000813 513898114268298048234851 := by
  unfold tailWord_1000813
  simp only [CollatzResearch.WordTrace]
  refine ⟨36502648923232901097455093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24335099282155267398303395 36502648923232901097455093)
  ·
    refine ⟨3422123336553084477886415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36502648923232901097455093 3422123336553084477886415)
    ·
      refine ⟨5133185004829626716829623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422123336553084477886415 5133185004829626716829623)
      ·
        refine ⟨7699777507244440075244435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5133185004829626716829623 7699777507244440075244435)
        ·
          refine ⟨11549666260866660112866653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7699777507244440075244435 11549666260866660112866653)
          ·
            refine ⟨4331124847824997542324995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11549666260866660112866653 4331124847824997542324995)
            ·
              refine ⟨6496687271737496313487493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331124847824997542324995 6496687271737496313487493)
              ·
                refine ⟨1218128863450780558778905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6496687271737496313487493 1218128863450780558778905)
                ·
                  refine ⟨913596647588085419084179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218128863450780558778905 913596647588085419084179)
                  ·
                    refine ⟨1370394971382128128626269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 913596647588085419084179 1370394971382128128626269)
                    ·
                      refine ⟨513898114268298048234851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1370394971382128128626269 513898114268298048234851)
                      ·
                        rfl

theorem cell23_1000813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1000813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000813 prefixEnd_1000813 := by exact prefixLift 1000813
  have htrace : WordTrace (prefixWord ++ tailWord_1000813) baseStart_1000813 baseEnd_1000813 := by
    simpa [prefixWord, tailWord_1000813, baseEnd_1000813] using wordTrace_append hprefix tailTrace_1000813
  have hstable : (prefixWord ++ tailWord_1000813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000813).length < 2 ^ (prefixWord ++ tailWord_1000813).sum := by decide
  have hdescent : baseEnd_1000813 < baseStart_1000813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000814 : List Nat := [4, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2]
def baseStart_1000814 : Nat := 118140960795 + 1000814 * 2 ^ 59
def prefixEnd_1000814 : Nat := 4983230072969 + 3 ^ 40 * 1000814 * 2
def baseEnd_1000814 : Nat := 513898627748952544322347

theorem tailTrace_1000814 : CollatzResearch.WordTrace tailWord_1000814 prefixEnd_1000814 513898627748952544322347 := by
  unfold tailWord_1000814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4562835674528659783530187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24335123597486185512160997 4562835674528659783530187)
  ·
    refine ⟨6844253511792989675295281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4562835674528659783530187 6844253511792989675295281)
    ·
      refine ⟨5133190133844742256471461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6844253511792989675295281 5133190133844742256471461)
      ·
        refine ⟨962473150095889173088399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5133190133844742256471461 962473150095889173088399)
        ·
          refine ⟨1443709725143833759632599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962473150095889173088399 1443709725143833759632599)
          ·
            refine ⟨2165564587715750639448899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1443709725143833759632599 2165564587715750639448899)
            ·
              refine ⟨3248346881573625959173349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2165564587715750639448899 3248346881573625959173349)
              ·
                refine ⟨609065040295054867345003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3248346881573625959173349 609065040295054867345003)
                ·
                  refine ⟨913597560442582301017505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609065040295054867345003 913597560442582301017505)
                  ·
                    refine ⟨685198170331936725763129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 913597560442582301017505 685198170331936725763129)
                    ·
                      refine ⟨513898627748952544322347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685198170331936725763129 513898627748952544322347)
                      ·
                        rfl

theorem cell23_1000814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_1000814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000814 prefixEnd_1000814 := by exact prefixLift 1000814
  have htrace : WordTrace (prefixWord ++ tailWord_1000814) baseStart_1000814 baseEnd_1000814 := by
    simpa [prefixWord, tailWord_1000814, baseEnd_1000814] using wordTrace_append hprefix tailTrace_1000814
  have hstable : (prefixWord ++ tailWord_1000814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000814).length < 2 ^ (prefixWord ++ tailWord_1000814).sum := by decide
  have hdescent : baseEnd_1000814 < baseStart_1000814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000829 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 2, 6]
def baseStart_1000829 : Nat := 118140960795 + 1000829 * 2 ^ 59
def prefixEnd_1000829 : Nat := 4983230072969 + 3 ^ 40 * 1000829 * 2
def baseEnd_1000829 : Nat := 171302109986256661878259

theorem tailTrace_1000829 : CollatzResearch.WordTrace tailWord_1000829 prefixEnd_1000829 171302109986256661878259 := by
  unfold tailWord_1000829
  simp only [CollatzResearch.WordTrace]
  refine ⟨36503232491174935830037541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24335488327449957220025027 36503232491174935830037541)
  ·
    refine ⟨6844356092095300468132039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36503232491174935830037541 6844356092095300468132039)
    ·
      refine ⟨10266534138142950702198059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6844356092095300468132039 10266534138142950702198059)
      ·
        refine ⟨15399801207214426053297089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10266534138142950702198059 15399801207214426053297089)
        ·
          refine ⟨11549850905410819539972817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15399801207214426053297089 11549850905410819539972817)
          ·
            refine ⟨8662388179058114654979613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11549850905410819539972817 8662388179058114654979613)
            ·
              refine ⟨3248395567146792995617355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8662388179058114654979613 3248395567146792995617355)
              ·
                refine ⟨4872593350720189493426033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3248395567146792995617355 4872593350720189493426033)
                ·
                  refine ⟨3654445013040142120069525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872593350720189493426033 3654445013040142120069525)
                  ·
                    refine ⟨171302109986256661878259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3654445013040142120069525 171302109986256661878259)
                    ·
                      rfl

theorem cell23_1000829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 2, 6].length) (baseStart_1000829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000829 prefixEnd_1000829 := by exact prefixLift 1000829
  have htrace : WordTrace (prefixWord ++ tailWord_1000829) baseStart_1000829 baseEnd_1000829 := by
    simpa [prefixWord, tailWord_1000829, baseEnd_1000829] using wordTrace_append hprefix tailTrace_1000829
  have hstable : (prefixWord ++ tailWord_1000829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000829).length < 2 ^ (prefixWord ++ tailWord_1000829).sum := by decide
  have hdescent : baseEnd_1000829 < baseStart_1000829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000866 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1000866 : Nat := 118140960795 + 1000866 * 2 ^ 59
def prefixEnd_1000866 : Nat := 4983230072969 + 3 ^ 40 * 1000866 * 2
def baseEnd_1000866 : Nat := 513925328742986340872107

theorem tailTrace_1000866 : CollatzResearch.WordTrace tailWord_1000866 prefixEnd_1000866 513925328742986340872107 := by
  unfold tailWord_1000866
  simp only [CollatzResearch.WordTrace]
  refine ⟨9126145498010222787283613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24336387994693927432756301 9126145498010222787283613)
  ·
    refine ⟨3422304561753833545231355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9126145498010222787283613 3422304561753833545231355)
    ·
      refine ⟨5133456842630750317847033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3422304561753833545231355 5133456842630750317847033)
      ·
        refine ⟨3850092631973062738385275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5133456842630750317847033 3850092631973062738385275)
        ·
          refine ⟨5775138947959594107577913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3850092631973062738385275 5775138947959594107577913)
          ·
            refine ⟨4331354210969695580683435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5775138947959594107577913 4331354210969695580683435)
            ·
              refine ⟨6497031316454543371025153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4331354210969695580683435 6497031316454543371025153)
              ·
                refine ⟨4872773487340907528268865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6497031316454543371025153 4872773487340907528268865)
                ·
                  refine ⟨3654580115505680646201649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4872773487340907528268865 3654580115505680646201649)
                  ·
                    refine ⟨2740935086629260484651237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3654580115505680646201649 2740935086629260484651237)
                    ·
                      refine ⟨513925328742986340872107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2740935086629260484651237 513925328742986340872107)
                      ·
                        rfl

theorem cell23_1000866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1000866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000866 prefixEnd_1000866 := by exact prefixLift 1000866
  have htrace : WordTrace (prefixWord ++ tailWord_1000866) baseStart_1000866 baseEnd_1000866 := by
    simpa [prefixWord, tailWord_1000866, baseEnd_1000866] using wordTrace_append hprefix tailTrace_1000866
  have hstable : (prefixWord ++ tailWord_1000866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000866).length < 2 ^ (prefixWord ++ tailWord_1000866).sum := by decide
  have hdescent : baseEnd_1000866 < baseStart_1000866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000876 : List Nat := [2, 2, 1, 1, 1, 1, 6, 4, 5]
def baseStart_1000876 : Nat := 118140960795 + 1000876 * 2 ^ 59
def prefixEnd_1000876 : Nat := 4983230072969 + 3 ^ 40 * 1000876 * 2
def baseEnd_1000876 : Nat := 57103384838836811305229

theorem tailTrace_1000876 : CollatzResearch.WordTrace tailWord_1000876 prefixEnd_1000876 57103384838836811305229 := by
  unfold tailWord_1000876
  simp only [CollatzResearch.WordTrace]
  refine ⟨18252473361002331428499241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24336631148003108571332321 18252473361002331428499241)
  ·
    refine ⟨13689355020751748571374431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18252473361002331428499241 13689355020751748571374431)
    ·
      refine ⟨20534032531127622857061647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13689355020751748571374431 20534032531127622857061647)
      ·
        refine ⟨30801048796691434285592471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20534032531127622857061647 30801048796691434285592471)
        ·
          refine ⟨46201573195037151428388707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30801048796691434285592471 46201573195037151428388707)
          ·
            refine ⟨69302359792555727142583061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46201573195037151428388707 69302359792555727142583061)
            ·
              refine ⟨3248548115276049709808581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 69302359792555727142583061 3248548115276049709808581)
              ·
                refine ⟨609102771614259320589109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3248548115276049709808581 609102771614259320589109)
                ·
                  refine ⟨57103384838836811305229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609102771614259320589109 57103384838836811305229)
                  ·
                    rfl

theorem cell23_1000876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_1000876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000876 prefixEnd_1000876 := by exact prefixLift 1000876
  have htrace : WordTrace (prefixWord ++ tailWord_1000876) baseStart_1000876 baseEnd_1000876 := by
    simpa [prefixWord, tailWord_1000876, baseEnd_1000876] using wordTrace_append hprefix tailTrace_1000876
  have hstable : (prefixWord ++ tailWord_1000876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000876).length < 2 ^ (prefixWord ++ tailWord_1000876).sum := by decide
  have hdescent : baseEnd_1000876 < baseStart_1000876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000896 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 2, 5, 2]
def baseStart_1000896 : Nat := 118140960795 + 1000896 * 2 ^ 59
def prefixEnd_1000896 : Nat := 4983230072969 + 3 ^ 40 * 1000896 * 2
def baseEnd_1000896 : Nat := 513940733162621223496969

theorem tailTrace_1000896 : CollatzResearch.WordTrace tailWord_1000896 prefixEnd_1000896 513940733162621223496969 := by
  unfold tailWord_1000896
  simp only [CollatzResearch.WordTrace]
  refine ⟨18252838090966103136363271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24337117454621470848484361 18252838090966103136363271)
  ·
    refine ⟨27379257136449154704544907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18252838090966103136363271 27379257136449154704544907)
    ·
      refine ⟨41068885704673732056817361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27379257136449154704544907 41068885704673732056817361)
      ·
        refine ⟨30801664278505299042613021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41068885704673732056817361 30801664278505299042613021)
        ·
          refine ⟨11550624104439487140979883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30801664278505299042613021 11550624104439487140979883)
          ·
            refine ⟨17325936156659230711469825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11550624104439487140979883 17325936156659230711469825)
            ·
              refine ⟨12994452117494423033602369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17325936156659230711469825 12994452117494423033602369)
              ·
                refine ⟨9745839088120817275201777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12994452117494423033602369 9745839088120817275201777)
                ·
                  refine ⟨7309379316090612956401333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9745839088120817275201777 7309379316090612956401333)
                  ·
                    refine ⟨685254310883494964662625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7309379316090612956401333 685254310883494964662625)
                    ·
                      refine ⟨513940733162621223496969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685254310883494964662625 513940733162621223496969)
                      ·
                        rfl

theorem cell23_1000896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 2, 5, 2].length) (baseStart_1000896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000896 prefixEnd_1000896 := by exact prefixLift 1000896
  have htrace : WordTrace (prefixWord ++ tailWord_1000896) baseStart_1000896 baseEnd_1000896 := by
    simpa [prefixWord, tailWord_1000896, baseEnd_1000896] using wordTrace_append hprefix tailTrace_1000896
  have hstable : (prefixWord ++ tailWord_1000896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000896).length < 2 ^ (prefixWord ++ tailWord_1000896).sum := by decide
  have hdescent : baseEnd_1000896 < baseStart_1000896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1000939 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4]
def baseStart_1000939 : Nat := 118140960795 + 1000939 * 2 ^ 59
def prefixEnd_1000939 : Nat := 4983230072969 + 3 ^ 40 * 1000939 * 2
def baseEnd_1000939 : Nat := 513962812830764555259271

theorem tailTrace_1000939 : CollatzResearch.WordTrace tailWord_1000939 prefixEnd_1000939 513962812830764555259271 := by
  unfold tailWord_1000939
  simp only [CollatzResearch.WordTrace]
  refine ⟨36507244520776424616541871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24338163013850949744361247 36507244520776424616541871)
  ·
    refine ⟨54760866781164636924812807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36507244520776424616541871 54760866781164636924812807)
    ·
      refine ⟨82141300171746955387219211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54760866781164636924812807 82141300171746955387219211)
      ·
        refine ⟨123211950257620433080828817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82141300171746955387219211 123211950257620433080828817)
        ·
          refine ⟨92408962693215324810621613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123211950257620433080828817 92408962693215324810621613)
          ·
            refine ⟨34653361009955746803983105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92408962693215324810621613 34653361009955746803983105)
            ·
              refine ⟨25990020757466810102987329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34653361009955746803983105 25990020757466810102987329)
              ·
                refine ⟨19492515568100107577240497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25990020757466810102987329 19492515568100107577240497)
                ·
                  refine ⟨14619386676075080682930373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19492515568100107577240497 14619386676075080682930373)
                  ·
                    refine ⟨2741135001764077628049445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14619386676075080682930373 2741135001764077628049445)
                    ·
                      refine ⟨513962812830764555259271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2741135001764077628049445 513962812830764555259271)
                      ·
                        rfl

theorem cell23_1000939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 4, 4].length) (baseStart_1000939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1000939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1000939 prefixEnd_1000939 := by exact prefixLift 1000939
  have htrace : WordTrace (prefixWord ++ tailWord_1000939) baseStart_1000939 baseEnd_1000939 := by
    simpa [prefixWord, tailWord_1000939, baseEnd_1000939] using wordTrace_append hprefix tailTrace_1000939
  have hstable : (prefixWord ++ tailWord_1000939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1000939).length < 2 ^ (prefixWord ++ tailWord_1000939).sum := by decide
  have hdescent : baseEnd_1000939 < baseStart_1000939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1000939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001014 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_1001014 : Nat := 118140960795 + 1001014 * 2 ^ 59
def prefixEnd_1001014 : Nat := 4983230072969 + 3 ^ 40 * 1001014 * 2
def baseEnd_1001014 : Nat := 514001323879851761821427

theorem tailTrace_1001014 : CollatzResearch.WordTrace tailWord_1001014 prefixEnd_1001014 514001323879851761821427 := by
  unfold tailWord_1001014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2281873749719044526595131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24339986663669808283681397 2281873749719044526595131)
  ·
    refine ⟨3422810624578566789892697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2281873749719044526595131 3422810624578566789892697)
    ·
      refine ⟨2567107968433925092419523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3422810624578566789892697 2567107968433925092419523)
      ·
        refine ⟨3850661952650887638629285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2567107968433925092419523 3850661952650887638629285)
        ·
          refine ⟨721999116122041432242991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3850661952650887638629285 721999116122041432242991)
          ·
            refine ⟨1082998674183062148364487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 721999116122041432242991 1082998674183062148364487)
            ·
              refine ⟨1624498011274593222546731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1082998674183062148364487 1624498011274593222546731)
              ·
                refine ⟨2436747016911889833820097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624498011274593222546731 2436747016911889833820097)
                ·
                  refine ⟨1827560262683917375365073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2436747016911889833820097 1827560262683917375365073)
                  ·
                    refine ⟨1370670197012938031523805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1827560262683917375365073 1370670197012938031523805)
                    ·
                      refine ⟨514001323879851761821427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1370670197012938031523805 514001323879851761821427)
                      ·
                        rfl

theorem cell23_1001014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_1001014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001014 prefixEnd_1001014 := by exact prefixLift 1001014
  have htrace : WordTrace (prefixWord ++ tailWord_1001014) baseStart_1001014 baseEnd_1001014 := by
    simpa [prefixWord, tailWord_1001014, baseEnd_1001014] using wordTrace_append hprefix tailTrace_1001014
  have hstable : (prefixWord ++ tailWord_1001014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001014).length < 2 ^ (prefixWord ++ tailWord_1001014).sum := by decide
  have hdescent : baseEnd_1001014 < baseStart_1001014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001020 : List Nat := [2, 2, 2, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_1001020 : Nat := 118140960795 + 1001020 * 2 ^ 59
def prefixEnd_1001020 : Nat := 4983230072969 + 3 ^ 40 * 1001020 * 2
def baseEnd_1001020 : Nat := 514004404763778738346399

theorem tailTrace_1001020 : CollatzResearch.WordTrace tailWord_1001020 prefixEnd_1001020 514004404763778738346399 := by
  unfold tailWord_1001020
  simp only [CollatzResearch.WordTrace]
  refine ⟨18255099416741487725120257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24340132555655316966827009 18255099416741487725120257)
  ·
    refine ⟨13691324562556115793840193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18255099416741487725120257 13691324562556115793840193)
    ·
      refine ⟨10268493421917086845380145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13691324562556115793840193 10268493421917086845380145)
      ·
        refine ⟨7701370066437815134035109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10268493421917086845380145 7701370066437815134035109)
        ·
          refine ⟨1444006887457090337631583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7701370066437815134035109 1444006887457090337631583)
          ·
            refine ⟨2166010331185635506447375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444006887457090337631583 2166010331185635506447375)
            ·
              refine ⟨3249015496778453259671063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166010331185635506447375 3249015496778453259671063)
              ·
                refine ⟨4873523245167679889506595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249015496778453259671063 4873523245167679889506595)
                ·
                  refine ⟨7310284867751519834259893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4873523245167679889506595 7310284867751519834259893)
                  ·
                    refine ⟨685339206351704984461865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7310284867751519834259893 685339206351704984461865)
                    ·
                      refine ⟨514004404763778738346399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685339206351704984461865 514004404763778738346399)
                      ·
                        rfl

theorem cell23_1001020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_1001020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001020 prefixEnd_1001020 := by exact prefixLift 1001020
  have htrace : WordTrace (prefixWord ++ tailWord_1001020) baseStart_1001020 baseEnd_1001020 := by
    simpa [prefixWord, tailWord_1001020, baseEnd_1001020] using wordTrace_append hprefix tailTrace_1001020
  have hstable : (prefixWord ++ tailWord_1001020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001020).length < 2 ^ (prefixWord ++ tailWord_1001020).sum := by decide
  have hdescent : baseEnd_1001020 < baseStart_1001020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001063 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_1001063 : Nat := 118140960795 + 1001063 * 2 ^ 59
def prefixEnd_1001063 : Nat := 4983230072969 + 3 ^ 40 * 1001063 * 2
def baseEnd_1001063 : Nat := 514026484431922070108701

theorem tailTrace_1001063 : CollatzResearch.WordTrace tailWord_1001063 prefixEnd_1001063 514026484431922070108701 := by
  unfold tailWord_1001063
  simp only [CollatzResearch.WordTrace]
  refine ⟨36511767172327193794055843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24341178114884795862703895 36511767172327193794055843)
  ·
    refine ⟨54767650758490790691083765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36511767172327193794055843 54767650758490790691083765)
    ·
      refine ⟨5134467258608511627289103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54767650758490790691083765 5134467258608511627289103)
      ·
        refine ⟨7701700887912767440933655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5134467258608511627289103 7701700887912767440933655)
        ·
          refine ⟨11552551331869151161400483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7701700887912767440933655 11552551331869151161400483)
          ·
            refine ⟨17328826997803726742100725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11552551331869151161400483 17328826997803726742100725)
            ·
              refine ⟨1624577531044099382071943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17328826997803726742100725 1624577531044099382071943)
              ·
                refine ⟨2436866296566149073107915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1624577531044099382071943 2436866296566149073107915)
                ·
                  refine ⟨3655299444849223609661873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2436866296566149073107915 3655299444849223609661873)
                  ·
                    refine ⟨2741474583636917707246405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655299444849223609661873 2741474583636917707246405)
                    ·
                      refine ⟨514026484431922070108701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2741474583636917707246405 514026484431922070108701)
                      ·
                        rfl

theorem cell23_1001063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_1001063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001063 prefixEnd_1001063 := by exact prefixLift 1001063
  have htrace : WordTrace (prefixWord ++ tailWord_1001063) baseStart_1001063 baseEnd_1001063 := by
    simpa [prefixWord, tailWord_1001063, baseEnd_1001063] using wordTrace_append hprefix tailTrace_1001063
  have hstable : (prefixWord ++ tailWord_1001063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001063).length < 2 ^ (prefixWord ++ tailWord_1001063).sum := by decide
  have hdescent : baseEnd_1001063 < baseStart_1001063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001083 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 3]
def baseStart_1001083 : Nat := 118140960795 + 1001083 * 2 ^ 59
def prefixEnd_1001083 : Nat := 4983230072969 + 3 ^ 40 * 1001083 * 2
def baseEnd_1001083 : Nat := 514036754045011991858609

theorem tailTrace_1001083 : CollatzResearch.WordTrace tailWord_1001083 prefixEnd_1001083 514036754045011991858609 := by
  unfold tailWord_1001083
  simp only [CollatzResearch.WordTrace]
  refine ⟨36512496632254737209783903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24341664421503158139855935 36512496632254737209783903)
  ·
    refine ⟨54768744948382105814675855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36512496632254737209783903 54768744948382105814675855)
    ·
      refine ⟨82153117422573158722013783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54768744948382105814675855 82153117422573158722013783)
      ·
        refine ⟨123229676133859738083020675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82153117422573158722013783 123229676133859738083020675)
        ·
          refine ⟨184844514200789607124531013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123229676133859738083020675 184844514200789607124531013)
          ·
            refine ⟨34658346412648051335849565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 184844514200789607124531013 34658346412648051335849565)
            ·
              refine ⟨12996879904743019250943587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34658346412648051335849565 12996879904743019250943587)
              ·
                refine ⟨19495319857114528876415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12996879904743019250943587 19495319857114528876415381)
                ·
                  refine ⟨913843118302243541081971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19495319857114528876415381 913843118302243541081971)
                  ·
                    refine ⟨1370764677453365311622957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 913843118302243541081971 1370764677453365311622957)
                    ·
                      refine ⟨514036754045011991858609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1370764677453365311622957 514036754045011991858609)
                      ·
                        rfl

theorem cell23_1001083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 3].length) (baseStart_1001083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001083 prefixEnd_1001083 := by exact prefixLift 1001083
  have htrace : WordTrace (prefixWord ++ tailWord_1001083) baseStart_1001083 baseEnd_1001083 := by
    simpa [prefixWord, tailWord_1001083, baseEnd_1001083] using wordTrace_append hprefix tailTrace_1001083
  have hstable : (prefixWord ++ tailWord_1001083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001083).length < 2 ^ (prefixWord ++ tailWord_1001083).sum := by decide
  have hdescent : baseEnd_1001083 < baseStart_1001083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001100 : List Nat := [2, 2, 1, 2, 1, 1, 4, 4, 2, 1, 3]
def baseStart_1001100 : Nat := 118140960795 + 1001100 * 2 ^ 59
def prefixEnd_1001100 : Nat := 4983230072969 + 3 ^ 40 * 1001100 * 2
def baseEnd_1001100 : Nat := 514045483216138425346031

theorem tailTrace_1001100 : CollatzResearch.WordTrace tailWord_1001100 prefixEnd_1001100 514045483216138425346031 := by
  unfold tailWord_1001100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18256558336596574556576377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24342077782128766075435169 18256558336596574556576377)
  ·
    refine ⟨13692418752447430917432283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18256558336596574556576377 13692418752447430917432283)
    ·
      refine ⟨20538628128671146376148425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13692418752447430917432283 20538628128671146376148425)
      ·
        refine ⟨15403971096503359782111319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20538628128671146376148425 15403971096503359782111319)
        ·
          refine ⟨23105956644755039673166979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15403971096503359782111319 23105956644755039673166979)
          ·
            refine ⟨34658934967132559509750469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23105956644755039673166979 34658934967132559509750469)
            ·
              refine ⟨6498550306337354908078213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34658934967132559509750469 6498550306337354908078213)
              ·
                refine ⟨1218478182438254045264665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6498550306337354908078213 1218478182438254045264665)
                ·
                  refine ⟨913858636828690533948499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218478182438254045264665 913858636828690533948499)
                  ·
                    refine ⟨1370787955243035800922749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 913858636828690533948499 1370787955243035800922749)
                    ·
                      refine ⟨514045483216138425346031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1370787955243035800922749 514045483216138425346031)
                      ·
                        rfl

theorem cell23_1001100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 4, 2, 1, 3].length) (baseStart_1001100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001100 prefixEnd_1001100 := by exact prefixLift 1001100
  have htrace : WordTrace (prefixWord ++ tailWord_1001100) baseStart_1001100 baseEnd_1001100 := by
    simpa [prefixWord, tailWord_1001100, baseEnd_1001100] using wordTrace_append hprefix tailTrace_1001100
  have hstable : (prefixWord ++ tailWord_1001100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001100).length < 2 ^ (prefixWord ++ tailWord_1001100).sum := by decide
  have hdescent : baseEnd_1001100 < baseStart_1001100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001143 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1001143 : Nat := 118140960795 + 1001143 * 2 ^ 59
def prefixEnd_1001143 : Nat := 4983230072969 + 3 ^ 40 * 1001143 * 2
def baseEnd_1001143 : Nat := 514067562884281757108333

theorem tailTrace_1001143 : CollatzResearch.WordTrace tailWord_1001143 prefixEnd_1001143 514067562884281757108333 := by
  unfold tailWord_1001143
  simp only [CollatzResearch.WordTrace]
  refine ⟨36514685012037367456968083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24343123341358244971312055 36514685012037367456968083)
  ·
    refine ⟨54772027518056051185452125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36514685012037367456968083 54772027518056051185452125)
    ·
      refine ⟨20539510319271019194544547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54772027518056051185452125 20539510319271019194544547)
      ·
        refine ⟨30809265478906528791816821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20539510319271019194544547 30809265478906528791816821)
        ·
          refine ⟨2888368638647487074232827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30809265478906528791816821 2888368638647487074232827)
          ·
            refine ⟨4332552957971230611349241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2888368638647487074232827 4332552957971230611349241)
            ·
              refine ⟨3249414718478422958511931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4332552957971230611349241 3249414718478422958511931)
              ·
                refine ⟨4874122077717634437767897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249414718478422958511931 4874122077717634437767897)
                ·
                  refine ⟨3655591558288225828325923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874122077717634437767897 3655591558288225828325923)
                  ·
                    refine ⟨5483387337432338742488885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3655591558288225828325923 5483387337432338742488885)
                    ·
                      refine ⟨514067562884281757108333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5483387337432338742488885 514067562884281757108333)
                      ·
                        rfl

theorem cell23_1001143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1001143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001143 prefixEnd_1001143 := by exact prefixLift 1001143
  have htrace : WordTrace (prefixWord ++ tailWord_1001143) baseStart_1001143 baseEnd_1001143 := by
    simpa [prefixWord, tailWord_1001143, baseEnd_1001143] using wordTrace_append hprefix tailTrace_1001143
  have hstable : (prefixWord ++ tailWord_1001143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001143).length < 2 ^ (prefixWord ++ tailWord_1001143).sum := by decide
  have hdescent : baseEnd_1001143 < baseStart_1001143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001170 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1001170 : Nat := 118140960795 + 1001170 * 2 ^ 59
def prefixEnd_1001170 : Nat := 4983230072969 + 3 ^ 40 * 1001170 * 2
def baseEnd_1001170 : Nat := 514081426861953151470709

theorem tailTrace_1001170 : CollatzResearch.WordTrace tailWord_1001170 prefixEnd_1001170 514081426861953151470709 := by
  unfold tailWord_1001170
  simp only [CollatzResearch.WordTrace]
  refine ⟨9128917445734887767050241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24343779855293034045467309 9128917445734887767050241)
  ·
    refine ⟨6846688084301165825287681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9128917445734887767050241 6846688084301165825287681)
    ·
      refine ⟨5135016063225874368965761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6846688084301165825287681 5135016063225874368965761)
      ·
        refine ⟨3851262047419405776724321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5135016063225874368965761 3851262047419405776724321)
        ·
          refine ⟨2888446535564554332543241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3851262047419405776724321 2888446535564554332543241)
          ·
            refine ⟨2166334901673415749407431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2888446535564554332543241 2166334901673415749407431)
            ·
              refine ⟨3249502352510123624111147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166334901673415749407431 3249502352510123624111147)
              ·
                refine ⟨4874253528765185436166721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3249502352510123624111147 4874253528765185436166721)
                ·
                  refine ⟨3655690146573889077125041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4874253528765185436166721 3655690146573889077125041)
                  ·
                    refine ⟨2741767609930416807843781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3655690146573889077125041 2741767609930416807843781)
                    ·
                      refine ⟨514081426861953151470709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2741767609930416807843781 514081426861953151470709)
                      ·
                        rfl

theorem cell23_1001170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1001170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001170 prefixEnd_1001170 := by exact prefixLift 1001170
  have htrace : WordTrace (prefixWord ++ tailWord_1001170) baseStart_1001170 baseEnd_1001170 := by
    simpa [prefixWord, tailWord_1001170, baseEnd_1001170] using wordTrace_append hprefix tailTrace_1001170
  have hstable : (prefixWord ++ tailWord_1001170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001170).length < 2 ^ (prefixWord ++ tailWord_1001170).sum := by decide
  have hdescent : baseEnd_1001170 < baseStart_1001170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001197 : List Nat := [1, 5, 1, 2, 1, 3, 2, 3, 5]
def baseStart_1001197 : Nat := 118140960795 + 1001197 * 2 ^ 59
def prefixEnd_1001197 : Nat := 4983230072969 + 3 ^ 40 * 1001197 * 2
def baseEnd_1001197 : Nat := 57121698982180505092565

theorem tailTrace_1001197 : CollatzResearch.WordTrace tailWord_1001197 prefixEnd_1001197 57121698982180505092565 := by
  unfold tailWord_1001197
  simp only [CollatzResearch.WordTrace]
  refine ⟨36516654553841734679433845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24344436369227823119622563 36516654553841734679433845)
  ·
    refine ⟨3423436364422662626196923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36516654553841734679433845 3423436364422662626196923)
    ·
      refine ⟨5135154546633993939295385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3423436364422662626196923 5135154546633993939295385)
      ·
        refine ⟨3851365909975495454471539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5135154546633993939295385 3851365909975495454471539)
        ·
          refine ⟨5777048864963243181707309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3851365909975495454471539 5777048864963243181707309)
          ·
            refine ⟨2166393324361216193140241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5777048864963243181707309 2166393324361216193140241)
            ·
              refine ⟨1624794993270912144855181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2166393324361216193140241 1624794993270912144855181)
              ·
                refine ⟨609298122476592054320693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1624794993270912144855181 609298122476592054320693)
                ·
                  refine ⟨57121698982180505092565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609298122476592054320693 57121698982180505092565)
                  ·
                    rfl

theorem cell23_1001197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_1001197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001197 prefixEnd_1001197 := by exact prefixLift 1001197
  have htrace : WordTrace (prefixWord ++ tailWord_1001197) baseStart_1001197 baseEnd_1001197 := by
    simpa [prefixWord, tailWord_1001197, baseEnd_1001197] using wordTrace_append hprefix tailTrace_1001197
  have hstable : (prefixWord ++ tailWord_1001197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001197).length < 2 ^ (prefixWord ++ tailWord_1001197).sum := by decide
  have hdescent : baseEnd_1001197 < baseStart_1001197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001240 : List Nat := [2, 1, 2, 3, 1, 1, 4, 2, 3, 4]
def baseStart_1001240 : Nat := 118140960795 + 1001240 * 2 ^ 59
def prefixEnd_1001240 : Nat := 4983230072969 + 3 ^ 40 * 1001240 * 2
def baseEnd_1001240 : Nat := 171372456835922625865129

theorem tailTrace_1001240 : CollatzResearch.WordTrace tailWord_1001240 prefixEnd_1001240 171372456835922625865129 := by
  unfold tailWord_1001240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18259111446342976511624587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24345481928457302015499449 18259111446342976511624587)
  ·
    refine ⟨27388667169514464767436881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18259111446342976511624587 27388667169514464767436881)
    ·
      refine ⟨20541500377135848575577661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27388667169514464767436881 20541500377135848575577661)
      ·
        refine ⟨7703062641425943215841623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20541500377135848575577661 7703062641425943215841623)
        ·
          refine ⟨11554593962138914823762435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7703062641425943215841623 11554593962138914823762435)
          ·
            refine ⟨17331890943208372235643653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11554593962138914823762435 17331890943208372235643653)
            ·
              refine ⟨3249729551851569794183185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17331890943208372235643653 3249729551851569794183185)
              ·
                refine ⟨2437297163888677345637389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249729551851569794183185 2437297163888677345637389)
                ·
                  refine ⟨913986436458254004614021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2437297163888677345637389 913986436458254004614021)
                  ·
                    refine ⟨171372456835922625865129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 913986436458254004614021 171372456835922625865129)
                    ·
                      rfl

theorem cell23_1001240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 2, 3, 4].length) (baseStart_1001240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001240 prefixEnd_1001240 := by exact prefixLift 1001240
  have htrace : WordTrace (prefixWord ++ tailWord_1001240) baseStart_1001240 baseEnd_1001240 := by
    simpa [prefixWord, tailWord_1001240, baseEnd_1001240] using wordTrace_append hprefix tailTrace_1001240
  have hstable : (prefixWord ++ tailWord_1001240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001240).length < 2 ^ (prefixWord ++ tailWord_1001240).sum := by decide
  have hdescent : baseEnd_1001240 < baseStart_1001240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001250 : List Nat := [3, 3, 1, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1001250 : Nat := 118140960795 + 1001250 * 2 ^ 59
def prefixEnd_1001250 : Nat := 4983230072969 + 3 ^ 40 * 1001250 * 2
def baseEnd_1001250 : Nat := 514122505314312838470341

theorem tailTrace_1001250 : CollatzResearch.WordTrace tailWord_1001250 prefixEnd_1001250 514122505314312838470341 := by
  unfold tailWord_1001250
  simp only [CollatzResearch.WordTrace]
  refine ⟨9129646905662431182778301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24345725081766483154075469 9129646905662431182778301)
  ·
    refine ⟨3423617589623411693541863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9129646905662431182778301 3423617589623411693541863)
    ·
      refine ⟨5135426384435117540312795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3423617589623411693541863 5135426384435117540312795)
      ·
        refine ⟨7703139576652676310469193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5135426384435117540312795 7703139576652676310469193)
        ·
          refine ⟨5777354682489507232851895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7703139576652676310469193 5777354682489507232851895)
          ·
            refine ⟨8666032023734260849277843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5777354682489507232851895 8666032023734260849277843)
            ·
              refine ⟨12999048035601391273916765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8666032023734260849277843 12999048035601391273916765)
              ·
                refine ⟨4874643013350521727718787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12999048035601391273916765 4874643013350521727718787)
                ·
                  refine ⟨7311964520025782591578181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4874643013350521727718787 7311964520025782591578181)
                  ·
                    refine ⟨1370993347504834235920909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7311964520025782591578181 1370993347504834235920909)
                    ·
                      refine ⟨514122505314312838470341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1370993347504834235920909 514122505314312838470341)
                      ·
                        rfl

theorem cell23_1001250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1001250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001250 prefixEnd_1001250 := by exact prefixLift 1001250
  have htrace : WordTrace (prefixWord ++ tailWord_1001250) baseStart_1001250 baseEnd_1001250 := by
    simpa [prefixWord, tailWord_1001250, baseEnd_1001250] using wordTrace_append hprefix tailTrace_1001250
  have hstable : (prefixWord ++ tailWord_1001250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001250).length < 2 ^ (prefixWord ++ tailWord_1001250).sum := by decide
  have hdescent : baseEnd_1001250 < baseStart_1001250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001253 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 8]
def baseStart_1001253 : Nat := 118140960795 + 1001253 * 2 ^ 59
def prefixEnd_1001253 : Nat := 4983230072969 + 3 ^ 40 * 1001253 * 2
def baseEnd_1001253 : Nat := 57124893972919591859203

theorem tailTrace_1001253 : CollatzResearch.WordTrace tailWord_1001253 prefixEnd_1001253 57124893972919591859203 := by
  unfold tailWord_1001253
  simp only [CollatzResearch.WordTrace]
  refine ⟨36518697041638856243472413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24345798027759237495648275 36518697041638856243472413)
  ·
    refine ⟨13694511390614571091302155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36518697041638856243472413 13694511390614571091302155)
    ·
      refine ⟨20541767085921856636953233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13694511390614571091302155 20541767085921856636953233)
      ·
        refine ⟨15406325314441392477714925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20541767085921856636953233 15406325314441392477714925)
        ·
          refine ⟨5777371992915522179143097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15406325314441392477714925 5777371992915522179143097)
          ·
            refine ⟨4333028994686641634357323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5777371992915522179143097 4333028994686641634357323)
            ·
              refine ⟨6499543492029962451535985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4333028994686641634357323 6499543492029962451535985)
              ·
                refine ⟨4874657619022471838651989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6499543492029962451535985 4874657619022471838651989)
                ·
                  refine ⟨57124893972919591859203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4874657619022471838651989 57124893972919591859203)
                  ·
                    rfl

theorem cell23_1001253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_1001253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001253 prefixEnd_1001253 := by exact prefixLift 1001253
  have htrace : WordTrace (prefixWord ++ tailWord_1001253) baseStart_1001253 baseEnd_1001253 := by
    simpa [prefixWord, tailWord_1001253, baseEnd_1001253] using wordTrace_append hprefix tailTrace_1001253
  have hstable : (prefixWord ++ tailWord_1001253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001253).length < 2 ^ (prefixWord ++ tailWord_1001253).sum := by decide
  have hdescent : baseEnd_1001253 < baseStart_1001253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001263 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 3]
def baseStart_1001263 : Nat := 118140960795 + 1001263 * 2 ^ 59
def prefixEnd_1001263 : Nat := 4983230072969 + 3 ^ 40 * 1001263 * 2
def baseEnd_1001263 : Nat := 514129180562821287607781

theorem tailTrace_1001263 : CollatzResearch.WordTrace tailWord_1001263 prefixEnd_1001263 514129180562821287607781 := by
  unfold tailWord_1001263
  simp only [CollatzResearch.WordTrace]
  refine ⟨36519061771602627951336443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24346041181068418634224295 36519061771602627951336443)
  ·
    refine ⟨54778592657403941927004665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36519061771602627951336443 54778592657403941927004665)
    ·
      refine ⟨41083944493052956445253499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54778592657403941927004665 41083944493052956445253499)
      ·
        refine ⟨61625916739579434667880249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41083944493052956445253499 61625916739579434667880249)
        ·
          refine ⟨46219437554684576000910187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61625916739579434667880249 46219437554684576000910187)
          ·
            refine ⟨69329156332026864001365281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46219437554684576000910187 69329156332026864001365281)
            ·
              refine ⟨51996867249020148001023961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69329156332026864001365281 51996867249020148001023961)
              ·
                refine ⟨38997650436765111000767971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 51996867249020148001023961 38997650436765111000767971)
                ·
                  refine ⟨58496475655147666501151957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38997650436765111000767971 58496475655147666501151957)
                  ·
                    refine ⟨1371011148167523433620749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58496475655147666501151957 1371011148167523433620749)
                    ·
                      refine ⟨514129180562821287607781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1371011148167523433620749 514129180562821287607781)
                      ·
                        rfl

theorem cell23_1001263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 7, 3].length) (baseStart_1001263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001263 prefixEnd_1001263 := by exact prefixLift 1001263
  have htrace : WordTrace (prefixWord ++ tailWord_1001263) baseStart_1001263 baseEnd_1001263 := by
    simpa [prefixWord, tailWord_1001263, baseEnd_1001263] using wordTrace_append hprefix tailTrace_1001263
  have hstable : (prefixWord ++ tailWord_1001263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001263).length < 2 ^ (prefixWord ++ tailWord_1001263).sum := by decide
  have hdescent : baseEnd_1001263 < baseStart_1001263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001267 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 3]
def baseStart_1001267 : Nat := 118140960795 + 1001267 * 2 ^ 59
def prefixEnd_1001267 : Nat := 4983230072969 + 3 ^ 40 * 1001267 * 2
def baseEnd_1001267 : Nat := 514131234485439271957763

theorem tailTrace_1001267 : CollatzResearch.WordTrace tailWord_1001267 prefixEnd_1001267 514131234485439271957763 := by
  unfold tailWord_1001267
  simp only [CollatzResearch.WordTrace]
  refine ⟨36519207663588136634482055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24346138442392091089654703 36519207663588136634482055)
  ·
    refine ⟨54778811495382204951723083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36519207663588136634482055 54778811495382204951723083)
    ·
      refine ⟨82168217243073307427584625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54778811495382204951723083 82168217243073307427584625)
      ·
        refine ⟨61626162932304980570688469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82168217243073307427584625 61626162932304980570688469)
        ·
          refine ⟨1444363193725897982125511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 61626162932304980570688469 1444363193725897982125511)
          ·
            refine ⟨2166544790588846973188267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444363193725897982125511 2166544790588846973188267)
            ·
              refine ⟨3249817185883270459782401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2166544790588846973188267 3249817185883270459782401)
              ·
                refine ⟨2437362889412452844836801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3249817185883270459782401 2437362889412452844836801)
                ·
                  refine ⟨1828022167059339633627601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437362889412452844836801 1828022167059339633627601)
                  ·
                    refine ⟨1371016625294504725220701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1828022167059339633627601 1371016625294504725220701)
                    ·
                      refine ⟨514131234485439271957763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1371016625294504725220701 514131234485439271957763)
                      ·
                        rfl

theorem cell23_1001267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 2, 2, 3].length) (baseStart_1001267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001267 prefixEnd_1001267 := by exact prefixLift 1001267
  have htrace : WordTrace (prefixWord ++ tailWord_1001267) baseStart_1001267 baseEnd_1001267 := by
    simpa [prefixWord, tailWord_1001267, baseEnd_1001267] using wordTrace_append hprefix tailTrace_1001267
  have hstable : (prefixWord ++ tailWord_1001267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001267).length < 2 ^ (prefixWord ++ tailWord_1001267).sum := by decide
  have hdescent : baseEnd_1001267 < baseStart_1001267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001347 : List Nat := [1, 1, 1, 3, 4, 2, 2, 3, 2, 4]
def baseStart_1001347 : Nat := 118140960795 + 1001347 * 2 ^ 59
def prefixEnd_1001347 : Nat := 4983230072969 + 3 ^ 40 * 1001347 * 2
def baseEnd_1001347 : Nat := 171390770979266319652465

theorem tailTrace_1001347 : CollatzResearch.WordTrace tailWord_1001347 prefixEnd_1001347 171390770979266319652465 := by
  unfold tailWord_1001347
  simp only [CollatzResearch.WordTrace]
  refine ⟨36522125503298310297394295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24348083668865540198262863 36522125503298310297394295)
  ·
    refine ⟨54783188254947465446091443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36522125503298310297394295 54783188254947465446091443)
    ·
      refine ⟨82174782382421198169137165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54783188254947465446091443 82174782382421198169137165)
      ·
        refine ⟨30815543393407949313426437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82174782382421198169137165 30815543393407949313426437)
        ·
          refine ⟨5777914386263990496267457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30815543393407949313426437 5777914386263990496267457)
          ·
            refine ⟨4333435789697992872200593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5777914386263990496267457 4333435789697992872200593)
            ·
              refine ⟨3250076842273494654150445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4333435789697992872200593 3250076842273494654150445)
              ·
                refine ⟨1218778815852560495306417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3250076842273494654150445 1218778815852560495306417)
                ·
                  refine ⟨914084111889420371479813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1218778815852560495306417 914084111889420371479813)
                  ·
                    refine ⟨171390770979266319652465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914084111889420371479813 171390770979266319652465)
                    ·
                      rfl

theorem cell23_1001347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 3, 2, 4].length) (baseStart_1001347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001347 prefixEnd_1001347 := by exact prefixLift 1001347
  have htrace : WordTrace (prefixWord ++ tailWord_1001347) baseStart_1001347 baseEnd_1001347 := by
    simpa [prefixWord, tailWord_1001347, baseEnd_1001347] using wordTrace_append hprefix tailTrace_1001347
  have hstable : (prefixWord ++ tailWord_1001347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001347).length < 2 ^ (prefixWord ++ tailWord_1001347).sum := by decide
  have hdescent : baseEnd_1001347 < baseStart_1001347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001358 : List Nat := [4, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1001358 : Nat := 118140960795 + 1001358 * 2 ^ 59
def prefixEnd_1001358 : Nat := 4983230072969 + 3 ^ 40 * 1001358 * 2
def baseEnd_1001358 : Nat := 514177961224998415919845

theorem tailTrace_1001358 : CollatzResearch.WordTrace tailWord_1001358 prefixEnd_1001358 514177961224998415919845 := by
  unfold tailWord_1001358
  simp only [CollatzResearch.WordTrace]
  refine ⟨4565315838282307397005591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24348351137505639450696485 4565315838282307397005591)
  ·
    refine ⟨6847973757423461095508387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4565315838282307397005591 6847973757423461095508387)
    ·
      refine ⟨10271960636135191643262581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6847973757423461095508387 10271960636135191643262581)
      ·
        refine ⟨962996309637674216555867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10271960636135191643262581 962996309637674216555867)
        ·
          refine ⟨1444494464456511324833801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 962996309637674216555867 1444494464456511324833801)
          ·
            refine ⟨1083370848342383493625351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1444494464456511324833801 1083370848342383493625351)
            ·
              refine ⟨1625056272513575240438027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083370848342383493625351 1625056272513575240438027)
              ·
                refine ⟨2437584408770362860657041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625056272513575240438027 2437584408770362860657041)
                ·
                  refine ⟨1828188306577772145492781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437584408770362860657041 1828188306577772145492781)
                  ·
                    refine ⟨685570614966664554559793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828188306577772145492781 685570614966664554559793)
                    ·
                      refine ⟨514177961224998415919845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685570614966664554559793 514177961224998415919845)
                      ·
                        rfl

theorem cell23_1001358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1001358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001358 prefixEnd_1001358 := by exact prefixLift 1001358
  have htrace : WordTrace (prefixWord ++ tailWord_1001358) baseStart_1001358 baseEnd_1001358 := by
    simpa [prefixWord, tailWord_1001358, baseEnd_1001358] using wordTrace_append hprefix tailTrace_1001358
  have hstable : (prefixWord ++ tailWord_1001358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001358).length < 2 ^ (prefixWord ++ tailWord_1001358).sum := by decide
  have hdescent : baseEnd_1001358 < baseStart_1001358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001363 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6]
def baseStart_1001363 : Nat := 118140960795 + 1001363 * 2 ^ 59
def prefixEnd_1001363 : Nat := 4983230072969 + 3 ^ 40 * 1001363 * 2
def baseEnd_1001363 : Nat := 514180528628270896357321

theorem tailTrace_1001363 : CollatzResearch.WordTrace tailWord_1001363 prefixEnd_1001363 514180528628270896357321 := by
  unfold tailWord_1001363
  simp only [CollatzResearch.WordTrace]
  refine ⟨36522709071240345029976743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24348472714160230019984495 36522709071240345029976743)
  ·
    refine ⟨54784063606860517544965115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36522709071240345029976743 54784063606860517544965115)
    ·
      refine ⟨82176095410290776317447673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54784063606860517544965115 82176095410290776317447673)
      ·
        refine ⟨61632071557718082238085755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82176095410290776317447673 61632071557718082238085755)
        ·
          refine ⟨92448107336577123357128633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61632071557718082238085755 92448107336577123357128633)
          ·
            refine ⟨69336080502432842517846475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92448107336577123357128633 69336080502432842517846475)
            ·
              refine ⟨104004120753649263776769713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69336080502432842517846475 104004120753649263776769713)
              ·
                refine ⟨78003090565236947832577285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104004120753649263776769713 78003090565236947832577285)
                ·
                  refine ⟨14625579480981927718608241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78003090565236947832577285 14625579480981927718608241)
                  ·
                    refine ⟨10969184610736445788956181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14625579480981927718608241 10969184610736445788956181)
                    ·
                      refine ⟨514180528628270896357321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10969184610736445788956181 514180528628270896357321)
                      ·
                        rfl

theorem cell23_1001363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_1001363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001363 prefixEnd_1001363 := by exact prefixLift 1001363
  have htrace : WordTrace (prefixWord ++ tailWord_1001363) baseStart_1001363 baseEnd_1001363 := by
    simpa [prefixWord, tailWord_1001363, baseEnd_1001363] using wordTrace_append hprefix tailTrace_1001363
  have hstable : (prefixWord ++ tailWord_1001363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001363).length < 2 ^ (prefixWord ++ tailWord_1001363).sum := by decide
  have hdescent : baseEnd_1001363 < baseStart_1001363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001368 : List Nat := [2, 1, 2, 6, 2, 1, 2, 1, 1, 5]
def baseStart_1001368 : Nat := 118140960795 + 1001368 * 2 ^ 59
def prefixEnd_1001368 : Nat := 4983230072969 + 3 ^ 40 * 1001368 * 2
def baseEnd_1001368 : Nat := 171394365343847792264933

theorem tailTrace_1001368 : CollatzResearch.WordTrace tailWord_1001368 prefixEnd_1001368 171394365343847792264933 := by
  unfold tailWord_1001368
  simp only [CollatzResearch.WordTrace]
  refine ⟨18261445718111115441954379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24348594290814820589272505 18261445718111115441954379)
  ·
    refine ⟨27392168577166673162931569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18261445718111115441954379 27392168577166673162931569)
    ·
      refine ⟨20544126432875004872198677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27392168577166673162931569 20544126432875004872198677)
      ·
        refine ⟨963005926541015853384313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20544126432875004872198677 963005926541015853384313)
        ·
          refine ⟨722254444905761890038235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 963005926541015853384313 722254444905761890038235)
          ·
            refine ⟨1083381667358642835057353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722254444905761890038235 1083381667358642835057353)
            ·
              refine ⟨812536250518982126293015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1083381667358642835057353 812536250518982126293015)
              ·
                refine ⟨1218804375778473189439523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 812536250518982126293015 1218804375778473189439523)
                ·
                  refine ⟨1828206563667709784159285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1218804375778473189439523 1828206563667709784159285)
                  ·
                    refine ⟨171394365343847792264933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1828206563667709784159285 171394365343847792264933)
                    ·
                      rfl

theorem cell23_1001368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 1, 5].length) (baseStart_1001368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001368 prefixEnd_1001368 := by exact prefixLift 1001368
  have htrace : WordTrace (prefixWord ++ tailWord_1001368) baseStart_1001368 baseEnd_1001368 := by
    simpa [prefixWord, tailWord_1001368, baseEnd_1001368] using wordTrace_append hprefix tailTrace_1001368
  have hstable : (prefixWord ++ tailWord_1001368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001368).length < 2 ^ (prefixWord ++ tailWord_1001368).sum := by decide
  have hdescent : baseEnd_1001368 < baseStart_1001368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001440 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1001440 : Nat := 118140960795 + 1001440 * 2 ^ 59
def prefixEnd_1001440 : Nat := 4983230072969 + 3 ^ 40 * 1001440 * 2
def baseEnd_1001440 : Nat := 514220066638667095094467

theorem tailTrace_1001440 : CollatzResearch.WordTrace tailWord_1001440 prefixEnd_1001440 514220066638667095094467 := by
  unfold tailWord_1001440
  simp only [CollatzResearch.WordTrace]
  refine ⟨18262758745980693590264887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24350344994640924787019849 18262758745980693590264887)
  ·
    refine ⟨27394138118971040385397331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18262758745980693590264887 27394138118971040385397331)
    ·
      refine ⟨41091207178456560578095997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27394138118971040385397331 41091207178456560578095997)
      ·
        refine ⟨15409202691921210216785999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41091207178456560578095997 15409202691921210216785999)
        ·
          refine ⟨23113804037881815325178999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15409202691921210216785999 23113804037881815325178999)
          ·
            refine ⟨34670706056822722987768499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23113804037881815325178999 34670706056822722987768499)
            ·
              refine ⟨52006059085234084481652749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34670706056822722987768499 52006059085234084481652749)
              ·
                refine ⟨19502272156962781680619781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52006059085234084481652749 19502272156962781680619781)
                ·
                  refine ⟨3656676029430521565116209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19502272156962781680619781 3656676029430521565116209)
                  ·
                    refine ⟨2742507022072891173837157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3656676029430521565116209 2742507022072891173837157)
                    ·
                      refine ⟨514220066638667095094467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2742507022072891173837157 514220066638667095094467)
                      ·
                        rfl

theorem cell23_1001440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1001440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001440 prefixEnd_1001440 := by exact prefixLift 1001440
  have htrace : WordTrace (prefixWord ++ tailWord_1001440) baseStart_1001440 baseEnd_1001440 := by
    simpa [prefixWord, tailWord_1001440, baseEnd_1001440] using wordTrace_append hprefix tailTrace_1001440
  have hstable : (prefixWord ++ tailWord_1001440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001440).length < 2 ^ (prefixWord ++ tailWord_1001440).sum := by decide
  have hdescent : baseEnd_1001440 < baseStart_1001440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001444 : List Nat := [2, 3, 1, 1, 1, 1, 3, 3, 4, 2, 2]
def baseStart_1001444 : Nat := 118140960795 + 1001444 * 2 ^ 59
def prefixEnd_1001444 : Nat := 4983230072969 + 3 ^ 40 * 1001444 * 2
def baseEnd_1001444 : Nat := 514222120561285079444449

theorem tailTrace_1001444 : CollatzResearch.WordTrace tailWord_1001444 prefixEnd_1001444 514222120561285079444449 := by
  unfold tailWord_1001444
  simp only [CollatzResearch.WordTrace]
  refine ⟨18262831691973447931837693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24350442255964597242450257 18262831691973447931837693)
  ·
    refine ⟨6848561884490042974439135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18262831691973447931837693 6848561884490042974439135)
    ·
      refine ⟨10272842826735064461658703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6848561884490042974439135 10272842826735064461658703)
      ·
        refine ⟨15409264240102596692488055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10272842826735064461658703 15409264240102596692488055)
        ·
          refine ⟨23113896360153895038732083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15409264240102596692488055 23113896360153895038732083)
          ·
            refine ⟨34670844540230842558098125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23113896360153895038732083 34670844540230842558098125)
            ·
              refine ⟨13001566702586565959286797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34670844540230842558098125 13001566702586565959286797)
              ·
                refine ⟨4875587513469962234732549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13001566702586565959286797 4875587513469962234732549)
                ·
                  refine ⟨914172658775617919012353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4875587513469962234732549 914172658775617919012353)
                  ·
                    refine ⟨685629494081713439259265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 914172658775617919012353 685629494081713439259265)
                    ·
                      refine ⟨514222120561285079444449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685629494081713439259265 514222120561285079444449)
                      ·
                        rfl

theorem cell23_1001444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_1001444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001444 prefixEnd_1001444 := by exact prefixLift 1001444
  have htrace : WordTrace (prefixWord ++ tailWord_1001444) baseStart_1001444 baseEnd_1001444 := by
    simpa [prefixWord, tailWord_1001444, baseEnd_1001444] using wordTrace_append hprefix tailTrace_1001444
  have hstable : (prefixWord ++ tailWord_1001444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001444).length < 2 ^ (prefixWord ++ tailWord_1001444).sum := by decide
  have hdescent : baseEnd_1001444 < baseStart_1001444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001501 : List Nat := [1, 4, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1001501 : Nat := 118140960795 + 1001501 * 2 ^ 59
def prefixEnd_1001501 : Nat := 4983230072969 + 3 ^ 40 * 1001501 * 2
def baseEnd_1001501 : Nat := 57139043217621261825743

theorem tailTrace_1001501 : CollatzResearch.WordTrace tailWord_1001501 prefixEnd_1001501 57139043217621261825743 := by
  unfold tailWord_1001501
  simp only [CollatzResearch.WordTrace]
  refine ⟨36527742344740394598500357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24351828229826929732333571 36527742344740394598500357)
  ·
    refine ⟨6848951689638823987218817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36527742344740394598500357 6848951689638823987218817)
    ·
      refine ⟨5136713767229117990414113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6848951689638823987218817 5136713767229117990414113)
      ·
        refine ⟨3852535325421838492810585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5136713767229117990414113 3852535325421838492810585)
        ·
          refine ⟨2889401494066378869607939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3852535325421838492810585 2889401494066378869607939)
          ·
            refine ⟨4334102241099568304411909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2889401494066378869607939 4334102241099568304411909)
            ·
              refine ⟨812644170206169057077233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4334102241099568304411909 812644170206169057077233)
              ·
                refine ⟨609483127654626792807925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812644170206169057077233 609483127654626792807925)
                ·
                  refine ⟨57139043217621261825743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609483127654626792807925 57139043217621261825743)
                  ·
                    rfl

theorem cell23_1001501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1001501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001501 prefixEnd_1001501 := by exact prefixLift 1001501
  have htrace : WordTrace (prefixWord ++ tailWord_1001501) baseStart_1001501 baseEnd_1001501 := by
    simpa [prefixWord, tailWord_1001501, baseEnd_1001501] using wordTrace_append hprefix tailTrace_1001501
  have hstable : (prefixWord ++ tailWord_1001501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001501).length < 2 ^ (prefixWord ++ tailWord_1001501).sum := by decide
  have hdescent : baseEnd_1001501 < baseStart_1001501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001511 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1001511 : Nat := 118140960795 + 1001511 * 2 ^ 59
def prefixEnd_1001511 : Nat := 4983230072969 + 3 ^ 40 * 1001511 * 2
def baseEnd_1001511 : Nat := 514256523765136317306641

theorem tailTrace_1001511 : CollatzResearch.WordTrace tailWord_1001511 prefixEnd_1001511 514256523765136317306641 := by
  unfold tailWord_1001511
  simp only [CollatzResearch.WordTrace]
  refine ⟨36528107074704166306364387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24352071383136110870909591 36528107074704166306364387)
  ·
    refine ⟨54792160612056249459546581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36528107074704166306364387 54792160612056249459546581)
    ·
      refine ⟨1284191264345068346708123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 54792160612056249459546581 1284191264345068346708123)
      ·
        refine ⟨1926286896517602520062185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1284191264345068346708123 1926286896517602520062185)
        ·
          refine ⟨1444715172388201890046639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1926286896517602520062185 1444715172388201890046639)
          ·
            refine ⟨2167072758582302835069959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444715172388201890046639 2167072758582302835069959)
            ·
              refine ⟨3250609137873454252604939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167072758582302835069959 3250609137873454252604939)
              ·
                refine ⟨4875913706810181378907409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250609137873454252604939 4875913706810181378907409)
                ·
                  refine ⟨3656935280107636034180557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4875913706810181378907409 3656935280107636034180557)
                  ·
                    refine ⟨1371350730040363512817709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3656935280107636034180557 1371350730040363512817709)
                    ·
                      refine ⟨514256523765136317306641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1371350730040363512817709 514256523765136317306641)
                      ·
                        rfl

theorem cell23_1001511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1001511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001511 prefixEnd_1001511 := by exact prefixLift 1001511
  have htrace : WordTrace (prefixWord ++ tailWord_1001511) baseStart_1001511 baseEnd_1001511 := by
    simpa [prefixWord, tailWord_1001511, baseEnd_1001511] using wordTrace_append hprefix tailTrace_1001511
  have hstable : (prefixWord ++ tailWord_1001511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001511).length < 2 ^ (prefixWord ++ tailWord_1001511).sum := by decide
  have hdescent : baseEnd_1001511 < baseStart_1001511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001527 : List Nat := [1, 1, 3, 1, 2, 2, 3, 1, 5, 4]
def baseStart_1001527 : Nat := 118140960795 + 1001527 * 2 ^ 59
def prefixEnd_1001527 : Nat := 4983230072969 + 3 ^ 40 * 1001527 * 2
def baseEnd_1001527 : Nat := 171421579818536084902189

theorem tailTrace_1001527 : CollatzResearch.WordTrace tailWord_1001527 prefixEnd_1001527 171421579818536084902189 := by
  unfold tailWord_1001527
  simp only [CollatzResearch.WordTrace]
  refine ⟨36528690642646201038946835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24352460428430800692631223 36528690642646201038946835)
  ·
    refine ⟨54793035963969301558420253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36528690642646201038946835 54793035963969301558420253)
    ·
      refine ⟨20547388486488488084407595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54793035963969301558420253 20547388486488488084407595)
      ·
        refine ⟨30821082729732732126611393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20547388486488488084407595 30821082729732732126611393)
        ·
          refine ⟨23115812047299549094958545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30821082729732732126611393 23115812047299549094958545)
          ·
            refine ⟨17336859035474661821218909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23115812047299549094958545 17336859035474661821218909)
            ·
              refine ⟨6501322138302998182957091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17336859035474661821218909 6501322138302998182957091)
              ·
                refine ⟨9751983207454497274435637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6501322138302998182957091 9751983207454497274435637)
                ·
                  refine ⟨914248425698859119478341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9751983207454497274435637 914248425698859119478341)
                  ·
                    refine ⟨171421579818536084902189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914248425698859119478341 171421579818536084902189)
                    ·
                      rfl

theorem cell23_1001527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_1001527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001527 prefixEnd_1001527 := by exact prefixLift 1001527
  have htrace : WordTrace (prefixWord ++ tailWord_1001527) baseStart_1001527 baseEnd_1001527 := by
    simpa [prefixWord, tailWord_1001527, baseEnd_1001527] using wordTrace_append hprefix tailTrace_1001527
  have hstable : (prefixWord ++ tailWord_1001527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001527).length < 2 ^ (prefixWord ++ tailWord_1001527).sum := by decide
  have hdescent : baseEnd_1001527 < baseStart_1001527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001557 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 8]
def baseStart_1001557 : Nat := 118140960795 + 1001557 * 2 ^ 59
def prefixEnd_1001557 : Nat := 4983230072969 + 3 ^ 40 * 1001557 * 2
def baseEnd_1001557 : Nat := 57142238208360348592381

theorem tailTrace_1001557 : CollatzResearch.WordTrace tailWord_1001557 prefixEnd_1001557 57142238208360348592381 := by
  unfold tailWord_1001557
  simp only [CollatzResearch.WordTrace]
  refine ⟨36529784832537516162538925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24353189888358344108359283 36529784832537516162538925)
  ·
    refine ⟨13698669312201568560952097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36529784832537516162538925 13698669312201568560952097)
    ·
      refine ⟨10274001984151176420714073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13698669312201568560952097 10274001984151176420714073)
      ·
        refine ⟨7705501488113382315535555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10274001984151176420714073 7705501488113382315535555)
        ·
          refine ⟨11558252232170073473303333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7705501488113382315535555 11558252232170073473303333)
          ·
            refine ⟨2167172293531888776244375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11558252232170073473303333 2167172293531888776244375)
            ·
              refine ⟨3250758440297833164366563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167172293531888776244375 3250758440297833164366563)
              ·
                refine ⟨4876137660446749746549845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3250758440297833164366563 4876137660446749746549845)
                ·
                  refine ⟨57142238208360348592381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4876137660446749746549845 57142238208360348592381)
                  ·
                    rfl

theorem cell23_1001557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_1001557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001557 prefixEnd_1001557 := by exact prefixLift 1001557
  have htrace : WordTrace (prefixWord ++ tailWord_1001557) baseStart_1001557 baseEnd_1001557 := by
    simpa [prefixWord, tailWord_1001557, baseEnd_1001557] using wordTrace_append hprefix tailTrace_1001557
  have hstable : (prefixWord ++ tailWord_1001557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001557).length < 2 ^ (prefixWord ++ tailWord_1001557).sum := by decide
  have hdescent : baseEnd_1001557 < baseStart_1001557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001594 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2]
def baseStart_1001594 : Nat := 118140960795 + 1001594 * 2 ^ 59
def prefixEnd_1001594 : Nat := 4983230072969 + 3 ^ 40 * 1001594 * 2
def baseEnd_1001594 : Nat := 514299142659459492568759

theorem tailTrace_1001594 : CollatzResearch.WordTrace tailWord_1001594 prefixEnd_1001594 514299142659459492568759 := by
  unfold tailWord_1001594
  simp only [CollatzResearch.WordTrace]
  refine ⟨9132783583350867870408959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24354089555602314321090557 9132783583350867870408959)
  ·
    refine ⟨13699175375026301805613439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9132783583350867870408959 13699175375026301805613439)
    ·
      refine ⟨20548763062539452708420159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699175375026301805613439 20548763062539452708420159)
      ·
        refine ⟨30823144593809179062630239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20548763062539452708420159 30823144593809179062630239)
        ·
          refine ⟨46234716890713768593945359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30823144593809179062630239 46234716890713768593945359)
          ·
            refine ⟨69352075336070652890918039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46234716890713768593945359 69352075336070652890918039)
            ·
              refine ⟨104028113004105979336377059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69352075336070652890918039 104028113004105979336377059)
              ·
                refine ⟨156042169506158969004565589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104028113004105979336377059 156042169506158969004565589)
                ·
                  refine ⟨1828619173900300418022253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 156042169506158969004565589 1828619173900300418022253)
                  ·
                    refine ⟨685732190212612656758345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1828619173900300418022253 685732190212612656758345)
                    ·
                      refine ⟨514299142659459492568759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685732190212612656758345 514299142659459492568759)
                      ·
                        rfl

theorem cell23_1001594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 8, 3, 2].length) (baseStart_1001594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001594 prefixEnd_1001594 := by exact prefixLift 1001594
  have htrace : WordTrace (prefixWord ++ tailWord_1001594) baseStart_1001594 baseEnd_1001594 := by
    simpa [prefixWord, tailWord_1001594, baseEnd_1001594] using wordTrace_append hprefix tailTrace_1001594
  have hstable : (prefixWord ++ tailWord_1001594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001594).length < 2 ^ (prefixWord ++ tailWord_1001594).sum := by decide
  have hdescent : baseEnd_1001594 < baseStart_1001594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001604 : List Nat := [2, 3, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_1001604 : Nat := 118140960795 + 1001604 * 2 ^ 59
def prefixEnd_1001604 : Nat := 4983230072969 + 3 ^ 40 * 1001604 * 2
def baseEnd_1001604 : Nat := 171434759155334817814571

theorem tailTrace_1001604 : CollatzResearch.WordTrace tailWord_1001604 prefixEnd_1001604 171434759155334817814571 := by
  unfold tailWord_1001604
  simp only [CollatzResearch.WordTrace]
  refine ⟨18265749531683621594749933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24354332708911495459666577 18265749531683621594749933)
  ·
    refine ⟨6849656074381358098031225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18265749531683621594749933 6849656074381358098031225)
    ·
      refine ⟨5137242055786018573523419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6849656074381358098031225 5137242055786018573523419)
      ·
        refine ⟨7705863083679027860285129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5137242055786018573523419 7705863083679027860285129)
        ·
          refine ⟨5779397312759270895213847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7705863083679027860285129 5779397312759270895213847)
          ·
            refine ⟨8669095969138906342820771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779397312759270895213847 8669095969138906342820771)
            ·
              refine ⟨13003643953708359514231157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669095969138906342820771 13003643953708359514231157)
              ·
                refine ⟨1219091620660158704459171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13003643953708359514231157 1219091620660158704459171)
                ·
                  refine ⟨1828637430990238056688757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219091620660158704459171 1828637430990238056688757)
                  ·
                    refine ⟨171434759155334817814571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1828637430990238056688757 171434759155334817814571)
                    ·
                      rfl

theorem cell23_1001604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_1001604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001604 prefixEnd_1001604 := by exact prefixLift 1001604
  have htrace : WordTrace (prefixWord ++ tailWord_1001604) baseStart_1001604 baseEnd_1001604 := by
    simpa [prefixWord, tailWord_1001604, baseEnd_1001604] using wordTrace_append hprefix tailTrace_1001604
  have hstable : (prefixWord ++ tailWord_1001604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001604).length < 2 ^ (prefixWord ++ tailWord_1001604).sum := by decide
  have hdescent : baseEnd_1001604 < baseStart_1001604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001627 : List Nat := [1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5]
def baseStart_1001627 : Nat := 118140960795 + 1001627 * 2 ^ 59
def prefixEnd_1001627 : Nat := 4983230072969 + 3 ^ 40 * 1001627 * 2
def baseEnd_1001627 : Nat := 514316087521057863456107

theorem tailTrace_1001627 : CollatzResearch.WordTrace tailWord_1001627 prefixEnd_1001627 514316087521057863456107 := by
  unfold tailWord_1001627
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532337942283918117587135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24354891961522612078391423 36532337942283918117587135)
  ·
    refine ⟨54798506913425877176380703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36532337942283918117587135 54798506913425877176380703)
    ·
      refine ⟨82197760370138815764571055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54798506913425877176380703 82197760370138815764571055)
      ·
        refine ⟨123296640555208223646856583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82197760370138815764571055 123296640555208223646856583)
        ·
          refine ⟨184944960832812335470284875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123296640555208223646856583 184944960832812335470284875)
          ·
            refine ⟨277417441249218503205427313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 184944960832812335470284875 277417441249218503205427313)
            ·
              refine ⟨208063080936913877404070485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 277417441249218503205427313 208063080936913877404070485)
              ·
                refine ⟨2438239229729459500828951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 208063080936913877404070485 2438239229729459500828951)
                ·
                  refine ⟨3657358844594189251243427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2438239229729459500828951 3657358844594189251243427)
                  ·
                    refine ⟨5486038266891283876865141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3657358844594189251243427 5486038266891283876865141)
                    ·
                      refine ⟨514316087521057863456107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5486038266891283876865141 514316087521057863456107)
                      ·
                        rfl

theorem cell23_1001627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 5].length) (baseStart_1001627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001627 prefixEnd_1001627 := by exact prefixLift 1001627
  have htrace : WordTrace (prefixWord ++ tailWord_1001627) baseStart_1001627 baseEnd_1001627 := by
    simpa [prefixWord, tailWord_1001627, baseEnd_1001627] using wordTrace_append hprefix tailTrace_1001627
  have hstable : (prefixWord ++ tailWord_1001627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001627).length < 2 ^ (prefixWord ++ tailWord_1001627).sum := by decide
  have hdescent : baseEnd_1001627 < baseStart_1001627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001637 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_1001637 : Nat := 118140960795 + 1001637 * 2 ^ 59
def prefixEnd_1001637 : Nat := 4983230072969 + 3 ^ 40 * 1001637 * 2
def baseEnd_1001637 : Nat := 514321222327602824331061

theorem tailTrace_1001637 : CollatzResearch.WordTrace tailWord_1001637 prefixEnd_1001637 514321222327602824331061 := by
  unfold tailWord_1001637
  simp only [CollatzResearch.WordTrace]
  refine ⟨36532702672247689825451165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24355135114831793216967443 36532702672247689825451165)
  ·
    refine ⟨13699763502092883684544187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36532702672247689825451165 13699763502092883684544187)
    ·
      refine ⟨20549645253139325526816281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13699763502092883684544187 20549645253139325526816281)
      ·
        refine ⟨15412233939854494145112211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20549645253139325526816281 15412233939854494145112211)
        ·
          refine ⟨23118350909781741217668317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15412233939854494145112211 23118350909781741217668317)
          ·
            refine ⟨8669381591168152956625619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23118350909781741217668317 8669381591168152956625619)
            ·
              refine ⟨13004072386752229434938429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669381591168152956625619 13004072386752229434938429)
              ·
                refine ⟨4876527145032086038101911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13004072386752229434938429 4876527145032086038101911)
                ·
                  refine ⟨7314790717548129057152867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4876527145032086038101911 7314790717548129057152867)
                  ·
                    refine ⟨10972186076322193585729301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7314790717548129057152867 10972186076322193585729301)
                    ·
                      refine ⟨514321222327602824331061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10972186076322193585729301 514321222327602824331061)
                      ·
                        rfl

theorem cell23_1001637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_1001637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001637 prefixEnd_1001637 := by exact prefixLift 1001637
  have htrace : WordTrace (prefixWord ++ tailWord_1001637) baseStart_1001637 baseEnd_1001637 := by
    simpa [prefixWord, tailWord_1001637, baseEnd_1001637] using wordTrace_append hprefix tailTrace_1001637
  have hstable : (prefixWord ++ tailWord_1001637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001637).length < 2 ^ (prefixWord ++ tailWord_1001637).sum := by decide
  have hdescent : baseEnd_1001637 < baseStart_1001637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001668 : List Nat := [2, 3, 3, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1001668 : Nat := 118140960795 + 1001668 * 2 ^ 59
def prefixEnd_1001668 : Nat := 4983230072969 + 3 ^ 40 * 1001668 * 2
def baseEnd_1001668 : Nat := 171445713409297401014473

theorem tailTrace_1001668 : CollatzResearch.WordTrace tailWord_1001668 prefixEnd_1001668 171445713409297401014473 := by
  unfold tailWord_1001668
  simp only [CollatzResearch.WordTrace]
  refine ⟨18266916667567691059914829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24355888890090254746553105 18266916667567691059914829)
  ·
    refine ⟨6850093750337884147468061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18266916667567691059914829 6850093750337884147468061)
    ·
      refine ⟨2568785156376706555300523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6850093750337884147468061 2568785156376706555300523)
      ·
        refine ⟨3853177734565059832950785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2568785156376706555300523 3853177734565059832950785)
        ·
          refine ⟨2889883300923794874713089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3853177734565059832950785 2889883300923794874713089)
          ·
            refine ⟨2167412475692846156034817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2889883300923794874713089 2167412475692846156034817)
            ·
              refine ⟨1625559356769634617026113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167412475692846156034817 1625559356769634617026113)
              ·
                refine ⟨1219169517577225962769585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1625559356769634617026113 1219169517577225962769585)
                ·
                  refine ⟨914377138182919472077189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219169517577225962769585 914377138182919472077189)
                  ·
                    refine ⟨171445713409297401014473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914377138182919472077189 171445713409297401014473)
                    ·
                      rfl

theorem cell23_1001668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1001668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001668 prefixEnd_1001668 := by exact prefixLift 1001668
  have htrace : WordTrace (prefixWord ++ tailWord_1001668) baseStart_1001668 baseEnd_1001668 := by
    simpa [prefixWord, tailWord_1001668, baseEnd_1001668] using wordTrace_append hprefix tailTrace_1001668
  have hstable : (prefixWord ++ tailWord_1001668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001668).length < 2 ^ (prefixWord ++ tailWord_1001668).sum := by decide
  have hdescent : baseEnd_1001668 < baseStart_1001668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001674 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1001674 : Nat := 118140960795 + 1001674 * 2 ^ 59
def prefixEnd_1001674 : Nat := 4983230072969 + 3 ^ 40 * 1001674 * 2
def baseEnd_1001674 : Nat := 514340221111819179568391

theorem tailTrace_1001674 : CollatzResearch.WordTrace tailWord_1001674 prefixEnd_1001674 514340221111819179568391 := by
  unfold tailWord_1001674
  simp only [CollatzResearch.WordTrace]
  refine ⟨9133513043278411286137019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24356034782075763429698717 9133513043278411286137019)
  ·
    refine ⟨13700269564917616929205529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9133513043278411286137019 13700269564917616929205529)
    ·
      refine ⟨10275202173688212696904147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13700269564917616929205529 10275202173688212696904147)
      ·
        refine ⟨15412803260532319045356221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275202173688212696904147 15412803260532319045356221)
        ·
          refine ⟨5779801222699619642008583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15412803260532319045356221 5779801222699619642008583)
          ·
            refine ⟨8669701834049429463012875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5779801222699619642008583 8669701834049429463012875)
            ·
              refine ⟨13004552751074144194519313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669701834049429463012875 13004552751074144194519313)
              ·
                refine ⟨9753414563305608145889485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13004552751074144194519313 9753414563305608145889485)
                ·
                  refine ⟨3657530461239603054708557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9753414563305608145889485 3657530461239603054708557)
                  ·
                    refine ⟨1371573922964851145515709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3657530461239603054708557 1371573922964851145515709)
                    ·
                      refine ⟨514340221111819179568391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1371573922964851145515709 514340221111819179568391)
                      ·
                        rfl

theorem cell23_1001674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1001674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001674 prefixEnd_1001674 := by exact prefixLift 1001674
  have htrace : WordTrace (prefixWord ++ tailWord_1001674) baseStart_1001674 baseEnd_1001674 := by
    simpa [prefixWord, tailWord_1001674, baseEnd_1001674] using wordTrace_append hprefix tailTrace_1001674
  have hstable : (prefixWord ++ tailWord_1001674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001674).length < 2 ^ (prefixWord ++ tailWord_1001674).sum := by decide
  have hdescent : baseEnd_1001674 < baseStart_1001674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001687 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1001687 : Nat := 118140960795 + 1001687 * 2 ^ 59
def prefixEnd_1001687 : Nat := 4983230072969 + 3 ^ 40 * 1001687 * 2
def baseEnd_1001687 : Nat := 514346896360327628705831

theorem tailTrace_1001687 : CollatzResearch.WordTrace tailWord_1001687 prefixEnd_1001687 514346896360327628705831 := by
  unfold tailWord_1001687
  simp only [CollatzResearch.WordTrace]
  refine ⟨36534526322066548364771315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24356350881377698909847543 36534526322066548364771315)
  ·
    refine ⟨54801789483099822547156973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36534526322066548364771315 54801789483099822547156973)
    ·
      refine ⟨20550671056162433455183865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54801789483099822547156973 20550671056162433455183865)
      ·
        refine ⟨15413003292121825091387899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20550671056162433455183865 15413003292121825091387899)
        ·
          refine ⟨23119504938182737637081849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15413003292121825091387899 23119504938182737637081849)
          ·
            refine ⟨17339628703637053227811387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23119504938182737637081849 17339628703637053227811387)
            ·
              refine ⟨26009443055455579841717081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17339628703637053227811387 26009443055455579841717081)
              ·
                refine ⟨19507082291591684881287811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26009443055455579841717081 19507082291591684881287811)
                ·
                  refine ⟨29260623437387527321931717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19507082291591684881287811 29260623437387527321931717)
                  ·
                    refine ⟨5486366894510161372862197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29260623437387527321931717 5486366894510161372862197)
                    ·
                      refine ⟨514346896360327628705831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5486366894510161372862197 514346896360327628705831)
                      ·
                        rfl

theorem cell23_1001687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1001687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001687 prefixEnd_1001687 := by exact prefixLift 1001687
  have htrace : WordTrace (prefixWord ++ tailWord_1001687) baseStart_1001687 baseEnd_1001687 := by
    simpa [prefixWord, tailWord_1001687, baseEnd_1001687] using wordTrace_append hprefix tailTrace_1001687
  have hstable : (prefixWord ++ tailWord_1001687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001687).length < 2 ^ (prefixWord ++ tailWord_1001687).sum := by decide
  have hdescent : baseEnd_1001687 < baseStart_1001687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001692 : List Nat := [2, 2, 5, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1001692 : Nat := 118140960795 + 1001692 * 2 ^ 59
def prefixEnd_1001692 : Nat := 4983230072969 + 3 ^ 40 * 1001692 * 2
def baseEnd_1001692 : Nat := 514349463763600109143309

theorem tailTrace_1001692 : CollatzResearch.WordTrace tailWord_1001692 prefixEnd_1001692 514349463763600109143309 := by
  unfold tailWord_1001692
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267354343524217109351665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24356472458032289479135553 18267354343524217109351665)
  ·
    refine ⟨13700515757643162832013749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18267354343524217109351665 13700515757643162832013749)
    ·
      refine ⟨1284423352279046515501289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13700515757643162832013749 1284423352279046515501289)
      ·
        refine ⟨963317514209284886625967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1284423352279046515501289 963317514209284886625967)
        ·
          refine ⟨1444976271313927329938951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 963317514209284886625967 1444976271313927329938951)
          ·
            refine ⟨2167464406970890994908427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1444976271313927329938951 2167464406970890994908427)
            ·
              refine ⟨3251196610456336492362641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2167464406970890994908427 3251196610456336492362641)
              ·
                refine ⟨2438397457842252369271981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3251196610456336492362641 2438397457842252369271981)
                ·
                  refine ⟨914399046690844638476993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2438397457842252369271981 914399046690844638476993)
                  ·
                    refine ⟨685799285018133478857745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 914399046690844638476993 685799285018133478857745)
                    ·
                      refine ⟨514349463763600109143309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685799285018133478857745 514349463763600109143309)
                      ·
                        rfl

theorem cell23_1001692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1001692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001692 prefixEnd_1001692 := by exact prefixLift 1001692
  have htrace : WordTrace (prefixWord ++ tailWord_1001692) baseStart_1001692 baseEnd_1001692 := by
    simpa [prefixWord, tailWord_1001692, baseEnd_1001692] using wordTrace_append hprefix tailTrace_1001692
  have hstable : (prefixWord ++ tailWord_1001692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001692).length < 2 ^ (prefixWord ++ tailWord_1001692).sum := by decide
  have hdescent : baseEnd_1001692 < baseStart_1001692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001707 : List Nat := [1, 1, 1, 1, 2, 5, 1, 2, 1, 8]
def baseStart_1001707 : Nat := 118140960795 + 1001707 * 2 ^ 59
def prefixEnd_1001707 : Nat := 4983230072969 + 3 ^ 40 * 1001707 * 2
def baseEnd_1001707 : Nat := 171452388657805850151913

theorem tailTrace_1001707 : CollatzResearch.WordTrace tailWord_1001707 prefixEnd_1001707 171452388657805850151913 := by
  unfold tailWord_1001707
  simp only [CollatzResearch.WordTrace]
  refine ⟨36535255781994091780499375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24356837187996061186999583 36535255781994091780499375)
  ·
    refine ⟨54802883672991137670749063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36535255781994091780499375 54802883672991137670749063)
    ·
      refine ⟨82204325509486706506123595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54802883672991137670749063 82204325509486706506123595)
      ·
        refine ⟨123306488264230059759185393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82204325509486706506123595 123306488264230059759185393)
        ·
          refine ⟨92479866198172544819389045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123306488264230059759185393 92479866198172544819389045)
          ·
            refine ⟨8669987456078676076817723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 92479866198172544819389045 8669987456078676076817723)
            ·
              refine ⟨13004981184118014115226585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8669987456078676076817723 13004981184118014115226585)
              ·
                refine ⟨9753735888088510586419939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13004981184118014115226585 9753735888088510586419939)
                ·
                  refine ⟨14630603832132765879629909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9753735888088510586419939 14630603832132765879629909)
                  ·
                    refine ⟨171452388657805850151913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14630603832132765879629909 171452388657805850151913)
                    ·
                      rfl

theorem cell23_1001707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 2, 1, 8].length) (baseStart_1001707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001707 prefixEnd_1001707 := by exact prefixLift 1001707
  have htrace : WordTrace (prefixWord ++ tailWord_1001707) baseStart_1001707 baseEnd_1001707 := by
    simpa [prefixWord, tailWord_1001707, baseEnd_1001707] using wordTrace_append hprefix tailTrace_1001707
  have hstable : (prefixWord ++ tailWord_1001707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001707).length < 2 ^ (prefixWord ++ tailWord_1001707).sum := by decide
  have hdescent : baseEnd_1001707 < baseStart_1001707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001724 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 2, 6]
def baseStart_1001724 : Nat := 118140960795 + 1001724 * 2 ^ 59
def prefixEnd_1001724 : Nat := 4983230072969 + 3 ^ 40 * 1001724 * 2
def baseEnd_1001724 : Nat := 171455298381514661314387

theorem tailTrace_1001724 : CollatzResearch.WordTrace tailWord_1001724 prefixEnd_1001724 171455298381514661314387 := by
  unfold tailWord_1001724
  simp only [CollatzResearch.WordTrace]
  refine ⟨18267937911466251841934113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24357250548621669122578817 18267937911466251841934113)
  ·
    refine ⟨13700953433599688881450585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18267937911466251841934113 13700953433599688881450585)
    ·
      refine ⟨10275715075199766661087939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13700953433599688881450585 10275715075199766661087939)
      ·
        refine ⟨15413572612799649991631909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10275715075199766661087939 15413572612799649991631909)
        ·
          refine ⟨2890044864899934373430983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15413572612799649991631909 2890044864899934373430983)
          ·
            refine ⟨4335067297349901560146475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890044864899934373430983 4335067297349901560146475)
            ·
              refine ⟨6502600946024852340219713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335067297349901560146475 6502600946024852340219713)
              ·
                refine ⟨4876950709518639255164785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6502600946024852340219713 4876950709518639255164785)
                ·
                  refine ⟨3657713032138979441373589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4876950709518639255164785 3657713032138979441373589)
                  ·
                    refine ⟨171455298381514661314387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3657713032138979441373589 171455298381514661314387)
                    ·
                      rfl

theorem cell23_1001724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_1001724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001724 prefixEnd_1001724 := by exact prefixLift 1001724
  have htrace : WordTrace (prefixWord ++ tailWord_1001724) baseStart_1001724 baseEnd_1001724 := by
    simpa [prefixWord, tailWord_1001724, baseEnd_1001724] using wordTrace_append hprefix tailTrace_1001724
  have hstable : (prefixWord ++ tailWord_1001724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001724).length < 2 ^ (prefixWord ++ tailWord_1001724).sum := by decide
  have hdescent : baseEnd_1001724 < baseStart_1001724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001747 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9]
def baseStart_1001747 : Nat := 118140960795 + 1001747 * 2 ^ 59
def prefixEnd_1001747 : Nat := 4983230072969 + 3 ^ 40 * 1001747 * 2
def baseEnd_1001747 : Nat := 514377705199597393955555

theorem tailTrace_1001747 : CollatzResearch.WordTrace tailWord_1001747 prefixEnd_1001747 514377705199597393955555 := by
  unfold tailWord_1001747
  simp only [CollatzResearch.WordTrace]
  refine ⟨36536714701849178611955495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24357809801232785741303663 36536714701849178611955495)
  ·
    refine ⟨54805072052773767917933243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36536714701849178611955495 54805072052773767917933243)
    ·
      refine ⟨82207608079160651876899865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54805072052773767917933243 82207608079160651876899865)
      ·
        refine ⟨61655706059370488907674899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82207608079160651876899865 61655706059370488907674899)
        ·
          refine ⟨92483559089055733361512349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61655706059370488907674899 92483559089055733361512349)
          ·
            refine ⟨34681334658395900010567131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92483559089055733361512349 34681334658395900010567131)
            ·
              refine ⟨52022001987593850015850697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34681334658395900010567131 52022001987593850015850697)
              ·
                refine ⟨39016501490695387511888023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52022001987593850015850697 39016501490695387511888023)
                ·
                  refine ⟨58524752236043081267832035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39016501490695387511888023 58524752236043081267832035)
                  ·
                    refine ⟨87787128354064621901748053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58524752236043081267832035 87787128354064621901748053)
                    ·
                      refine ⟨514377705199597393955555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 87787128354064621901748053 514377705199597393955555)
                      ·
                        rfl

theorem cell23_1001747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_1001747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001747 prefixEnd_1001747 := by exact prefixLift 1001747
  have htrace : WordTrace (prefixWord ++ tailWord_1001747) baseStart_1001747 baseEnd_1001747 := by
    simpa [prefixWord, tailWord_1001747, baseEnd_1001747] using wordTrace_append hprefix tailTrace_1001747
  have hstable : (prefixWord ++ tailWord_1001747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001747).length < 2 ^ (prefixWord ++ tailWord_1001747).sum := by decide
  have hdescent : baseEnd_1001747 < baseStart_1001747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001784 : List Nat := [2, 1, 2, 1, 3, 1, 3, 1, 4, 5]
def baseStart_1001784 : Nat := 118140960795 + 1001784 * 2 ^ 59
def prefixEnd_1001784 : Nat := 4983230072969 + 3 ^ 40 * 1001784 * 2
def baseEnd_1001784 : Nat := 171465567994604583064295

theorem tailTrace_1001784 : CollatzResearch.WordTrace tailWord_1001784 prefixEnd_1001784 171465567994604583064295 := by
  unfold tailWord_1001784
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269032101357566965526203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24358709468476755954034937 18269032101357566965526203)
  ·
    refine ⟨27403548152036350448289305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18269032101357566965526203 27403548152036350448289305)
    ·
      refine ⟨20552661114027262836216979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27403548152036350448289305 20552661114027262836216979)
      ·
        refine ⟨30828991671040894254325469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20552661114027262836216979 30828991671040894254325469)
        ·
          refine ⟨11560871876640335345372051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30828991671040894254325469 11560871876640335345372051)
          ·
            refine ⟨17341307814960503018058077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11560871876640335345372051 17341307814960503018058077)
            ·
              refine ⟨6502990430610188631771779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17341307814960503018058077 6502990430610188631771779)
              ·
                refine ⟨9754485645915282947657669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6502990430610188631771779 9754485645915282947657669)
                ·
                  refine ⟨1828966058609115552685813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9754485645915282947657669 1828966058609115552685813)
                  ·
                    refine ⟨171465567994604583064295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1828966058609115552685813 171465567994604583064295)
                    ·
                      rfl

theorem cell23_1001784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 5].length) (baseStart_1001784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001784 prefixEnd_1001784 := by exact prefixLift 1001784
  have htrace : WordTrace (prefixWord ++ tailWord_1001784) baseStart_1001784 baseEnd_1001784 := by
    simpa [prefixWord, tailWord_1001784, baseEnd_1001784] using wordTrace_append hprefix tailTrace_1001784
  have hstable : (prefixWord ++ tailWord_1001784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001784).length < 2 ^ (prefixWord ++ tailWord_1001784).sum := by decide
  have hdescent : baseEnd_1001784 < baseStart_1001784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001788 : List Nat := [2, 2, 2, 2, 1, 2, 5, 2, 5]
def baseStart_1001788 : Nat := 118140960795 + 1001788 * 2 ^ 59
def prefixEnd_1001788 : Nat := 4983230072969 + 3 ^ 40 * 1001788 * 2
def baseEnd_1001788 : Nat := 57155417545159081504763

theorem tailTrace_1001788 : CollatzResearch.WordTrace tailWord_1001788 prefixEnd_1001788 57155417545159081504763 := by
  unfold tailWord_1001788
  simp only [CollatzResearch.WordTrace]
  refine ⟨18269105047350321307099009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24358806729800428409465345 18269105047350321307099009)
  ·
    refine ⟨13701828785512740980324257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18269105047350321307099009 13701828785512740980324257)
    ·
      refine ⟨10276371589134555735243193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13701828785512740980324257 10276371589134555735243193)
      ·
        refine ⟨7707278691850916801432395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10276371589134555735243193 7707278691850916801432395)
        ·
          refine ⟨11560918037776375202148593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7707278691850916801432395 11560918037776375202148593)
          ·
            refine ⟨8670688528332281401611445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11560918037776375202148593 8670688528332281401611445)
            ·
              refine ⟨812877049531151381401073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8670688528332281401611445 812877049531151381401073)
              ·
                refine ⟨609657787148363536050805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812877049531151381401073 609657787148363536050805)
                ·
                  refine ⟨57155417545159081504763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609657787148363536050805 57155417545159081504763)
                  ·
                    rfl

theorem cell23_1001788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 2, 5].length) (baseStart_1001788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001788 prefixEnd_1001788 := by exact prefixLift 1001788
  have htrace : WordTrace (prefixWord ++ tailWord_1001788) baseStart_1001788 baseEnd_1001788 := by
    simpa [prefixWord, tailWord_1001788, baseEnd_1001788] using wordTrace_append hprefix tailTrace_1001788
  have hstable : (prefixWord ++ tailWord_1001788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001788).length < 2 ^ (prefixWord ++ tailWord_1001788).sum := by decide
  have hdescent : baseEnd_1001788 < baseStart_1001788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001791 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 2, 5, 2]
def baseStart_1001791 : Nat := 118140960795 + 1001791 * 2 ^ 59
def prefixEnd_1001791 : Nat := 4983230072969 + 3 ^ 40 * 1001791 * 2
def baseEnd_1001791 : Nat := 514400298348395221805353

theorem tailTrace_1001791 : CollatzResearch.WordTrace tailWord_1001791 prefixEnd_1001791 514400298348395221805353 := by
  unfold tailWord_1001791
  simp only [CollatzResearch.WordTrace]
  refine ⟨36538319513689774126557227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24358879675793182751038151 36538319513689774126557227)
  ·
    refine ⟨54807479270534661189835841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36538319513689774126557227 54807479270534661189835841)
    ·
      refine ⟨41105609452900995892376881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54807479270534661189835841 41105609452900995892376881)
      ·
        refine ⟨30829207089675746919282661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41105609452900995892376881 30829207089675746919282661)
        ·
          refine ⟨5780476329314202547365499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30829207089675746919282661 5780476329314202547365499)
          ·
            refine ⟨8670714493971303821048249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5780476329314202547365499 8670714493971303821048249)
            ·
              refine ⟨6503035870478477865786187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8670714493971303821048249 6503035870478477865786187)
              ·
                refine ⟨9754553805717716798679281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6503035870478477865786187 9754553805717716798679281)
                ·
                  refine ⟨7315915354288287599009461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9754553805717716798679281 7315915354288287599009461)
                  ·
                    refine ⟨685867064464526962407137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7315915354288287599009461 685867064464526962407137)
                    ·
                      refine ⟨514400298348395221805353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685867064464526962407137 514400298348395221805353)
                      ·
                        rfl

theorem cell23_1001791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 5, 2].length) (baseStart_1001791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001791 prefixEnd_1001791 := by exact prefixLift 1001791
  have htrace : WordTrace (prefixWord ++ tailWord_1001791) baseStart_1001791 baseEnd_1001791 := by
    simpa [prefixWord, tailWord_1001791, baseEnd_1001791] using wordTrace_append hprefix tailTrace_1001791
  have hstable : (prefixWord ++ tailWord_1001791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001791).length < 2 ^ (prefixWord ++ tailWord_1001791).sum := by decide
  have hdescent : baseEnd_1001791 < baseStart_1001791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001905 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1001905 : Nat := 118140960795 + 1001905 * 2 ^ 59
def prefixEnd_1001905 : Nat := 4983230072969 + 3 ^ 40 * 1001905 * 2
def baseEnd_1001905 : Nat := 514458835143007775779829

theorem tailTrace_1001905 : CollatzResearch.WordTrace tailWord_1001905 prefixEnd_1001905 514458835143007775779829 := by
  unfold tailWord_1001905
  simp only [CollatzResearch.WordTrace]
  refine ⟨36542477435276771596207169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24361651623517847730804779 36542477435276771596207169)
  ·
    refine ⟨27406858076457578697155377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36542477435276771596207169 27406858076457578697155377)
    ·
      refine ⟨20555143557343184022866533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27406858076457578697155377 20555143557343184022866533)
      ·
        refine ⟨3854089417001847004287475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20555143557343184022866533 3854089417001847004287475)
        ·
          refine ⟨5781134125502770506431213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3854089417001847004287475 5781134125502770506431213)
          ·
            refine ⟨2167925297063538939911705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5781134125502770506431213 2167925297063538939911705)
            ·
              refine ⟨1625943972797654204933779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2167925297063538939911705 1625943972797654204933779)
              ·
                refine ⟨2438915959196481307400669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625943972797654204933779 2438915959196481307400669)
                ·
                  refine ⟨914593484698680490275251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2438915959196481307400669 914593484698680490275251)
                  ·
                    refine ⟨1371890227048020735412877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914593484698680490275251 1371890227048020735412877)
                    ·
                      refine ⟨514458835143007775779829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1371890227048020735412877 514458835143007775779829)
                      ·
                        rfl

theorem cell23_1001905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1001905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001905 prefixEnd_1001905 := by exact prefixLift 1001905
  have htrace : WordTrace (prefixWord ++ tailWord_1001905) baseStart_1001905 baseEnd_1001905 := by
    simpa [prefixWord, tailWord_1001905, baseEnd_1001905] using wordTrace_append hprefix tailTrace_1001905
  have hstable : (prefixWord ++ tailWord_1001905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001905).length < 2 ^ (prefixWord ++ tailWord_1001905).sum := by decide
  have hdescent : baseEnd_1001905 < baseStart_1001905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001928 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_1001928 : Nat := 118140960795 + 1001928 * 2 ^ 59
def prefixEnd_1001928 : Nat := 4983230072969 + 3 ^ 40 * 1001928 * 2
def baseEnd_1001928 : Nat := 514470645198061185792223

theorem tailTrace_1001928 : CollatzResearch.WordTrace tailWord_1001928 prefixEnd_1001928 514470645198061185792223 := by
  unfold tailWord_1001928
  simp only [CollatzResearch.WordTrace]
  refine ⟨18271658157096723262147219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24362210876128964349529625 18271658157096723262147219)
  ·
    refine ⟨27407487235645084893220829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18271658157096723262147219 27407487235645084893220829)
    ·
      refine ⟨10277807713366906834957811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27407487235645084893220829 10277807713366906834957811)
      ·
        refine ⟨15416711570050360252436717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10277807713366906834957811 15416711570050360252436717)
        ·
          refine ⟨5781266838768885094663769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15416711570050360252436717 5781266838768885094663769)
          ·
            refine ⟨4335950129076663820997827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5781266838768885094663769 4335950129076663820997827)
            ·
              refine ⟨6503925193614995731496741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4335950129076663820997827 6503925193614995731496741)
              ·
                refine ⟨1219485973802811699655639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6503925193614995731496741 1219485973802811699655639)
                ·
                  refine ⟨1829228960704217549483459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1219485973802811699655639 1829228960704217549483459)
                  ·
                    refine ⟨2743843441056326324225189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1829228960704217549483459 2743843441056326324225189)
                    ·
                      refine ⟨514470645198061185792223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2743843441056326324225189 514470645198061185792223)
                      ·
                        rfl

theorem cell23_1001928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_1001928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001928 prefixEnd_1001928 := by exact prefixLift 1001928
  have htrace : WordTrace (prefixWord ++ tailWord_1001928) baseStart_1001928 baseEnd_1001928 := by
    simpa [prefixWord, tailWord_1001928, baseEnd_1001928] using wordTrace_append hprefix tailTrace_1001928
  have hstable : (prefixWord ++ tailWord_1001928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001928).length < 2 ^ (prefixWord ++ tailWord_1001928).sum := by decide
  have hdescent : baseEnd_1001928 < baseStart_1001928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001951 : List Nat := [1, 1, 2, 3, 3, 4, 9]
def baseStart_1001951 : Nat := 118140960795 + 1001951 * 2 ^ 59
def prefixEnd_1001951 : Nat := 4983230072969 + 3 ^ 40 * 1001951 * 2
def baseEnd_1001951 : Nat := 6351635250038451800057

theorem tailTrace_1001951 : CollatzResearch.WordTrace tailWord_1001951 prefixEnd_1001951 6351635250038451800057 := by
  unfold tailWord_1001951
  simp only [CollatzResearch.WordTrace]
  refine ⟨36544155193110121452381707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24362770128740080968254471 36544155193110121452381707)
  ·
    refine ⟨54816232789665182178572561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36544155193110121452381707 54816232789665182178572561)
    ·
      refine ⟨41112174592248886633929421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54816232789665182178572561 41112174592248886633929421)
      ·
        refine ⟨15417065472093332487723533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41112174592248886633929421 15417065472093332487723533)
        ·
          refine ⟨5781399552034999682896325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15417065472093332487723533 5781399552034999682896325)
          ·
            refine ⟨1084012416006562440543061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5781399552034999682896325 1084012416006562440543061)
            ·
              refine ⟨6351635250038451800057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1084012416006562440543061 6351635250038451800057)
              ·
                rfl

theorem cell23_1001951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 9].length) (baseStart_1001951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001951 prefixEnd_1001951 := by exact prefixLift 1001951
  have htrace : WordTrace (prefixWord ++ tailWord_1001951) baseStart_1001951 baseEnd_1001951 := by
    simpa [prefixWord, tailWord_1001951, baseEnd_1001951] using wordTrace_append hprefix tailTrace_1001951
  have hstable : (prefixWord ++ tailWord_1001951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001951).length < 2 ^ (prefixWord ++ tailWord_1001951).sum := by decide
  have hdescent : baseEnd_1001951 < baseStart_1001951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001961 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 3]
def baseStart_1001961 : Nat := 118140960795 + 1001961 * 2 ^ 59
def prefixEnd_1001961 : Nat := 4983230072969 + 3 ^ 40 * 1001961 * 2
def baseEnd_1001961 : Nat := 514487590059659556679571

theorem tailTrace_1001961 : CollatzResearch.WordTrace tailWord_1001961 prefixEnd_1001961 514487590059659556679571 := by
  unfold tailWord_1001961
  simp only [CollatzResearch.WordTrace]
  refine ⟨36544519923073893160245737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24363013282049262106830491 36544519923073893160245737)
  ·
    refine ⟨27408389942305419870184303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36544519923073893160245737 27408389942305419870184303)
    ·
      refine ⟨41112584913458129805276455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27408389942305419870184303 41112584913458129805276455)
      ·
        refine ⟨61668877370187194707914683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41112584913458129805276455 61668877370187194707914683)
        ·
          refine ⟨92503316055280792061872025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61668877370187194707914683 92503316055280792061872025)
          ·
            refine ⟨69377487041460594046404019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92503316055280792061872025 69377487041460594046404019)
            ·
              refine ⟨104066230562190891069606029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69377487041460594046404019 104066230562190891069606029)
              ·
                refine ⟨39024836460821584151102261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104066230562190891069606029 39024836460821584151102261)
                ·
                  refine ⟨3658578418202023514165837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39024836460821584151102261 3658578418202023514165837)
                  ·
                    refine ⟨1371966906825758817812189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3658578418202023514165837 1371966906825758817812189)
                    ·
                      refine ⟨514487590059659556679571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1371966906825758817812189 514487590059659556679571)
                      ·
                        rfl

theorem cell23_1001961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 5, 3, 3].length) (baseStart_1001961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001961 prefixEnd_1001961 := by exact prefixLift 1001961
  have htrace : WordTrace (prefixWord ++ tailWord_1001961) baseStart_1001961 baseEnd_1001961 := by
    simpa [prefixWord, tailWord_1001961, baseEnd_1001961] using wordTrace_append hprefix tailTrace_1001961
  have hstable : (prefixWord ++ tailWord_1001961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001961).length < 2 ^ (prefixWord ++ tailWord_1001961).sum := by decide
  have hdescent : baseEnd_1001961 < baseStart_1001961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001962 : List Nat := [3, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2]
def baseStart_1001962 : Nat := 118140960795 + 1001962 * 2 ^ 59
def prefixEnd_1001962 : Nat := 4983230072969 + 3 ^ 40 * 1001962 * 2
def baseEnd_1001962 : Nat := 514488103540314052767067

theorem tailTrace_1001962 : CollatzResearch.WordTrace tailWord_1001962 prefixEnd_1001962 514488103540314052767067 := by
  unfold tailWord_1001962
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136139099017567582758035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24363037597380180220688093 9136139099017567582758035)
  ·
    refine ⟨13704208648526351374137053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9136139099017567582758035 13704208648526351374137053)
    ·
      refine ⟨5139078243197381765301395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13704208648526351374137053 5139078243197381765301395)
      ·
        refine ⟨7708617364796072647952093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139078243197381765301395 7708617364796072647952093)
        ·
          refine ⟨2890731511798527242982035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7708617364796072647952093 2890731511798527242982035)
          ·
            refine ⟨4336097267697790864473053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2890731511798527242982035 4336097267697790864473053)
            ·
              refine ⟨1626036475386671574177395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4336097267697790864473053 1626036475386671574177395)
              ·
                refine ⟨2439054713080007361266093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626036475386671574177395 2439054713080007361266093)
                ·
                  refine ⟨914645517405002760474785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2439054713080007361266093 914645517405002760474785)
                  ·
                    refine ⟨685984138053752070356089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 914645517405002760474785 685984138053752070356089)
                    ·
                      refine ⟨514488103540314052767067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 685984138053752070356089 514488103540314052767067)
                      ·
                        rfl

theorem cell23_1001962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_1001962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001962 prefixEnd_1001962 := by exact prefixLift 1001962
  have htrace : WordTrace (prefixWord ++ tailWord_1001962) baseStart_1001962 baseEnd_1001962 := by
    simpa [prefixWord, tailWord_1001962, baseEnd_1001962] using wordTrace_append hprefix tailTrace_1001962
  have hstable : (prefixWord ++ tailWord_1001962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001962).length < 2 ^ (prefixWord ++ tailWord_1001962).sum := by decide
  have hdescent : baseEnd_1001962 < baseStart_1001962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1001978 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3]
def baseStart_1001978 : Nat := 118140960795 + 1001978 * 2 ^ 59
def prefixEnd_1001978 : Nat := 4983230072969 + 3 ^ 40 * 1001978 * 2
def baseEnd_1001978 : Nat := 514496319230785990166993

theorem tailTrace_1001978 : CollatzResearch.WordTrace tailWord_1001978 prefixEnd_1001978 514496319230785990166993 := by
  unfold tailWord_1001978
  simp only [CollatzResearch.WordTrace]
  refine ⟨9136284991003076265903647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24363426642674870042409725 9136284991003076265903647)
  ·
    refine ⟨13704427486504614398855471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9136284991003076265903647 13704427486504614398855471)
    ·
      refine ⟨20556641229756921598283207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13704427486504614398855471 20556641229756921598283207)
      ·
        refine ⟨30834961844635382397424811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20556641229756921598283207 30834961844635382397424811)
        ·
          refine ⟨46252442766953073596137217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30834961844635382397424811 46252442766953073596137217)
          ·
            refine ⟨34689332075214805197102913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46252442766953073596137217 34689332075214805197102913)
            ·
              refine ⟨26016999056411103897827185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34689332075214805197102913 26016999056411103897827185)
              ·
                refine ⟨19512749292308327923370389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26016999056411103897827185 19512749292308327923370389)
                ·
                  refine ⟨914660123076952871407987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 19512749292308327923370389 914660123076952871407987)
                  ·
                    refine ⟨1371990184615429307111981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914660123076952871407987 1371990184615429307111981)
                    ·
                      refine ⟨514496319230785990166993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1371990184615429307111981 514496319230785990166993)
                      ·
                        rfl

theorem cell23_1001978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3].length) (baseStart_1001978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1001978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1001978 prefixEnd_1001978 := by exact prefixLift 1001978
  have htrace : WordTrace (prefixWord ++ tailWord_1001978) baseStart_1001978 baseEnd_1001978 := by
    simpa [prefixWord, tailWord_1001978, baseEnd_1001978] using wordTrace_append hprefix tailTrace_1001978
  have hstable : (prefixWord ++ tailWord_1001978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1001978).length < 2 ^ (prefixWord ++ tailWord_1001978).sum := by decide
  have hdescent : baseEnd_1001978 < baseStart_1001978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1001978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002012 : List Nat := [2, 2, 3, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_1002012 : Nat := 118140960795 + 1002012 * 2 ^ 59
def prefixEnd_1002012 : Nat := 4983230072969 + 3 ^ 40 * 1002012 * 2
def baseEnd_1002012 : Nat := 514513777573038857141837

theorem tailTrace_1002012 : CollatzResearch.WordTrace tailWord_1002012 prefixEnd_1002012 514513777573038857141837 := by
  unfold tailWord_1002012
  simp only [CollatzResearch.WordTrace]
  refine ⟨18273190022944564435176145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24364253363926085913568193 18273190022944564435176145)
  ·
    refine ⟨13704892517208423326382109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18273190022944564435176145 13704892517208423326382109)
    ·
      refine ⟨5139334693953158747393291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13704892517208423326382109 5139334693953158747393291)
      ·
        refine ⟨7709002040929738121089937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5139334693953158747393291 7709002040929738121089937)
        ·
          refine ⟨5781751530697303590817453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7709002040929738121089937 5781751530697303590817453)
          ·
            refine ⟨2168156824011488846556545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5781751530697303590817453 2168156824011488846556545)
            ·
              refine ⟨1626117618008616634917409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168156824011488846556545 1626117618008616634917409)
              ·
                refine ⟨1219588213506462476188057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1626117618008616634917409 1219588213506462476188057)
                ·
                  refine ⟨914691160129846857141043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219588213506462476188057 914691160129846857141043)
                  ·
                    refine ⟨1372036740194770285711565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914691160129846857141043 1372036740194770285711565)
                    ·
                      refine ⟨514513777573038857141837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372036740194770285711565 514513777573038857141837)
                      ·
                        rfl

theorem cell23_1002012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_1002012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002012 prefixEnd_1002012 := by exact prefixLift 1002012
  have htrace : WordTrace (prefixWord ++ tailWord_1002012) baseStart_1002012 baseEnd_1002012 := by
    simpa [prefixWord, tailWord_1002012, baseEnd_1002012] using wordTrace_append hprefix tailTrace_1002012
  have hstable : (prefixWord ++ tailWord_1002012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002012).length < 2 ^ (prefixWord ++ tailWord_1002012).sum := by decide
  have hdescent : baseEnd_1002012 < baseStart_1002012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002021 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_1002021 : Nat := 118140960795 + 1002021 * 2 ^ 59
def prefixEnd_1002021 : Nat := 4983230072969 + 3 ^ 40 * 1002021 * 2
def baseEnd_1002021 : Nat := 514518398898929321929295

theorem tailTrace_1002021 : CollatzResearch.WordTrace tailWord_1002021 prefixEnd_1002021 514518398898929321929295 := by
  unfold tailWord_1002021
  simp only [CollatzResearch.WordTrace]
  refine ⟨36546708302856523407429917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24364472201904348938286611 36546708302856523407429917)
  ·
    refine ⟨13705015613571196277786219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36546708302856523407429917 13705015613571196277786219)
    ·
      refine ⟨20557523420356794416679329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13705015613571196277786219 20557523420356794416679329)
      ·
        refine ⟨15418142565267595812509497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20557523420356794416679329 15418142565267595812509497)
        ·
          refine ⟨11563606923950696859382123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15418142565267595812509497 11563606923950696859382123)
          ·
            refine ⟨17345410385926045289073185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11563606923950696859382123 17345410385926045289073185)
            ·
              refine ⟨13009057789444533966804889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17345410385926045289073185 13009057789444533966804889)
              ·
                refine ⟨9756793342083400475103667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13009057789444533966804889 9756793342083400475103667)
                ·
                  refine ⟨14635190013125100712655501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9756793342083400475103667 14635190013125100712655501)
                  ·
                    refine ⟨5488196254921912767245813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14635190013125100712655501 5488196254921912767245813)
                    ·
                      refine ⟨514518398898929321929295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5488196254921912767245813 514518398898929321929295)
                      ·
                        rfl

theorem cell23_1002021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_1002021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002021 prefixEnd_1002021 := by exact prefixLift 1002021
  have htrace : WordTrace (prefixWord ++ tailWord_1002021) baseStart_1002021 baseEnd_1002021 := by
    simpa [prefixWord, tailWord_1002021, baseEnd_1002021] using wordTrace_append hprefix tailTrace_1002021
  have hstable : (prefixWord ++ tailWord_1002021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002021).length < 2 ^ (prefixWord ++ tailWord_1002021).sum := by decide
  have hdescent : baseEnd_1002021 < baseStart_1002021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002035 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 1, 4, 2]
def baseStart_1002035 : Nat := 118140960795 + 1002035 * 2 ^ 59
def prefixEnd_1002035 : Nat := 4983230072969 + 3 ^ 40 * 1002035 * 2
def baseEnd_1002035 : Nat := 514525587628092267154231

theorem tailTrace_1002035 : CollatzResearch.WordTrace tailWord_1002035 prefixEnd_1002035 514525587628092267154231 := by
  unfold tailWord_1002035
  simp only [CollatzResearch.WordTrace]
  refine ⟨36547218924805803798439559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24364812616537202532293039 36547218924805803798439559)
  ·
    refine ⟨54820828387208705697659339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36547218924805803798439559 54820828387208705697659339)
    ·
      refine ⟨82231242580813058546489009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54820828387208705697659339 82231242580813058546489009)
      ·
        refine ⟨61673431935609793909866757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82231242580813058546489009 61673431935609793909866757)
        ·
          refine ⟨11563768487926836358100017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61673431935609793909866757 11563768487926836358100017)
          ·
            refine ⟨8672826365945127268575013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11563768487926836358100017 8672826365945127268575013)
            ·
              refine ⟨1626154943614711362857815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8672826365945127268575013 1626154943614711362857815)
              ·
                refine ⟨2439232415422067044286723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1626154943614711362857815 2439232415422067044286723)
                ·
                  refine ⟨3658848623133100566430085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439232415422067044286723 3658848623133100566430085)
                  ·
                    refine ⟨686034116837456356205641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3658848623133100566430085 686034116837456356205641)
                    ·
                      refine ⟨514525587628092267154231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686034116837456356205641 514525587628092267154231)
                      ·
                        rfl

theorem cell23_1002035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4, 2].length) (baseStart_1002035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002035 prefixEnd_1002035 := by exact prefixLift 1002035
  have htrace : WordTrace (prefixWord ++ tailWord_1002035) baseStart_1002035 baseEnd_1002035 := by
    simpa [prefixWord, tailWord_1002035, baseEnd_1002035] using wordTrace_append hprefix tailTrace_1002035
  have hstable : (prefixWord ++ tailWord_1002035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002035).length < 2 ^ (prefixWord ++ tailWord_1002035).sum := by decide
  have hdescent : baseEnd_1002035 < baseStart_1002035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002108 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_1002108 : Nat := 118140960795 + 1002108 * 2 ^ 59
def prefixEnd_1002108 : Nat := 4983230072969 + 3 ^ 40 * 1002108 * 2
def baseEnd_1002108 : Nat := 514563071715870481541395

theorem tailTrace_1002108 : CollatzResearch.WordTrace tailWord_1002108 prefixEnd_1002108 514563071715870481541395 := by
  unfold tailWord_1002108
  simp only [CollatzResearch.WordTrace]
  refine ⟨18274940726770668632923489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24366587635694224843897985 18274940726770668632923489)
  ·
    refine ⟨13706205545078001474692617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18274940726770668632923489 13706205545078001474692617)
    ·
      refine ⟨10279654158808501106019463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13706205545078001474692617 10279654158808501106019463)
      ·
        refine ⟨15419481238212751659029195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279654158808501106019463 15419481238212751659029195)
        ·
          refine ⟨23129221857319127488543793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15419481238212751659029195 23129221857319127488543793)
          ·
            refine ⟨17346916392989345616407845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23129221857319127488543793 17346916392989345616407845)
            ·
              refine ⟨3252546823685502303076471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17346916392989345616407845 3252546823685502303076471)
              ·
                refine ⟨4878820235528253454614707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3252546823685502303076471 4878820235528253454614707)
                ·
                  refine ⟨7318230353292380181922061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4878820235528253454614707 7318230353292380181922061)
                  ·
                    refine ⟨2744336382484642568220773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7318230353292380181922061 2744336382484642568220773)
                    ·
                      refine ⟨514563071715870481541395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2744336382484642568220773 514563071715870481541395)
                      ·
                        rfl

theorem cell23_1002108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_1002108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002108 prefixEnd_1002108 := by exact prefixLift 1002108
  have htrace : WordTrace (prefixWord ++ tailWord_1002108) baseStart_1002108 baseEnd_1002108 := by
    simpa [prefixWord, tailWord_1002108, baseEnd_1002108] using wordTrace_append hprefix tailTrace_1002108
  have hstable : (prefixWord ++ tailWord_1002108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002108).length < 2 ^ (prefixWord ++ tailWord_1002108).sum := by decide
  have hdescent : baseEnd_1002108 < baseStart_1002108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002109 : List Nat := [1, 4, 1, 1, 6, 1, 1, 3, 5]
def baseStart_1002109 : Nat := 118140960795 + 1002109 * 2 ^ 59
def prefixEnd_1002109 : Nat := 4983230072969 + 3 ^ 40 * 1002109 * 2
def baseEnd_1002109 : Nat := 57173731688502775292099

theorem tailTrace_1002109 : CollatzResearch.WordTrace tailWord_1002109 prefixEnd_1002109 57173731688502775292099 := by
  unfold tailWord_1002109
  simp only [CollatzResearch.WordTrace]
  refine ⟨36549917926537714436633381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24366611951025142957755587 36549917926537714436633381)
  ·
    refine ⟨6853109611225821456868759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36549917926537714436633381 6853109611225821456868759)
    ·
      refine ⟨10279664416838732185303139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853109611225821456868759 10279664416838732185303139)
      ·
        refine ⟨15419496625258098277954709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10279664416838732185303139 15419496625258098277954709)
        ·
          refine ⟨722788904308973356779127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 15419496625258098277954709 722788904308973356779127)
          ·
            refine ⟨1084183356463460035168691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722788904308973356779127 1084183356463460035168691)
            ·
              refine ⟨1626275034695190052753037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084183356463460035168691 1626275034695190052753037)
              ·
                refine ⟨609853138010696269782389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1626275034695190052753037 609853138010696269782389)
                ·
                  refine ⟨57173731688502775292099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 609853138010696269782389 57173731688502775292099)
                  ·
                    rfl

theorem cell23_1002109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_1002109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002109 prefixEnd_1002109 := by exact prefixLift 1002109
  have htrace : WordTrace (prefixWord ++ tailWord_1002109) baseStart_1002109 baseEnd_1002109 := by
    simpa [prefixWord, tailWord_1002109, baseEnd_1002109] using wordTrace_append hprefix tailTrace_1002109
  have hstable : (prefixWord ++ tailWord_1002109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002109).length < 2 ^ (prefixWord ++ tailWord_1002109).sum := by decide
  have hdescent : baseEnd_1002109 < baseStart_1002109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002142 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_1002142 : Nat := 118140960795 + 1002142 * 2 ^ 59
def prefixEnd_1002142 : Nat := 4983230072969 + 3 ^ 40 * 1002142 * 2
def baseEnd_1002142 : Nat := 514580530058123348516239

theorem tailTrace_1002142 : CollatzResearch.WordTrace tailWord_1002142 prefixEnd_1002142 514580530058123348516239 := by
  unfold tailWord_1002142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4568890191927270134073085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24367414356945440715056453 4568890191927270134073085)
  ·
    refine ⟨1713333821972726300277407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4568890191927270134073085 1713333821972726300277407)
    ·
      refine ⟨2570000732959089450416111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713333821972726300277407 2570000732959089450416111)
      ·
        refine ⟨3855001099438634175624167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2570000732959089450416111 3855001099438634175624167)
        ·
          refine ⟨5782501649157951263436251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855001099438634175624167 5782501649157951263436251)
          ·
            refine ⟨8673752473736926895154377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5782501649157951263436251 8673752473736926895154377)
            ·
              refine ⟨6505314355302695171365783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8673752473736926895154377 6505314355302695171365783)
              ·
                refine ⟨9757971532954042757048675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6505314355302695171365783 9757971532954042757048675)
                ·
                  refine ⟨14636957299431064135573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9757971532954042757048675 14636957299431064135573013)
                  ·
                    refine ⟨686107373410831131354985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14636957299431064135573013 686107373410831131354985)
                    ·
                      refine ⟨514580530058123348516239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686107373410831131354985 514580530058123348516239)
                      ·
                        rfl

theorem cell23_1002142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_1002142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002142 prefixEnd_1002142 := by exact prefixLift 1002142
  have htrace : WordTrace (prefixWord ++ tailWord_1002142) baseStart_1002142 baseEnd_1002142 := by
    simpa [prefixWord, tailWord_1002142, baseEnd_1002142] using wordTrace_append hprefix tailTrace_1002142
  have hstable : (prefixWord ++ tailWord_1002142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002142).length < 2 ^ (prefixWord ++ tailWord_1002142).sum := by decide
  have hdescent : baseEnd_1002142 < baseStart_1002142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002186 : List Nat := [3, 1, 2, 1, 4, 3, 2, 2, 1, 4]
def baseStart_1002186 : Nat := 118140960795 + 1002186 * 2 ^ 59
def prefixEnd_1002186 : Nat := 4983230072969 + 3 ^ 40 * 1002186 * 2
def baseEnd_1002186 : Nat := 171534374402307058788679

theorem tailTrace_1002186 : CollatzResearch.WordTrace tailWord_1002186 prefixEnd_1002186 171534374402307058788679 := by
  unfold tailWord_1002186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138181586814689146796603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24368484231505837724790941 9138181586814689146796603)
  ·
    refine ⟨13707272380222033720194905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9138181586814689146796603 13707272380222033720194905)
    ·
      refine ⟨10280454285166525290146179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13707272380222033720194905 10280454285166525290146179)
      ·
        refine ⟨15420681427749787935219269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10280454285166525290146179 15420681427749787935219269)
        ·
          refine ⟨2891377767703085237853613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15420681427749787935219269 2891377767703085237853613)
          ·
            refine ⟨1084266662888656964195105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2891377767703085237853613 1084266662888656964195105)
            ·
              refine ⟨813199997166492723146329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084266662888656964195105 813199997166492723146329)
              ·
                refine ⟨609899997874869542359747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813199997166492723146329 609899997874869542359747)
                ·
                  refine ⟨914849996812304313539621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609899997874869542359747 914849996812304313539621)
                  ·
                    refine ⟨171534374402307058788679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914849996812304313539621 171534374402307058788679)
                    ·
                      rfl

theorem cell23_1002186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_1002186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002186 prefixEnd_1002186 := by exact prefixLift 1002186
  have htrace : WordTrace (prefixWord ++ tailWord_1002186) baseStart_1002186 baseEnd_1002186 := by
    simpa [prefixWord, tailWord_1002186, baseEnd_1002186] using wordTrace_append hprefix tailTrace_1002186
  have hstable : (prefixWord ++ tailWord_1002186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002186).length < 2 ^ (prefixWord ++ tailWord_1002186).sum := by decide
  have hdescent : baseEnd_1002186 < baseStart_1002186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002225 : List Nat := [1, 2, 2, 2, 2, 2, 2, 2, 4, 4]
def baseStart_1002225 : Nat := 118140960795 + 1002225 * 2 ^ 59
def prefixEnd_1002225 : Nat := 4983230072969 + 3 ^ 40 * 1002225 * 2
def baseEnd_1002225 : Nat := 171541049650815507926119

theorem tailTrace_1002225 : CollatzResearch.WordTrace tailWord_1002225 prefixEnd_1002225 171541049650815507926119 := by
  unfold tailWord_1002225
  simp only [CollatzResearch.WordTrace]
  refine ⟨36554148794117466247856129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24369432529411644165237419 36554148794117466247856129)
  ·
    refine ⟨27415611595588099685892097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36554148794117466247856129 27415611595588099685892097)
    ·
      refine ⟨20561708696691074764419073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27415611595588099685892097 20561708696691074764419073)
      ·
        refine ⟨15421281522518306073314305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20561708696691074764419073 15421281522518306073314305)
        ·
          refine ⟨11565961141888729554985729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15421281522518306073314305 11565961141888729554985729)
          ·
            refine ⟨8674470856416547166239297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11565961141888729554985729 8674470856416547166239297)
            ·
              refine ⟨6505853142312410374679473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8674470856416547166239297 6505853142312410374679473)
              ·
                refine ⟨4879389856734307781009605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6505853142312410374679473 4879389856734307781009605)
                ·
                  refine ⟨914885598137682708939301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4879389856734307781009605 914885598137682708939301)
                  ·
                    refine ⟨171541049650815507926119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914885598137682708939301 171541049650815507926119)
                    ·
                      rfl

theorem cell23_1002225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 4, 4].length) (baseStart_1002225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002225 prefixEnd_1002225 := by exact prefixLift 1002225
  have htrace : WordTrace (prefixWord ++ tailWord_1002225) baseStart_1002225 baseEnd_1002225 := by
    simpa [prefixWord, tailWord_1002225, baseEnd_1002225] using wordTrace_append hprefix tailTrace_1002225
  have hstable : (prefixWord ++ tailWord_1002225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002225).length < 2 ^ (prefixWord ++ tailWord_1002225).sum := by decide
  have hdescent : baseEnd_1002225 < baseStart_1002225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002226 : List Nat := [3, 2, 1, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1002226 : Nat := 118140960795 + 1002226 * 2 ^ 59
def prefixEnd_1002226 : Nat := 4983230072969 + 3 ^ 40 * 1002226 * 2
def baseEnd_1002226 : Nat := 514623662433101019865853

theorem tailTrace_1002226 : CollatzResearch.WordTrace tailWord_1002226 prefixEnd_1002226 514623662433101019865853 := by
  unfold tailWord_1002226
  simp only [CollatzResearch.WordTrace]
  refine ⟨9138546316778460854660633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24369456844742562279095021 9138546316778460854660633)
  ·
    refine ⟨6853909737583845640995475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9138546316778460854660633 6853909737583845640995475)
    ·
      refine ⟨10280864606375768461493213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6853909737583845640995475 10280864606375768461493213)
      ·
        refine ⟨3855324227390913173059955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10280864606375768461493213 3855324227390913173059955)
        ·
          refine ⟨5782986341086369759589933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855324227390913173059955 5782986341086369759589933)
          ·
            refine ⟨2168619877907388659846225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5782986341086369759589933 2168619877907388659846225)
            ·
              refine ⟨1626464908430541494884669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168619877907388659846225 1626464908430541494884669)
              ·
                refine ⟨609924340661453060581751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1626464908430541494884669 609924340661453060581751)
                ·
                  refine ⟨914886510992179590872627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 609924340661453060581751 914886510992179590872627)
                  ·
                    refine ⟨1372329766488269386308941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914886510992179590872627 1372329766488269386308941)
                    ·
                      refine ⟨514623662433101019865853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372329766488269386308941 514623662433101019865853)
                      ·
                        rfl

theorem cell23_1002226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1002226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002226 prefixEnd_1002226 := by exact prefixLift 1002226
  have htrace : WordTrace (prefixWord ++ tailWord_1002226) baseStart_1002226 baseEnd_1002226 := by
    simpa [prefixWord, tailWord_1002226, baseEnd_1002226] using wordTrace_append hprefix tailTrace_1002226
  have hstable : (prefixWord ++ tailWord_1002226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002226).length < 2 ^ (prefixWord ++ tailWord_1002226).sum := by decide
  have hdescent : baseEnd_1002226 < baseStart_1002226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002232 : List Nat := [2, 1, 2, 1, 1, 2, 3, 2, 5, 2, 2]
def baseStart_1002232 : Nat := 118140960795 + 1002232 * 2 ^ 59
def prefixEnd_1002232 : Nat := 4983230072969 + 3 ^ 40 * 1002232 * 2
def baseEnd_1002232 : Nat := 514626743317027996390825

theorem tailTrace_1002232 : CollatzResearch.WordTrace tailWord_1002232 prefixEnd_1002232 514626743317027996390825 := by
  unfold tailWord_1002232
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277202052546053221680475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24369602736728070962240633 18277202052546053221680475)
  ·
    refine ⟨27415803078819079832520713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18277202052546053221680475 27415803078819079832520713)
    ·
      refine ⟨20561852309114309874390535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27415803078819079832520713 20561852309114309874390535)
      ·
        refine ⟨30842778463671464811585803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20561852309114309874390535 30842778463671464811585803)
        ·
          refine ⟨46264167695507197217378705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30842778463671464811585803 46264167695507197217378705)
          ·
            refine ⟨34698125771630397913034029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46264167695507197217378705 34698125771630397913034029)
            ·
              refine ⟨13011797164361399217387761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34698125771630397913034029 13011797164361399217387761)
              ·
                refine ⟨9758847873271049413040821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13011797164361399217387761 9758847873271049413040821)
                ·
                  refine ⟨914891988119160882472577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9758847873271049413040821 914891988119160882472577)
                  ·
                    refine ⟨686168991089370661854433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 914891988119160882472577 686168991089370661854433)
                    ·
                      refine ⟨514626743317027996390825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686168991089370661854433 514626743317027996390825)
                      ·
                        rfl

theorem cell23_1002232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_1002232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002232 prefixEnd_1002232 := by exact prefixLift 1002232
  have htrace : WordTrace (prefixWord ++ tailWord_1002232) baseStart_1002232 baseEnd_1002232 := by
    simpa [prefixWord, tailWord_1002232, baseEnd_1002232] using wordTrace_append hprefix tailTrace_1002232
  have hstable : (prefixWord ++ tailWord_1002232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002232).length < 2 ^ (prefixWord ++ tailWord_1002232).sum := by decide
  have hdescent : baseEnd_1002232 < baseStart_1002232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002265 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 3]
def baseStart_1002265 : Nat := 118140960795 + 1002265 * 2 ^ 59
def prefixEnd_1002265 : Nat := 4983230072969 + 3 ^ 40 * 1002265 * 2
def baseEnd_1002265 : Nat := 514643688178626367278173

theorem tailTrace_1002265 : CollatzResearch.WordTrace tailWord_1002265 prefixEnd_1002265 514643688178626367278173 := by
  unfold tailWord_1002265
  simp only [CollatzResearch.WordTrace]
  refine ⟨36555607713972553079312249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24370405142648368719541499 36555607713972553079312249)
  ·
    refine ⟨27416705785479414809484187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36555607713972553079312249 27416705785479414809484187)
    ·
      refine ⟨41125058678219122214226281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27416705785479414809484187 41125058678219122214226281)
      ·
        refine ⟨30843794008664341660669711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41125058678219122214226281 30843794008664341660669711)
        ·
          refine ⟨46265691012996512491004567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30843794008664341660669711 46265691012996512491004567)
          ·
            refine ⟨69398536519494768736506851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46265691012996512491004567 69398536519494768736506851)
            ·
              refine ⟨104097804779242153104760277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69398536519494768736506851 104097804779242153104760277)
              ·
                refine ⟨2439792299513487963392819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 104097804779242153104760277 2439792299513487963392819)
                ·
                  refine ⟨3659688449270231945089229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439792299513487963392819 3659688449270231945089229)
                  ·
                    refine ⟨1372383168476336979408461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3659688449270231945089229 1372383168476336979408461)
                    ·
                      refine ⟨514643688178626367278173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372383168476336979408461 514643688178626367278173)
                      ·
                        rfl

theorem cell23_1002265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_1002265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002265 prefixEnd_1002265 := by exact prefixLift 1002265
  have htrace : WordTrace (prefixWord ++ tailWord_1002265) baseStart_1002265 baseEnd_1002265 := by
    simpa [prefixWord, tailWord_1002265, baseEnd_1002265] using wordTrace_append hprefix tailTrace_1002265
  have hstable : (prefixWord ++ tailWord_1002265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002265).length < 2 ^ (prefixWord ++ tailWord_1002265).sum := by decide
  have hdescent : baseEnd_1002265 < baseStart_1002265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002272 : List Nat := [2, 1, 1, 5, 1, 4, 2, 7]
def baseStart_1002272 : Nat := 118140960795 + 1002272 * 2 ^ 59
def prefixEnd_1002272 : Nat := 4983230072969 + 3 ^ 40 * 1002272 * 2
def baseEnd_1002272 : Nat := 19061010464563253329283

theorem tailTrace_1002272 : CollatzResearch.WordTrace tailWord_1002272 prefixEnd_1002272 19061010464563253329283 := by
  unfold tailWord_1002272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18277931512473596637408535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24370575349964795516544713 18277931512473596637408535)
  ·
    refine ⟨27416897268710394956112803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18277931512473596637408535 27416897268710394956112803)
    ·
      refine ⟨41125345903065592434169205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27416897268710394956112803 41125345903065592434169205)
      ·
        refine ⟨3855501178412399290703363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41125345903065592434169205 3855501178412399290703363)
        ·
          refine ⟨5783251767618598936055045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3855501178412399290703363 5783251767618598936055045)
          ·
            refine ⟨1084359706428487300510321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5783251767618598936055045 1084359706428487300510321)
            ·
              refine ⟨813269779821365475382741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084359706428487300510321 813269779821365475382741)
              ·
                refine ⟨19061010464563253329283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 813269779821365475382741 19061010464563253329283)
                ·
                  rfl

theorem cell23_1002272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 7].length) (baseStart_1002272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002272 prefixEnd_1002272 := by exact prefixLift 1002272
  have htrace : WordTrace (prefixWord ++ tailWord_1002272) baseStart_1002272 baseEnd_1002272 := by
    simpa [prefixWord, tailWord_1002272, baseEnd_1002272] using wordTrace_append hprefix tailTrace_1002272
  have hstable : (prefixWord ++ tailWord_1002272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002272).length < 2 ^ (prefixWord ++ tailWord_1002272).sum := by decide
  have hdescent : baseEnd_1002272 < baseStart_1002272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002288 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8]
def baseStart_1002288 : Nat := 118140960795 + 1002288 * 2 ^ 59
def prefixEnd_1002288 : Nat := 4983230072969 + 3 ^ 40 * 1002288 * 2
def baseEnd_1002288 : Nat := 514655498233679777290567

theorem tailTrace_1002288 : CollatzResearch.WordTrace tailWord_1002288 prefixEnd_1002288 514655498233679777290567 := by
  unfold tailWord_1002288
  simp only [CollatzResearch.WordTrace]
  refine ⟨18278223296444614003699759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24370964395259485338266345 18278223296444614003699759)
  ·
    refine ⟨27417334944666921005549639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18278223296444614003699759 27417334944666921005549639)
    ·
      refine ⟨41126002417000381508324459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27417334944666921005549639 41126002417000381508324459)
      ·
        refine ⟨61689003625500572262486689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41126002417000381508324459 61689003625500572262486689)
        ·
          refine ⟨46266752719125429196865017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61689003625500572262486689 46266752719125429196865017)
          ·
            refine ⟨34700064539344071897648763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46266752719125429196865017 34700064539344071897648763)
            ·
              refine ⟨52050096809016107846473145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34700064539344071897648763 52050096809016107846473145)
              ·
                refine ⟨39037572606762080884854859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52050096809016107846473145 39037572606762080884854859)
                ·
                  refine ⟨58556358910143121327282289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39037572606762080884854859 58556358910143121327282289)
                  ·
                    refine ⟨43917269182607340995461717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58556358910143121327282289 43917269182607340995461717)
                    ·
                      refine ⟨514655498233679777290567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43917269182607340995461717 514655498233679777290567)
                      ·
                        rfl

theorem cell23_1002288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_1002288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002288 prefixEnd_1002288 := by exact prefixLift 1002288
  have htrace : WordTrace (prefixWord ++ tailWord_1002288) baseStart_1002288 baseEnd_1002288 := by
    simpa [prefixWord, tailWord_1002288, baseEnd_1002288] using wordTrace_append hprefix tailTrace_1002288
  have hstable : (prefixWord ++ tailWord_1002288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002288).length < 2 ^ (prefixWord ++ tailWord_1002288).sum := by decide
  have hdescent : baseEnd_1002288 < baseStart_1002288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002310 : List Nat := [6, 1, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1002310 : Nat := 118140960795 + 1002310 * 2 ^ 59
def prefixEnd_1002310 : Nat := 4983230072969 + 3 ^ 40 * 1002310 * 2
def baseEnd_1002310 : Nat := 171555598269359563738489

theorem tailTrace_1002310 : CollatzResearch.WordTrace tailWord_1002310 prefixEnd_1002310 171555598269359563738489 := by
  unfold tailWord_1002310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1142414031212797680146887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24371499332539683843133589 1142414031212797680146887)
  ·
    refine ⟨1713621046819196520220331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1142414031212797680146887 1713621046819196520220331)
    ·
      refine ⟨2570431570228794780330497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1713621046819196520220331 2570431570228794780330497)
      ·
        refine ⟨1927823677671596085247873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2570431570228794780330497 1927823677671596085247873)
        ·
          refine ⟨1445867758253697063935905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927823677671596085247873 1445867758253697063935905)
          ·
            refine ⟨1084400818690272797951929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1445867758253697063935905 1084400818690272797951929)
            ·
              refine ⟨813300614017704598463947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1084400818690272797951929 813300614017704598463947)
              ·
                refine ⟨1219950921026556897695921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813300614017704598463947 1219950921026556897695921)
                ·
                  refine ⟨914963190769917673271941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219950921026556897695921 914963190769917673271941)
                  ·
                    refine ⟨171555598269359563738489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 914963190769917673271941 171555598269359563738489)
                    ·
                      rfl

theorem cell23_1002310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1002310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002310 prefixEnd_1002310 := by exact prefixLift 1002310
  have htrace : WordTrace (prefixWord ++ tailWord_1002310) baseStart_1002310 baseEnd_1002310 := by
    simpa [prefixWord, tailWord_1002310, baseEnd_1002310] using wordTrace_append hprefix tailTrace_1002310
  have hstable : (prefixWord ++ tailWord_1002310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002310).length < 2 ^ (prefixWord ++ tailWord_1002310).sum := by decide
  have hdescent : baseEnd_1002310 < baseStart_1002310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002316 : List Nat := [2, 2, 1, 3, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1002316 : Nat := 118140960795 + 1002316 * 2 ^ 59
def prefixEnd_1002316 : Nat := 4983230072969 + 3 ^ 40 * 1002316 * 2
def baseEnd_1002316 : Nat := 514669875692005667740439

theorem tailTrace_1002316 : CollatzResearch.WordTrace tailWord_1002316 prefixEnd_1002316 514669875692005667740439 := by
  unfold tailWord_1002316
  simp only [CollatzResearch.WordTrace]
  refine ⟨18278733918393894394709401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24371645224525192526279201 18278733918393894394709401)
  ·
    refine ⟨13709050438795420796032051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18278733918393894394709401 13709050438795420796032051)
    ·
      refine ⟨20563575658193131194048077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13709050438795420796032051 20563575658193131194048077)
      ·
        refine ⟨7711340871822424197768029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20563575658193131194048077 7711340871822424197768029)
        ·
          refine ⟨2891752826933409074163011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7711340871822424197768029 2891752826933409074163011)
          ·
            refine ⟨4337629240400113611244517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2891752826933409074163011 4337629240400113611244517)
            ·
              refine ⟨813305482575021302108347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4337629240400113611244517 813305482575021302108347)
              ·
                refine ⟨1219958223862531953162521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813305482575021302108347 1219958223862531953162521)
                ·
                  refine ⟨914968667896898964871891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1219958223862531953162521 914968667896898964871891)
                  ·
                    refine ⟨1372453001845348447307837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 914968667896898964871891 1372453001845348447307837)
                    ·
                      refine ⟨514669875692005667740439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372453001845348447307837 514669875692005667740439)
                      ·
                        rfl

theorem cell23_1002316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1002316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002316 prefixEnd_1002316 := by exact prefixLift 1002316
  have htrace : WordTrace (prefixWord ++ tailWord_1002316) baseStart_1002316 baseEnd_1002316 := by
    simpa [prefixWord, tailWord_1002316, baseEnd_1002316] using wordTrace_append hprefix tailTrace_1002316
  have hstable : (prefixWord ++ tailWord_1002316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002316).length < 2 ^ (prefixWord ++ tailWord_1002316).sum := by decide
  have hdescent : baseEnd_1002316 < baseStart_1002316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002325 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_1002325 : Nat := 118140960795 + 1002325 * 2 ^ 59
def prefixEnd_1002325 : Nat := 4983230072969 + 3 ^ 40 * 1002325 * 2
def baseEnd_1002325 : Nat := 514674497017896132527897

theorem tailTrace_1002325 : CollatzResearch.WordTrace tailWord_1002325 prefixEnd_1002325 514674497017896132527897 := by
  unfold tailWord_1002325
  simp only [CollatzResearch.WordTrace]
  refine ⟨36557796093755183326496429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24371864062503455550997619 36557796093755183326496429)
  ·
    refine ⟨13709173535158193747436161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36557796093755183326496429 13709173535158193747436161)
    ·
      refine ⟨10281880151368645310577121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13709173535158193747436161 10281880151368645310577121)
      ·
        refine ⟨7711410113526483982932841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10281880151368645310577121 7711410113526483982932841)
        ·
          refine ⟨5783557585144862987199631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7711410113526483982932841 5783557585144862987199631)
          ·
            refine ⟨8675336377717294480799447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5783557585144862987199631 8675336377717294480799447)
            ·
              refine ⟨13013004566575941721199171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8675336377717294480799447 13013004566575941721199171)
              ·
                refine ⟨19519506849863912581798757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13013004566575941721199171 19519506849863912581798757)
                ·
                  refine ⟨3659907534349483609087267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19519506849863912581798757 3659907534349483609087267)
                  ·
                    refine ⟨5489861301524225413630901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3659907534349483609087267 5489861301524225413630901)
                    ·
                      refine ⟨514674497017896132527897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5489861301524225413630901 514674497017896132527897)
                      ·
                        rfl

theorem cell23_1002325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_1002325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002325 prefixEnd_1002325 := by exact prefixLift 1002325
  have htrace : WordTrace (prefixWord ++ tailWord_1002325) baseStart_1002325 baseEnd_1002325 := by
    simpa [prefixWord, tailWord_1002325, baseEnd_1002325] using wordTrace_append hprefix tailTrace_1002325
  have hstable : (prefixWord ++ tailWord_1002325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002325).length < 2 ^ (prefixWord ++ tailWord_1002325).sum := by decide
  have hdescent : baseEnd_1002325 < baseStart_1002325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002339 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 1, 4, 2]
def baseStart_1002339 : Nat := 118140960795 + 1002339 * 2 ^ 59
def prefixEnd_1002339 : Nat := 4983230072969 + 3 ^ 40 * 1002339 * 2
def baseEnd_1002339 : Nat := 514681685747059077752833

theorem tailTrace_1002339 : CollatzResearch.WordTrace tailWord_1002339 prefixEnd_1002339 514681685747059077752833 := by
  unfold tailWord_1002339
  simp only [CollatzResearch.WordTrace]
  refine ⟨36558306715704463717506071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24372204477136309145004047 36558306715704463717506071)
  ·
    refine ⟨54837460073556695576259107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36558306715704463717506071 54837460073556695576259107)
    ·
      refine ⟨82256190110335043364388661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54837460073556695576259107 82256190110335043364388661)
      ·
        refine ⟨7711517822843910315411437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82256190110335043364388661 7711517822843910315411437)
        ·
          refine ⟨2891819183566466368279289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7711517822843910315411437 2891819183566466368279289)
          ·
            refine ⟨2168864387674849776209467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2891819183566466368279289 2168864387674849776209467)
            ·
              refine ⟨3253296581512274664314201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2168864387674849776209467 3253296581512274664314201)
              ·
                refine ⟨2439972436134205998235651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253296581512274664314201 2439972436134205998235651)
                ·
                  refine ⟨3659958654201308997353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2439972436134205998235651 3659958654201308997353477)
                  ·
                    refine ⟨686242247662745437003777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3659958654201308997353477 686242247662745437003777)
                    ·
                      refine ⟨514681685747059077752833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686242247662745437003777 514681685747059077752833)
                      ·
                        rfl

theorem cell23_1002339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_1002339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002339 prefixEnd_1002339 := by exact prefixLift 1002339
  have htrace : WordTrace (prefixWord ++ tailWord_1002339) baseStart_1002339 baseEnd_1002339 := by
    simpa [prefixWord, tailWord_1002339, baseEnd_1002339] using wordTrace_append hprefix tailTrace_1002339
  have hstable : (prefixWord ++ tailWord_1002339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002339).length < 2 ^ (prefixWord ++ tailWord_1002339).sum := by decide
  have hdescent : baseEnd_1002339 < baseStart_1002339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002396 : List Nat := [2, 2, 3, 3, 2, 1, 2, 3, 5]
def baseStart_1002396 : Nat := 118140960795 + 1002396 * 2 ^ 59
def prefixEnd_1002396 : Nat := 4983230072969 + 3 ^ 40 * 1002396 * 2
def baseEnd_1002396 : Nat := 57190106016040594971119

theorem tailTrace_1002396 : CollatzResearch.WordTrace tailWord_1002396 prefixEnd_1002396 57190106016040594971119 := by
  unfold tailWord_1002396
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280192838248981226165521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24373590450998641634887361 18280192838248981226165521)
  ·
    refine ⟨13710144628686735919624141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18280192838248981226165521 13710144628686735919624141)
    ·
      refine ⟨5141304235757525969859053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13710144628686735919624141 5141304235757525969859053)
      ·
        refine ⟨1927989088409072238697145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5141304235757525969859053 1927989088409072238697145)
        ·
          refine ⟨1445991816306804179022859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1927989088409072238697145 1445991816306804179022859)
          ·
            refine ⟨2168987724460206268534289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1445991816306804179022859 2168987724460206268534289)
            ·
              refine ⟨1626740793345154701400717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2168987724460206268534289 1626740793345154701400717)
              ·
                refine ⟨610027797504433013025269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1626740793345154701400717 610027797504433013025269)
                ·
                  refine ⟨57190106016040594971119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610027797504433013025269 57190106016040594971119)
                  ·
                    rfl

theorem cell23_1002396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 3, 5].length) (baseStart_1002396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002396 prefixEnd_1002396 := by exact prefixLift 1002396
  have htrace : WordTrace (prefixWord ++ tailWord_1002396) baseStart_1002396 baseEnd_1002396 := by
    simpa [prefixWord, tailWord_1002396, baseEnd_1002396] using wordTrace_append hprefix tailTrace_1002396
  have hstable : (prefixWord ++ tailWord_1002396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002396).length < 2 ^ (prefixWord ++ tailWord_1002396).sum := by decide
  have hdescent : baseEnd_1002396 < baseStart_1002396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002412 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 3, 6, 2]
def baseStart_1002412 : Nat := 118140960795 + 1002412 * 2 ^ 59
def prefixEnd_1002412 : Nat := 4983230072969 + 3 ^ 40 * 1002412 * 2
def baseEnd_1002412 : Nat := 514719169834837292139997

theorem tailTrace_1002412 : CollatzResearch.WordTrace tailWord_1002412 prefixEnd_1002412 514719169834837292139997 := by
  unfold tailWord_1002412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280484622219998592456745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24373979496293331456608993 18280484622219998592456745)
  ·
    refine ⟨13710363466664998944342559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18280484622219998592456745 13710363466664998944342559)
    ·
      refine ⟨20565545199997498416513839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13710363466664998944342559 20565545199997498416513839)
      ·
        refine ⟨30848317799996247624770759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20565545199997498416513839 30848317799996247624770759)
        ·
          refine ⟨46272476699994371437156139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30848317799996247624770759 46272476699994371437156139)
          ·
            refine ⟨69408715049991557155734209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46272476699994371437156139 69408715049991557155734209)
            ·
              refine ⟨52056536287493667866800657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69408715049991557155734209 52056536287493667866800657)
              ·
                refine ⟨39042402215620250900100493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52056536287493667866800657 39042402215620250900100493)
                ·
                  refine ⟨14640900830857594087537685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39042402215620250900100493 14640900830857594087537685)
                  ·
                    refine ⟨686292226446449722853329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14640900830857594087537685 686292226446449722853329)
                    ·
                      refine ⟨514719169834837292139997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686292226446449722853329 514719169834837292139997)
                      ·
                        rfl

theorem cell23_1002412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 6, 2].length) (baseStart_1002412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002412 prefixEnd_1002412 := by exact prefixLift 1002412
  have htrace : WordTrace (prefixWord ++ tailWord_1002412) baseStart_1002412 baseEnd_1002412 := by
    simpa [prefixWord, tailWord_1002412, baseEnd_1002412] using wordTrace_append hprefix tailTrace_1002412
  have hstable : (prefixWord ++ tailWord_1002412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002412).length < 2 ^ (prefixWord ++ tailWord_1002412).sum := by decide
  have hdescent : baseEnd_1002412 < baseStart_1002412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002432 : List Nat := [2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3]
def baseStart_1002432 : Nat := 118140960795 + 1002432 * 2 ^ 59
def prefixEnd_1002432 : Nat := 4983230072969 + 3 ^ 40 * 1002432 * 2
def baseEnd_1002432 : Nat := 514729439447927213889905

theorem tailTrace_1002432 : CollatzResearch.WordTrace tailWord_1002432 prefixEnd_1002432 514729439447927213889905 := by
  unfold tailWord_1002432
  simp only [CollatzResearch.WordTrace]
  refine ⟨18280849352183770300320775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24374465802911693733761033 18280849352183770300320775)
  ·
    refine ⟨27421274028275655450481163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18280849352183770300320775 27421274028275655450481163)
    ·
      refine ⟨41131911042413483175721745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27421274028275655450481163 41131911042413483175721745)
      ·
        refine ⟨30848933281810112381791309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41131911042413483175721745 30848933281810112381791309)
        ·
          refine ⟨11568349980678792143171741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30848933281810112381791309 11568349980678792143171741)
          ·
            refine ⟨4338131242754547053689403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11568349980678792143171741 4338131242754547053689403)
            ·
              refine ⟨6507196864131820580534105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338131242754547053689403 6507196864131820580534105)
              ·
                refine ⟨4880397648098865435400579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507196864131820580534105 4880397648098865435400579)
                ·
                  refine ⟨7320596472148298153100869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4880397648098865435400579 7320596472148298153100869)
                  ·
                    refine ⟨1372611838527805903706413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7320596472148298153100869 1372611838527805903706413)
                    ·
                      refine ⟨514729439447927213889905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372611838527805903706413 514729439447927213889905)
                      ·
                        rfl

theorem cell23_1002432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 3].length) (baseStart_1002432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002432 prefixEnd_1002432 := by exact prefixLift 1002432
  have htrace : WordTrace (prefixWord ++ tailWord_1002432) baseStart_1002432 baseEnd_1002432 := by
    simpa [prefixWord, tailWord_1002432, baseEnd_1002432] using wordTrace_append hprefix tailTrace_1002432
  have hstable : (prefixWord ++ tailWord_1002432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002432).length < 2 ^ (prefixWord ++ tailWord_1002432).sum := by decide
  have hdescent : baseEnd_1002432 < baseStart_1002432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002452 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1002452 : Nat := 118140960795 + 1002452 * 2 ^ 59
def prefixEnd_1002452 : Nat := 4983230072969 + 3 ^ 40 * 1002452 * 2
def baseEnd_1002452 : Nat := 57193301006779681737757

theorem tailTrace_1002452 : CollatzResearch.WordTrace tailWord_1002452 prefixEnd_1002452 57193301006779681737757 := by
  unfold tailWord_1002452
  simp only [CollatzResearch.WordTrace]
  refine ⟨18281214082147542008184805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24374952109530056010913073 18281214082147542008184805)
  ·
    refine ⟨3427727640402664126534651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18281214082147542008184805 3427727640402664126534651)
    ·
      refine ⟨5141591460603996189801977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427727640402664126534651 5141591460603996189801977)
      ·
        refine ⟨3856193595452997142351483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5141591460603996189801977 3856193595452997142351483)
        ·
          refine ⟨5784290393179495713527225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856193595452997142351483 5784290393179495713527225)
          ·
            refine ⟨4338217794884621785145419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5784290393179495713527225 4338217794884621785145419)
            ·
              refine ⟨6507326692326932677718129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338217794884621785145419 6507326692326932677718129)
              ·
                refine ⟨4880495019245199508288597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6507326692326932677718129 4880495019245199508288597)
                ·
                  refine ⟨57193301006779681737757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4880495019245199508288597 57193301006779681737757)
                  ·
                    rfl

theorem cell23_1002452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1002452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002452 prefixEnd_1002452 := by exact prefixLift 1002452
  have htrace : WordTrace (prefixWord ++ tailWord_1002452) baseStart_1002452 baseEnd_1002452 := by
    simpa [prefixWord, tailWord_1002452, baseEnd_1002452] using wordTrace_append hprefix tailTrace_1002452
  have hstable : (prefixWord ++ tailWord_1002452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002452).length < 2 ^ (prefixWord ++ tailWord_1002452).sum := by decide
  have hdescent : baseEnd_1002452 < baseStart_1002452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002455 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1002455 : Nat := 118140960795 + 1002455 * 2 ^ 59
def prefixEnd_1002455 : Nat := 4983230072969 + 3 ^ 40 * 1002455 * 2
def baseEnd_1002455 : Nat := 514741249502980623902299

theorem tailTrace_1002455 : CollatzResearch.WordTrace tailWord_1002455 prefixEnd_1002455 514741249502980623902299 := by
  unfold tailWord_1002455
  simp only [CollatzResearch.WordTrace]
  refine ⟨36562537583284215528728819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24375025055522810352485879 36562537583284215528728819)
  ·
    refine ⟨54843806374926323293093229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36562537583284215528728819 54843806374926323293093229)
    ·
      refine ⟨20566427390597371234909961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54843806374926323293093229 20566427390597371234909961)
      ·
        refine ⟨15424820542948028426182471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20566427390597371234909961 15424820542948028426182471)
        ·
          refine ⟨23137230814422042639273707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15424820542948028426182471 23137230814422042639273707)
          ·
            refine ⟨34705846221633063958910561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23137230814422042639273707 34705846221633063958910561)
            ·
              refine ⟨26029384666224797969182921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34705846221633063958910561 26029384666224797969182921)
              ·
                refine ⟨19522038499668598476887191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26029384666224797969182921 19522038499668598476887191)
                ·
                  refine ⟨29283057749502897715330787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19522038499668598476887191 29283057749502897715330787)
                  ·
                    refine ⟨43924586624254346572996181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29283057749502897715330787 43924586624254346572996181)
                    ·
                      refine ⟨514741249502980623902299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 43924586624254346572996181 514741249502980623902299)
                      ·
                        rfl

theorem cell23_1002455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1002455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002455 prefixEnd_1002455 := by exact prefixLift 1002455
  have htrace : WordTrace (prefixWord ++ tailWord_1002455) baseStart_1002455 baseEnd_1002455 := by
    simpa [prefixWord, tailWord_1002455, baseEnd_1002455] using wordTrace_append hprefix tailTrace_1002455
  have hstable : (prefixWord ++ tailWord_1002455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002455).length < 2 ^ (prefixWord ++ tailWord_1002455).sum := by decide
  have hdescent : baseEnd_1002455 < baseStart_1002455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002456 : List Nat := [2, 1, 2, 2, 2, 3, 3, 3, 1, 4]
def baseStart_1002456 : Nat := 118140960795 + 1002456 * 2 ^ 59
def prefixEnd_1002456 : Nat := 4983230072969 + 3 ^ 40 * 1002456 * 2
def baseEnd_1002456 : Nat := 171580587661211706663265

theorem tailTrace_1002456 : CollatzResearch.WordTrace tailWord_1002456 prefixEnd_1002456 171580587661211706663265 := by
  unfold tailWord_1002456
  simp only [CollatzResearch.WordTrace]
  refine ⟨18281287028140296349757611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24375049370853728466343481 18281287028140296349757611)
  ·
    refine ⟨27421930542210444524636417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18281287028140296349757611 27421930542210444524636417)
    ·
      refine ⟨20566447906657833393477313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27421930542210444524636417 20566447906657833393477313)
      ·
        refine ⟨15424835929993375045107985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20566447906657833393477313 15424835929993375045107985)
        ·
          refine ⟨11568626947495031283830989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15424835929993375045107985 11568626947495031283830989)
          ·
            refine ⟨4338235105310636731436621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11568626947495031283830989 4338235105310636731436621)
            ·
              refine ⟨1626838164491488774288733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4338235105310636731436621 1626838164491488774288733)
              ·
                refine ⟨610064311684308290358275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1626838164491488774288733 610064311684308290358275)
                ·
                  refine ⟨915096467526462435537413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610064311684308290358275 915096467526462435537413)
                  ·
                    refine ⟨171580587661211706663265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 915096467526462435537413 171580587661211706663265)
                    ·
                      rfl

theorem cell23_1002456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 3, 3, 1, 4].length) (baseStart_1002456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002456 prefixEnd_1002456 := by exact prefixLift 1002456
  have htrace : WordTrace (prefixWord ++ tailWord_1002456) baseStart_1002456 baseEnd_1002456 := by
    simpa [prefixWord, tailWord_1002456, baseEnd_1002456] using wordTrace_append hprefix tailTrace_1002456
  have hstable : (prefixWord ++ tailWord_1002456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002456).length < 2 ^ (prefixWord ++ tailWord_1002456).sum := by decide
  have hdescent : baseEnd_1002456 < baseStart_1002456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002466 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1002466 : Nat := 118140960795 + 1002466 * 2 ^ 59
def prefixEnd_1002466 : Nat := 4983230072969 + 3 ^ 40 * 1002466 * 2
def baseEnd_1002466 : Nat := 514746897790180080864749

theorem tailTrace_1002466 : CollatzResearch.WordTrace tailWord_1002466 prefixEnd_1002466 514746897790180080864749 := by
  unfold tailWord_1002466
  simp only [CollatzResearch.WordTrace]
  refine ⟨9140734696561091101844813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24375292524162909604919501 9140734696561091101844813)
  ·
    refine ⟨3427775511210409163191805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9140734696561091101844813 3427775511210409163191805)
    ·
      refine ⟨1285415816703903436196927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3427775511210409163191805 1285415816703903436196927)
      ·
        refine ⟨1928123725055855154295391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285415816703903436196927 1928123725055855154295391)
        ·
          refine ⟨2892185587583782731443087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928123725055855154295391 2892185587583782731443087)
          ·
            refine ⟨4338278381375674097164631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892185587583782731443087 4338278381375674097164631)
            ·
              refine ⟨6507417572063511145746947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338278381375674097164631 6507417572063511145746947)
              ·
                refine ⟨9761126358095266718620421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6507417572063511145746947 9761126358095266718620421)
                ·
                  refine ⟨1830211192142862509741329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9761126358095266718620421 1830211192142862509741329)
                  ·
                    refine ⟨1372658394107146882305997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1830211192142862509741329 1372658394107146882305997)
                    ·
                      refine ⟨514746897790180080864749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372658394107146882305997 514746897790180080864749)
                      ·
                        rfl

theorem cell23_1002466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1002466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002466 prefixEnd_1002466 := by exact prefixLift 1002466
  have htrace : WordTrace (prefixWord ++ tailWord_1002466) baseStart_1002466 baseEnd_1002466 := by
    simpa [prefixWord, tailWord_1002466, baseEnd_1002466] using wordTrace_append hprefix tailTrace_1002466
  have hstable : (prefixWord ++ tailWord_1002466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002466).length < 2 ^ (prefixWord ++ tailWord_1002466).sum := by decide
  have hdescent : baseEnd_1002466 < baseStart_1002466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002475 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7]
def baseStart_1002475 : Nat := 118140960795 + 1002475 * 2 ^ 59
def prefixEnd_1002475 : Nat := 4983230072969 + 3 ^ 40 * 1002475 * 2
def baseEnd_1002475 : Nat := 514751519116070545652207

theorem tailTrace_1002475 : CollatzResearch.WordTrace tailWord_1002475 prefixEnd_1002475 514751519116070545652207 := by
  unfold tailWord_1002475
  simp only [CollatzResearch.WordTrace]
  refine ⟨36563267043211758944456879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24375511362141172629637919 36563267043211758944456879)
  ·
    refine ⟨54844900564817638416685319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36563267043211758944456879 54844900564817638416685319)
    ·
      refine ⟨82267350847226457625027979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54844900564817638416685319 82267350847226457625027979)
      ·
        refine ⟨123401026270839686437541969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82267350847226457625027979 123401026270839686437541969)
        ·
          refine ⟨92550769703129764828156477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123401026270839686437541969 92550769703129764828156477)
          ·
            refine ⟨34706538638673661810558679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92550769703129764828156477 34706538638673661810558679)
            ·
              refine ⟨52059807958010492715838019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34706538638673661810558679 52059807958010492715838019)
              ·
                refine ⟨78089711937015739073757029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52059807958010492715838019 78089711937015739073757029)
                ·
                  refine ⟨14641820988190451076329443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78089711937015739073757029 14641820988190451076329443)
                  ·
                    refine ⟨21962731482285676614494165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14641820988190451076329443 21962731482285676614494165)
                    ·
                      refine ⟨514751519116070545652207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21962731482285676614494165 514751519116070545652207)
                      ·
                        rfl

theorem cell23_1002475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_1002475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002475 prefixEnd_1002475 := by exact prefixLift 1002475
  have htrace : WordTrace (prefixWord ++ tailWord_1002475) baseStart_1002475 baseEnd_1002475 := by
    simpa [prefixWord, tailWord_1002475, baseEnd_1002475] using wordTrace_append hprefix tailTrace_1002475
  have hstable : (prefixWord ++ tailWord_1002475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002475).length < 2 ^ (prefixWord ++ tailWord_1002475).sum := by decide
  have hdescent : baseEnd_1002475 < baseStart_1002475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002486 : List Nat := [5, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1002486 : Nat := 118140960795 + 1002486 * 2 ^ 59
def prefixEnd_1002486 : Nat := 4983230072969 + 3 ^ 40 * 1002486 * 2
def baseEnd_1002486 : Nat := 57195240822585555846073

theorem tailTrace_1002486 : CollatzResearch.WordTrace tailWord_1002486 prefixEnd_1002486 57195240822585555846073 := by
  unfold tailWord_1002486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285229265385744238944207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24375778830781271882071541 2285229265385744238944207)
  ·
    refine ⟨3427843898078616358416311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2285229265385744238944207 3427843898078616358416311)
    ·
      refine ⟨5141765847117924537624467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427843898078616358416311 5141765847117924537624467)
      ·
        refine ⟨7712648770676886806436701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141765847117924537624467 7712648770676886806436701)
        ·
          refine ⟨2892243289003832552413763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7712648770676886806436701 2892243289003832552413763)
          ·
            refine ⟨4338364933505748828620645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892243289003832552413763 4338364933505748828620645)
            ·
              refine ⟨813443425032327905366371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4338364933505748828620645 813443425032327905366371)
              ·
                refine ⟨1220165137548491858049557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 813443425032327905366371 1220165137548491858049557)
                ·
                  refine ⟨57195240822585555846073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1220165137548491858049557 57195240822585555846073)
                  ·
                    rfl

theorem cell23_1002486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1002486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002486 prefixEnd_1002486 := by exact prefixLift 1002486
  have htrace : WordTrace (prefixWord ++ tailWord_1002486) baseStart_1002486 baseEnd_1002486 := by
    simpa [prefixWord, tailWord_1002486, baseEnd_1002486] using wordTrace_append hprefix tailTrace_1002486
  have hstable : (prefixWord ++ tailWord_1002486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002486).length < 2 ^ (prefixWord ++ tailWord_1002486).sum := by decide
  have hdescent : baseEnd_1002486 < baseStart_1002486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002489 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 4, 3, 2]
def baseStart_1002489 : Nat := 118140960795 + 1002489 * 2 ^ 59
def prefixEnd_1002489 : Nat := 4983230072969 + 3 ^ 40 * 1002489 * 2
def baseEnd_1002489 : Nat := 514758707845233490877143

theorem tailTrace_1002489 : CollatzResearch.WordTrace tailWord_1002489 prefixEnd_1002489 514758707845233490877143 := by
  unfold tailWord_1002489
  simp only [CollatzResearch.WordTrace]
  refine ⟨36563777665161039335466521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24375851776774026223644347 36563777665161039335466521)
  ·
    refine ⟨27422833248870779501599891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36563777665161039335466521 27422833248870779501599891)
    ·
      refine ⟨41134249873306169252399837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27422833248870779501599891 41134249873306169252399837)
      ·
        refine ⟨15425343702489813469649939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41134249873306169252399837 15425343702489813469649939)
        ·
          refine ⟨23138015553734720204474909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15425343702489813469649939 23138015553734720204474909)
          ·
            refine ⟨8676755832650520076678091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23138015553734720204474909 8676755832650520076678091)
            ·
              refine ⟨13015133748975780115017137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8676755832650520076678091 13015133748975780115017137)
              ·
                refine ⟨9761350311731835086262853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13015133748975780115017137 9761350311731835086262853)
                ·
                  refine ⟨1830253183449719078674285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9761350311731835086262853 1830253183449719078674285)
                  ·
                    refine ⟨686344943793644654502857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830253183449719078674285 686344943793644654502857)
                    ·
                      refine ⟨514758707845233490877143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686344943793644654502857 514758707845233490877143)
                      ·
                        rfl

theorem cell23_1002489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_1002489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002489 prefixEnd_1002489 := by exact prefixLift 1002489
  have htrace : WordTrace (prefixWord ++ tailWord_1002489) baseStart_1002489 baseEnd_1002489 := by
    simpa [prefixWord, tailWord_1002489, baseEnd_1002489] using wordTrace_append hprefix tailTrace_1002489
  have hstable : (prefixWord ++ tailWord_1002489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002489).length < 2 ^ (prefixWord ++ tailWord_1002489).sum := by decide
  have hdescent : baseEnd_1002489 < baseStart_1002489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002506 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2]
def baseStart_1002506 : Nat := 118140960795 + 1002506 * 2 ^ 59
def prefixEnd_1002506 : Nat := 4983230072969 + 3 ^ 40 * 1002506 * 2
def baseEnd_1002506 : Nat := 514767437016359924364565

theorem tailTrace_1002506 : CollatzResearch.WordTrace tailWord_1002506 prefixEnd_1002506 514767437016359924364565 := by
  unfold tailWord_1002506
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141099426524862809708843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24376265137399634159223581 9141099426524862809708843)
  ·
    refine ⟨13711649139787294214563265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141099426524862809708843 13711649139787294214563265)
    ·
      refine ⟨10283736854840470660922449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13711649139787294214563265 10283736854840470660922449)
      ·
        refine ⟨7712802641130352995691837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10283736854840470660922449 7712802641130352995691837)
        ·
          refine ⟨2892300990423882373384439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7712802641130352995691837 2892300990423882373384439)
          ·
            refine ⟨4338451485635823560076659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892300990423882373384439 4338451485635823560076659)
            ·
              refine ⟨6507677228453735340114989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4338451485635823560076659 6507677228453735340114989)
              ·
                refine ⟨2440378960670150752543121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6507677228453735340114989 2440378960670150752543121)
                ·
                  refine ⟨1830284220502613064407341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2440378960670150752543121 1830284220502613064407341)
                  ·
                    refine ⟨686356582688479899152753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1830284220502613064407341 686356582688479899152753)
                    ·
                      refine ⟨514767437016359924364565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686356582688479899152753 514767437016359924364565)
                      ·
                        rfl

theorem cell23_1002506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_1002506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002506 prefixEnd_1002506 := by exact prefixLift 1002506
  have htrace : WordTrace (prefixWord ++ tailWord_1002506) baseStart_1002506 baseEnd_1002506 := by
    simpa [prefixWord, tailWord_1002506, baseEnd_1002506] using wordTrace_append hprefix tailTrace_1002506
  have hstable : (prefixWord ++ tailWord_1002506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002506).length < 2 ^ (prefixWord ++ tailWord_1002506).sum := by decide
  have hdescent : baseEnd_1002506 < baseStart_1002506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002530 : List Nat := [3, 3, 1, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_1002530 : Nat := 118140960795 + 1002530 * 2 ^ 59
def prefixEnd_1002530 : Nat := 4983230072969 + 3 ^ 40 * 1002530 * 2
def baseEnd_1002530 : Nat := 514779760552067830464455

theorem tailTrace_1002530 : CollatzResearch.WordTrace tailWord_1002530 prefixEnd_1002530 514779760552067830464455 := by
  unfold tailWord_1002530
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141318264503125834427261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24376848705341668891806029 9141318264503125834427261)
  ·
    refine ⟨3427994349188672187910223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9141318264503125834427261 3427994349188672187910223)
    ·
      refine ⟨5141991523783008281865335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3427994349188672187910223 5141991523783008281865335)
      ·
        refine ⟨7712987285674512422798003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5141991523783008281865335 7712987285674512422798003)
        ·
          refine ⟨11569480928511768634197005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7712987285674512422798003 11569480928511768634197005)
          ·
            refine ⟨4338555348191913237823877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11569480928511768634197005 4338555348191913237823877)
            ·
              refine ⟨813479127785983732091977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4338555348191913237823877 813479127785983732091977)
              ·
                refine ⟨610109345839487799068983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813479127785983732091977 610109345839487799068983)
                ·
                  refine ⟨915164018759231698603475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610109345839487799068983 915164018759231698603475)
                  ·
                    refine ⟨1372746028138847547905213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915164018759231698603475 1372746028138847547905213)
                    ·
                      refine ⟨514779760552067830464455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372746028138847547905213 514779760552067830464455)
                      ·
                        rfl

theorem cell23_1002530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_1002530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002530 prefixEnd_1002530 := by exact prefixLift 1002530
  have htrace : WordTrace (prefixWord ++ tailWord_1002530) baseStart_1002530 baseEnd_1002530 := by
    simpa [prefixWord, tailWord_1002530, baseEnd_1002530] using wordTrace_append hprefix tailTrace_1002530
  have hstable : (prefixWord ++ tailWord_1002530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002530).length < 2 ^ (prefixWord ++ tailWord_1002530).sum := by decide
  have hdescent : baseEnd_1002530 < baseStart_1002530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002553 : List Nat := [1, 2, 1, 5, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1002553 : Nat := 118140960795 + 1002553 * 2 ^ 59
def prefixEnd_1002553 : Nat := 4983230072969 + 3 ^ 40 * 1002553 * 2
def baseEnd_1002553 : Nat := 514791570607121240476849

theorem tailTrace_1002553 : CollatzResearch.WordTrace tailWord_1002553 prefixEnd_1002553 514791570607121240476849 := by
  unfold tailWord_1002553
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566111936929178265796313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24377407957952785510530875 36566111936929178265796313)
  ·
    refine ⟨27424583952696883699347235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36566111936929178265796313 27424583952696883699347235)
    ·
      refine ⟨41136875929045325549020853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27424583952696883699347235 41136875929045325549020853)
      ·
        refine ⟨3856582118347999270220705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41136875929045325549020853 3856582118347999270220705)
        ·
          refine ⟨2892436588760999452665529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3856582118347999270220705 2892436588760999452665529)
          ·
            refine ⟨2169327441570749589499147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2892436588760999452665529 2169327441570749589499147)
            ·
              refine ⟨3253991162356124384248721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169327441570749589499147 3253991162356124384248721)
              ·
                refine ⟨2440493371767093288186541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3253991162356124384248721 2440493371767093288186541)
                ·
                  refine ⟨915185014412659983069953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2440493371767093288186541 915185014412659983069953)
                  ·
                    refine ⟨686388760809494987302465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 915185014412659983069953 686388760809494987302465)
                    ·
                      refine ⟨514791570607121240476849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686388760809494987302465 514791570607121240476849)
                      ·
                        rfl

theorem cell23_1002553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1002553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002553 prefixEnd_1002553 := by exact prefixLift 1002553
  have htrace : WordTrace (prefixWord ++ tailWord_1002553) baseStart_1002553 baseEnd_1002553 := by
    simpa [prefixWord, tailWord_1002553, baseEnd_1002553] using wordTrace_append hprefix tailTrace_1002553
  have hstable : (prefixWord ++ tailWord_1002553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002553).length < 2 ^ (prefixWord ++ tailWord_1002553).sum := by decide
  have hdescent : baseEnd_1002553 < baseStart_1002553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002573 : List Nat := [1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1002573 : Nat := 118140960795 + 1002573 * 2 ^ 59
def prefixEnd_1002573 : Nat := 4983230072969 + 3 ^ 40 * 1002573 * 2
def baseEnd_1002573 : Nat := 514801840220211162226757

theorem tailTrace_1002573 : CollatzResearch.WordTrace tailWord_1002573 prefixEnd_1002573 514801840220211162226757 := by
  unfold tailWord_1002573
  simp only [CollatzResearch.WordTrace]
  refine ⟨36566841396856721681524373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24377894264571147787682915 36566841396856721681524373)
  ·
    refine ⟨1714070690477658828821455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 36566841396856721681524373 1714070690477658828821455)
    ·
      refine ⟨2571106035716488243232183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714070690477658828821455 2571106035716488243232183)
      ·
        refine ⟨3856659053574732364848275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2571106035716488243232183 3856659053574732364848275)
        ·
          refine ⟨5784988580362098547272413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3856659053574732364848275 5784988580362098547272413)
          ·
            refine ⟨2169370717635786955227155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5784988580362098547272413 2169370717635786955227155)
            ·
              refine ⟨3254056076453680432840733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169370717635786955227155 3254056076453680432840733)
              ·
                refine ⟨1220271028670130162315275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254056076453680432840733 1220271028670130162315275)
                ·
                  refine ⟨1830406543005195243472913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1220271028670130162315275 1830406543005195243472913)
                  ·
                    refine ⟨1372804907253896432604685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1830406543005195243472913 1372804907253896432604685)
                    ·
                      refine ⟨514801840220211162226757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372804907253896432604685 514801840220211162226757)
                      ·
                        rfl

theorem cell23_1002573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1002573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002573 prefixEnd_1002573 := by exact prefixLift 1002573
  have htrace : WordTrace (prefixWord ++ tailWord_1002573) baseStart_1002573 baseEnd_1002573 := by
    simpa [prefixWord, tailWord_1002573, baseEnd_1002573] using wordTrace_append hprefix tailTrace_1002573
  have hstable : (prefixWord ++ tailWord_1002573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002573).length < 2 ^ (prefixWord ++ tailWord_1002573).sum := by decide
  have hdescent : baseEnd_1002573 < baseStart_1002573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002586 : List Nat := [3, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3]
def baseStart_1002586 : Nat := 118140960795 + 1002586 * 2 ^ 59
def prefixEnd_1002586 : Nat := 4983230072969 + 3 ^ 40 * 1002586 * 2
def baseEnd_1002586 : Nat := 514808515468719611364197

theorem tailTrace_1002586 : CollatzResearch.WordTrace tailWord_1002586 prefixEnd_1002586 514808515468719611364197 := by
  unfold tailWord_1002586
  simp only [CollatzResearch.WordTrace]
  refine ⟨9141828886452406225436903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24378210363873083267831741 9141828886452406225436903)
  ·
    refine ⟨13712743329678609338155355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9141828886452406225436903 13712743329678609338155355)
    ·
      refine ⟨20569114994517914007233033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13712743329678609338155355 20569114994517914007233033)
      ·
        refine ⟨15426836245888435505424775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20569114994517914007233033 15426836245888435505424775)
        ·
          refine ⟨23140254368832653258137163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15426836245888435505424775 23140254368832653258137163)
          ·
            refine ⟨34710381553248979887205745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23140254368832653258137163 34710381553248979887205745)
            ·
              refine ⟨26032786164936734915404309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34710381553248979887205745 26032786164936734915404309)
              ·
                refine ⟨1220286851481409449159577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26032786164936734915404309 1220286851481409449159577)
                ·
                  refine ⟨915215138611057086869683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1220286851481409449159577 915215138611057086869683)
                  ·
                    refine ⟨1372822707916585630304525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915215138611057086869683 1372822707916585630304525)
                    ·
                      refine ⟨514808515468719611364197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372822707916585630304525 514808515468719611364197)
                      ·
                        rfl

theorem cell23_1002586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_1002586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002586 prefixEnd_1002586 := by exact prefixLift 1002586
  have htrace : WordTrace (prefixWord ++ tailWord_1002586) baseStart_1002586 baseEnd_1002586 := by
    simpa [prefixWord, tailWord_1002586, baseEnd_1002586] using wordTrace_append hprefix tailTrace_1002586
  have hstable : (prefixWord ++ tailWord_1002586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002586).length < 2 ^ (prefixWord ++ tailWord_1002586).sum := by decide
  have hdescent : baseEnd_1002586 < baseStart_1002586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002600 : List Nat := [2, 1, 4, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1002600 : Nat := 118140960795 + 1002600 * 2 ^ 59
def prefixEnd_1002600 : Nat := 4983230072969 + 3 ^ 40 * 1002600 * 2
def baseEnd_1002600 : Nat := 514815704197882556589133

theorem tailTrace_1002600 : CollatzResearch.WordTrace tailWord_1002600 prefixEnd_1002600 514815704197882556589133 := by
  unfold tailWord_1002600
  simp only [CollatzResearch.WordTrace]
  refine ⟨18283913083879452646378627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24378550778505936861838169 18283913083879452646378627)
  ·
    refine ⟨27425869625819178969567941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18283913083879452646378627 27425869625819178969567941)
    ·
      refine ⟨5142350554841096056793989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27425869625819178969567941 5142350554841096056793989)
      ·
        refine ⟨964190729032705510648873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5142350554841096056793989 964190729032705510648873)
        ·
          refine ⟨723143046774529132986655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964190729032705510648873 723143046774529132986655)
          ·
            refine ⟨1084714570161793699479983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723143046774529132986655 1084714570161793699479983)
            ·
              refine ⟨1627071855242690549219975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084714570161793699479983 1627071855242690549219975)
              ·
                refine ⟨2440607782864035823829963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627071855242690549219975 2440607782864035823829963)
                ·
                  refine ⟨3660911674296053735744945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2440607782864035823829963 3660911674296053735744945)
                  ·
                    refine ⟨2745683755722040301808709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3660911674296053735744945 2745683755722040301808709)
                    ·
                      refine ⟨514815704197882556589133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2745683755722040301808709 514815704197882556589133)
                      ·
                        rfl

theorem cell23_1002600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1002600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002600 prefixEnd_1002600 := by exact prefixLift 1002600
  have htrace : WordTrace (prefixWord ++ tailWord_1002600) baseStart_1002600 baseEnd_1002600 := by
    simpa [prefixWord, tailWord_1002600, baseEnd_1002600] using wordTrace_append hprefix tailTrace_1002600
  have hstable : (prefixWord ++ tailWord_1002600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002600).length < 2 ^ (prefixWord ++ tailWord_1002600).sum := by decide
  have hdescent : baseEnd_1002600 < baseStart_1002600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002659 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 3]
def baseStart_1002659 : Nat := 118140960795 + 1002659 * 2 ^ 59
def prefixEnd_1002659 : Nat := 4983230072969 + 3 ^ 40 * 1002659 * 2
def baseEnd_1002659 : Nat := 514845999556497825751361

theorem tailTrace_1002659 : CollatzResearch.WordTrace tailWord_1002659 prefixEnd_1002659 514845999556497825751361 := by
  unfold tailWord_1002659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36569978074545158369155031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24379985383030105579436687 36569978074545158369155031)
  ·
    refine ⟨54854967111817737553732547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36569978074545158369155031 54854967111817737553732547)
    ·
      refine ⟨82282450667726606330598821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54854967111817737553732547 82282450667726606330598821)
      ·
        refine ⟨15427959500198738686987279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82282450667726606330598821 15427959500198738686987279)
        ·
          refine ⟨23141939250298108030480919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15427959500198738686987279 23141939250298108030480919)
          ·
            refine ⟨34712908875447162045721379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23141939250298108030480919 34712908875447162045721379)
            ·
              refine ⟨52069363313170743068582069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34712908875447162045721379 52069363313170743068582069)
              ·
                refine ⟨4881502810609757162679569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52069363313170743068582069 4881502810609757162679569)
                ·
                  refine ⟨3661127107957317872009677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4881502810609757162679569 3661127107957317872009677)
                  ·
                    refine ⟨1372922665483994202003629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3661127107957317872009677 1372922665483994202003629)
                    ·
                      refine ⟨514845999556497825751361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372922665483994202003629 514845999556497825751361)
                      ·
                        rfl

theorem cell23_1002659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_1002659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002659 prefixEnd_1002659 := by exact prefixLift 1002659
  have htrace : WordTrace (prefixWord ++ tailWord_1002659) baseStart_1002659 baseEnd_1002659 := by
    simpa [prefixWord, tailWord_1002659, baseEnd_1002659] using wordTrace_append hprefix tailTrace_1002659
  have hstable : (prefixWord ++ tailWord_1002659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002659).length < 2 ^ (prefixWord ++ tailWord_1002659).sum := by decide
  have hdescent : baseEnd_1002659 < baseStart_1002659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002660 : List Nat := [2, 3, 1, 2, 3, 2, 1, 3, 2, 2, 2]
def baseStart_1002660 : Nat := 118140960795 + 1002660 * 2 ^ 59
def prefixEnd_1002660 : Nat := 4983230072969 + 3 ^ 40 * 1002660 * 2
def baseEnd_1002660 : Nat := 514846513037152321838857

theorem tailTrace_1002660 : CollatzResearch.WordTrace tailWord_1002660 prefixEnd_1002660 514846513037152321838857 := by
  unfold tailWord_1002660
  simp only [CollatzResearch.WordTrace]
  refine ⟨18285007273770767769970717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24380009698361023693294289 18285007273770767769970717)
  ·
    refine ⟨6856877727664037913739019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18285007273770767769970717 6856877727664037913739019)
    ·
      refine ⟨10285316591496056870608529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6856877727664037913739019 10285316591496056870608529)
      ·
        refine ⟨7713987443622042652956397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10285316591496056870608529 7713987443622042652956397)
        ·
          refine ⟨2892745291358265994858649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7713987443622042652956397 2892745291358265994858649)
          ·
            refine ⟨2169558968518699496143987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2892745291358265994858649 2169558968518699496143987)
            ·
              refine ⟨3254338452778049244215981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169558968518699496143987 3254338452778049244215981)
              ·
                refine ⟨1220376919791768466580993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254338452778049244215981 1220376919791768466580993)
                ·
                  refine ⟨915282689843826349935745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1220376919791768466580993 915282689843826349935745)
                  ·
                    refine ⟨686462017382869762451809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 915282689843826349935745 686462017382869762451809)
                    ·
                      refine ⟨514846513037152321838857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686462017382869762451809 514846513037152321838857)
                      ·
                        rfl

theorem cell23_1002660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_1002660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002660 prefixEnd_1002660 := by exact prefixLift 1002660
  have htrace : WordTrace (prefixWord ++ tailWord_1002660) baseStart_1002660 baseEnd_1002660 := by
    simpa [prefixWord, tailWord_1002660, baseEnd_1002660] using wordTrace_append hprefix tailTrace_1002660
  have hstable : (prefixWord ++ tailWord_1002660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002660).length < 2 ^ (prefixWord ++ tailWord_1002660).sum := by decide
  have hdescent : baseEnd_1002660 < baseStart_1002660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002699 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 4]
def baseStart_1002699 : Nat := 118140960795 + 1002699 * 2 ^ 59
def prefixEnd_1002699 : Nat := 4983230072969 + 3 ^ 40 * 1002699 * 2
def baseEnd_1002699 : Nat := 514866538782677669251177

theorem tailTrace_1002699 : CollatzResearch.WordTrace tailWord_1002699 prefixEnd_1002699 514866538782677669251177 := by
  unfold tailWord_1002699
  simp only [CollatzResearch.WordTrace]
  refine ⟨36571436994400245200611151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24380957996266830133740767 36571436994400245200611151)
  ·
    refine ⟨54857155491600367800916727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36571436994400245200611151 54857155491600367800916727)
    ·
      refine ⟨82285733237400551701375091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54857155491600367800916727 82285733237400551701375091)
      ·
        refine ⟨123428599856100827552062637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82285733237400551701375091 123428599856100827552062637)
        ·
          refine ⟨46285724946037810332023489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123428599856100827552062637 46285724946037810332023489)
          ·
            refine ⟨34714293709528357749017617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46285724946037810332023489 34714293709528357749017617)
            ·
              refine ⟨26035720282146268311763213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34714293709528357749017617 26035720282146268311763213)
              ·
                refine ⟨9763395105804850616911205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26035720282146268311763213 9763395105804850616911205)
                ·
                  refine ⟨1830636582338409490670851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9763395105804850616911205 1830636582338409490670851)
                  ·
                    refine ⟨2745954873507614236006277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830636582338409490670851 2745954873507614236006277)
                    ·
                      refine ⟨514866538782677669251177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2745954873507614236006277 514866538782677669251177)
                      ·
                        rfl

theorem cell23_1002699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 1, 4].length) (baseStart_1002699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002699 prefixEnd_1002699 := by exact prefixLift 1002699
  have htrace : WordTrace (prefixWord ++ tailWord_1002699) baseStart_1002699 baseEnd_1002699 := by
    simpa [prefixWord, tailWord_1002699, baseEnd_1002699] using wordTrace_append hprefix tailTrace_1002699
  have hstable : (prefixWord ++ tailWord_1002699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002699).length < 2 ^ (prefixWord ++ tailWord_1002699).sum := by decide
  have hdescent : baseEnd_1002699 < baseStart_1002699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002710 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_1002710 : Nat := 118140960795 + 1002710 * 2 ^ 59
def prefixEnd_1002710 : Nat := 4983230072969 + 3 ^ 40 * 1002710 * 2
def baseEnd_1002710 : Nat := 514872187069877126213627

theorem tailTrace_1002710 : CollatzResearch.WordTrace tailWord_1002710 prefixEnd_1002710 514872187069877126213627 := by
  unfold tailWord_1002710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2285739887335024629953849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24381225464906929386174389 2285739887335024629953849)
  ·
    refine ⟨1714304915501268472465387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2285739887335024629953849 1714304915501268472465387)
    ·
      refine ⟨2571457373251902708698081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1714304915501268472465387 2571457373251902708698081)
      ·
        refine ⟨1928593029938927031523561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2571457373251902708698081 1928593029938927031523561)
        ·
          refine ⟨1446444772454195273642671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928593029938927031523561 1446444772454195273642671)
          ·
            refine ⟨2169667158681292910464007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446444772454195273642671 2169667158681292910464007)
            ·
              refine ⟨3254500738021939365696011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169667158681292910464007 3254500738021939365696011)
              ·
                refine ⟨4881751107032909048544017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254500738021939365696011 4881751107032909048544017)
                ·
                  refine ⟨3661313330274681786408013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4881751107032909048544017 3661313330274681786408013)
                  ·
                    refine ⟨1372992498853005669903005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3661313330274681786408013 1372992498853005669903005)
                    ·
                      refine ⟨514872187069877126213627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1372992498853005669903005 514872187069877126213627)
                      ·
                        rfl

theorem cell23_1002710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_1002710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002710 prefixEnd_1002710 := by exact prefixLift 1002710
  have htrace : WordTrace (prefixWord ++ tailWord_1002710) baseStart_1002710 baseEnd_1002710 := by
    simpa [prefixWord, tailWord_1002710, baseEnd_1002710] using wordTrace_append hprefix tailTrace_1002710
  have hstable : (prefixWord ++ tailWord_1002710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002710).length < 2 ^ (prefixWord ++ tailWord_1002710).sum := by decide
  have hdescent : baseEnd_1002710 < baseStart_1002710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002733 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1002733 : Nat := 118140960795 + 1002733 * 2 ^ 59
def prefixEnd_1002733 : Nat := 4983230072969 + 3 ^ 40 * 1002733 * 2
def baseEnd_1002733 : Nat := 514883997124930536226021

theorem tailTrace_1002733 : CollatzResearch.WordTrace tailWord_1002733 prefixEnd_1002733 514883997124930536226021 := by
  unfold tailWord_1002733
  simp only [CollatzResearch.WordTrace]
  refine ⟨36572677076277069007348853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24381784717518046004899235 36572677076277069007348853)
  ·
    refine ⟨3428688475900975219438955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36572677076277069007348853 3428688475900975219438955)
    ·
      refine ⟨5143032713851462829158433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3428688475900975219438955 5143032713851462829158433)
      ·
        refine ⟨3857274535388597121868825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5143032713851462829158433 3857274535388597121868825)
        ·
          refine ⟨2892955901541447841401619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3857274535388597121868825 2892955901541447841401619)
          ·
            refine ⟨4339433852312171762102429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2892955901541447841401619 4339433852312171762102429)
            ·
              refine ⟨1627287694617064410788411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4339433852312171762102429 1627287694617064410788411)
              ·
                refine ⟨2440931541925596616182617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627287694617064410788411 2440931541925596616182617)
                ·
                  refine ⟨1830698656444197462136963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2440931541925596616182617 1830698656444197462136963)
                  ·
                    refine ⟨2746047984666296193205445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1830698656444197462136963 2746047984666296193205445)
                    ·
                      refine ⟨514883997124930536226021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2746047984666296193205445 514883997124930536226021)
                      ·
                        rfl

theorem cell23_1002733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1002733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002733 prefixEnd_1002733 := by exact prefixLift 1002733
  have htrace : WordTrace (prefixWord ++ tailWord_1002733) baseStart_1002733 baseEnd_1002733 := by
    simpa [prefixWord, tailWord_1002733, baseEnd_1002733] using wordTrace_append hprefix tailTrace_1002733
  have hstable : (prefixWord ++ tailWord_1002733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002733).length < 2 ^ (prefixWord ++ tailWord_1002733).sum := by decide
  have hdescent : baseEnd_1002733 < baseStart_1002733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002756 : List Nat := [2, 3, 2, 2, 2, 2, 1, 1, 8]
def baseStart_1002756 : Nat := 118140960795 + 1002756 * 2 ^ 59
def prefixEnd_1002756 : Nat := 4983230072969 + 3 ^ 40 * 1002756 * 2
def baseEnd_1002756 : Nat := 57210645242220438470935

theorem tailTrace_1002756 : CollatzResearch.WordTrace tailWord_1002756 prefixEnd_1002756 57210645242220438470935 := by
  unfold tailWord_1002756
  simp only [CollatzResearch.WordTrace]
  refine ⟨18286757977596871967718061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24382343970129162623624081 18286757977596871967718061)
  ·
    refine ⟨6857534241598826987894273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18286757977596871967718061 6857534241598826987894273)
    ·
      refine ⟨5143150681199120240920705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6857534241598826987894273 5143150681199120240920705)
      ·
        refine ⟨3857363010899340180690529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5143150681199120240920705 3857363010899340180690529)
        ·
          refine ⟨2893022258174505135517897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3857363010899340180690529 2893022258174505135517897)
          ·
            refine ⟨2169766693630878851638423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2893022258174505135517897 2169766693630878851638423)
            ·
              refine ⟨3254650040446318277457635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2169766693630878851638423 3254650040446318277457635)
              ·
                refine ⟨4881975060669477416186453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3254650040446318277457635 4881975060669477416186453)
                ·
                  refine ⟨57210645242220438470935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4881975060669477416186453 57210645242220438470935)
                  ·
                    rfl

theorem cell23_1002756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_1002756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002756 prefixEnd_1002756 := by exact prefixLift 1002756
  have htrace : WordTrace (prefixWord ++ tailWord_1002756) baseStart_1002756 baseEnd_1002756 := by
    simpa [prefixWord, tailWord_1002756, baseEnd_1002756] using wordTrace_append hprefix tailTrace_1002756
  have hstable : (prefixWord ++ tailWord_1002756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002756).length < 2 ^ (prefixWord ++ tailWord_1002756).sum := by decide
  have hdescent : baseEnd_1002756 < baseStart_1002756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002799 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 3, 6]
def baseStart_1002799 : Nat := 118140960795 + 1002799 * 2 ^ 59
def prefixEnd_1002799 : Nat := 4983230072969 + 3 ^ 40 * 1002799 * 2
def baseEnd_1002799 : Nat := 171639295616042426000239

theorem tailTrace_1002799 : CollatzResearch.WordTrace tailWord_1002799 prefixEnd_1002799 171639295616042426000239 := by
  unfold tailWord_1002799
  simp only [CollatzResearch.WordTrace]
  refine ⟨36575084294037962279251451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24383389529358641519500967 36575084294037962279251451)
  ·
    refine ⟨54862626441056943418877177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36575084294037962279251451 54862626441056943418877177)
    ·
      refine ⟨41146969830792707564157883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54862626441056943418877177 41146969830792707564157883)
      ·
        refine ⟨61720454746189061346236825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41146969830792707564157883 61720454746189061346236825)
        ·
          refine ⟨46290341059641796009677619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61720454746189061346236825 46290341059641796009677619)
          ·
            refine ⟨69435511589462694014516429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46290341059641796009677619 69435511589462694014516429)
            ·
              refine ⟨26038316846048510255443661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69435511589462694014516429 26038316846048510255443661)
              ·
                refine ⟨9764368817268191345791373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26038316846048510255443661 9764368817268191345791373)
                ·
                  refine ⟨3661638306475571754671765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9764368817268191345791373 3661638306475571754671765)
                  ·
                    refine ⟨171639295616042426000239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3661638306475571754671765 171639295616042426000239)
                    ·
                      rfl

theorem cell23_1002799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 3, 6].length) (baseStart_1002799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002799 prefixEnd_1002799 := by exact prefixLift 1002799
  have htrace : WordTrace (prefixWord ++ tailWord_1002799) baseStart_1002799 baseEnd_1002799 := by
    simpa [prefixWord, tailWord_1002799, baseEnd_1002799] using wordTrace_append hprefix tailTrace_1002799
  have hstable : (prefixWord ++ tailWord_1002799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002799).length < 2 ^ (prefixWord ++ tailWord_1002799).sum := by decide
  have hdescent : baseEnd_1002799 < baseStart_1002799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002816 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 4, 4]
def baseStart_1002816 : Nat := 118140960795 + 1002816 * 2 ^ 59
def prefixEnd_1002816 : Nat := 4983230072969 + 3 ^ 40 * 1002816 * 2
def baseEnd_1002816 : Nat := 171642205339751237162713

theorem tailTrace_1002816 : CollatzResearch.WordTrace tailWord_1002816 prefixEnd_1002816 171642205339751237162713 := by
  unfold tailWord_1002816
  simp only [CollatzResearch.WordTrace]
  refine ⟨18287852167488187091310151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24383802889984249455080201 18287852167488187091310151)
  ·
    refine ⟨27431778251232280636965227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18287852167488187091310151 27431778251232280636965227)
    ·
      refine ⟨41147667376848420955447841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27431778251232280636965227 41147667376848420955447841)
      ·
        refine ⟨30860750532636315716585881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41147667376848420955447841 30860750532636315716585881)
        ·
          refine ⟨23145562899477236787439411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30860750532636315716585881 23145562899477236787439411)
          ·
            refine ⟨34718344349215855181159117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23145562899477236787439411 34718344349215855181159117)
            ·
              refine ⟨13019379130955945692934669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34718344349215855181159117 13019379130955945692934669)
              ·
                refine ⟨4882267174108479634850501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13019379130955945692934669 4882267174108479634850501)
                ·
                  refine ⟨915425095145339931534469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4882267174108479634850501 915425095145339931534469)
                  ·
                    refine ⟨171642205339751237162713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 915425095145339931534469 171642205339751237162713)
                    ·
                      rfl

theorem cell23_1002816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 4, 4].length) (baseStart_1002816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002816 prefixEnd_1002816 := by exact prefixLift 1002816
  have htrace : WordTrace (prefixWord ++ tailWord_1002816) baseStart_1002816 baseEnd_1002816 := by
    simpa [prefixWord, tailWord_1002816, baseEnd_1002816] using wordTrace_append hprefix tailTrace_1002816
  have hstable : (prefixWord ++ tailWord_1002816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002816).length < 2 ^ (prefixWord ++ tailWord_1002816).sum := by decide
  have hdescent : baseEnd_1002816 < baseStart_1002816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002817 : List Nat := [1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1002817 : Nat := 118140960795 + 1002817 * 2 ^ 59
def prefixEnd_1002817 : Nat := 4983230072969 + 3 ^ 40 * 1002817 * 2
def baseEnd_1002817 : Nat := 514927129499908207575635

theorem tailTrace_1002817 : CollatzResearch.WordTrace tailWord_1002817 prefixEnd_1002817 514927129499908207575635 := by
  unfold tailWord_1002817
  simp only [CollatzResearch.WordTrace]
  refine ⟨36575740807972751353406705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24383827205315167568937803 36575740807972751353406705)
  ·
    refine ⟨27431805605979563515055029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36575740807972751353406705 27431805605979563515055029)
    ·
      refine ⟨2571731775560584079536409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27431805605979563515055029 2571731775560584079536409)
      ·
        refine ⟨1928798831670438059652307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2571731775560584079536409 1928798831670438059652307)
        ·
          refine ⟨2893198247505657089478461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1928798831670438059652307 2893198247505657089478461)
          ·
            refine ⟨1084949342814621408554423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2893198247505657089478461 1084949342814621408554423)
            ·
              refine ⟨1627424014221932112831635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1084949342814621408554423 1627424014221932112831635)
              ·
                refine ⟨2441136021332898169247453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627424014221932112831635 2441136021332898169247453)
                ·
                  refine ⟨915426007999836813467795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2441136021332898169247453 915426007999836813467795)
                  ·
                    refine ⟨1373139011999755220201693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915426007999836813467795 1373139011999755220201693)
                    ·
                      refine ⟨514927129499908207575635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1373139011999755220201693 514927129499908207575635)
                      ·
                        rfl

theorem cell23_1002817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1002817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002817 prefixEnd_1002817 := by exact prefixLift 1002817
  have htrace : WordTrace (prefixWord ++ tailWord_1002817) baseStart_1002817 baseEnd_1002817 := by
    simpa [prefixWord, tailWord_1002817, baseEnd_1002817] using wordTrace_append hprefix tailTrace_1002817
  have hstable : (prefixWord ++ tailWord_1002817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002817).length < 2 ^ (prefixWord ++ tailWord_1002817).sum := by decide
  have hdescent : baseEnd_1002817 < baseStart_1002817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002833 : List Nat := [1, 2, 2, 1, 4, 1, 3, 3, 2, 4]
def baseStart_1002833 : Nat := 118140960795 + 1002833 * 2 ^ 59
def prefixEnd_1002833 : Nat := 4983230072969 + 3 ^ 40 * 1002833 * 2
def baseEnd_1002833 : Nat := 171645115063460048325187

theorem tailTrace_1002833 : CollatzResearch.WordTrace tailWord_1002833 prefixEnd_1002833 171645115063460048325187 := by
  unfold tailWord_1002833
  simp only [CollatzResearch.WordTrace]
  refine ⟨36576324375914786085989153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24384216250609857390659435 36576324375914786085989153)
  ·
    refine ⟨27432243281936089564491865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36576324375914786085989153 27432243281936089564491865)
    ·
      refine ⟨20574182461452067173368899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27432243281936089564491865 20574182461452067173368899)
      ·
        refine ⟨30861273692178100760053349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20574182461452067173368899 30861273692178100760053349)
        ·
          refine ⟨5786488817283393892510003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30861273692178100760053349 5786488817283393892510003)
          ·
            refine ⟨8679733225925090838765005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786488817283393892510003 8679733225925090838765005)
            ·
              refine ⟨3254899959721909064536877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8679733225925090838765005 3254899959721909064536877)
              ·
                refine ⟨1220587484895715899201329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3254899959721909064536877 1220587484895715899201329)
                ·
                  refine ⟨915440613671786924400997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1220587484895715899201329 915440613671786924400997)
                  ·
                    refine ⟨171645115063460048325187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 915440613671786924400997 171645115063460048325187)
                    ·
                      rfl

theorem cell23_1002833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_1002833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002833 prefixEnd_1002833 := by exact prefixLift 1002833
  have htrace : WordTrace (prefixWord ++ tailWord_1002833) baseStart_1002833 baseEnd_1002833 := by
    simpa [prefixWord, tailWord_1002833, baseEnd_1002833] using wordTrace_append hprefix tailTrace_1002833
  have hstable : (prefixWord ++ tailWord_1002833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002833).length < 2 ^ (prefixWord ++ tailWord_1002833).sum := by decide
  have hdescent : baseEnd_1002833 < baseStart_1002833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002836 : List Nat := [2, 4, 1, 1, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1002836 : Nat := 118140960795 + 1002836 * 2 ^ 59
def prefixEnd_1002836 : Nat := 4983230072969 + 3 ^ 40 * 1002836 * 2
def baseEnd_1002836 : Nat := 514936885632343633238047

theorem tailTrace_1002836 : CollatzResearch.WordTrace tailWord_1002836 prefixEnd_1002836 514936885632343633238047 := by
  unfold tailWord_1002836
  simp only [CollatzResearch.WordTrace]
  refine ⟨18288216897451958799174181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24384289196602611732232241 18288216897451958799174181)
  ·
    refine ⟨3429040668272242274845159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18288216897451958799174181 3429040668272242274845159)
    ·
      refine ⟨5143561002408363412267739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3429040668272242274845159 5143561002408363412267739)
      ·
        refine ⟨7715341503612545118401609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5143561002408363412267739 7715341503612545118401609)
        ·
          refine ⟨5786506127709408838801207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7715341503612545118401609 5786506127709408838801207)
          ·
            refine ⟨8679759191564113258201811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786506127709408838801207 8679759191564113258201811)
            ·
              refine ⟨13019638787346169887302717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8679759191564113258201811 13019638787346169887302717)
              ·
                refine ⟨4882364545254813707738519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13019638787346169887302717 4882364545254813707738519)
                ·
                  refine ⟨7323546817882220561607779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4882364545254813707738519 7323546817882220561607779)
                  ·
                    refine ⟨10985320226823330842411669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7323546817882220561607779 10985320226823330842411669)
                    ·
                      refine ⟨514936885632343633238047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 10985320226823330842411669 514936885632343633238047)
                      ·
                        rfl

theorem cell23_1002836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1002836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002836 prefixEnd_1002836 := by exact prefixLift 1002836
  have htrace : WordTrace (prefixWord ++ tailWord_1002836) baseStart_1002836 baseEnd_1002836 := by
    simpa [prefixWord, tailWord_1002836, baseEnd_1002836] using wordTrace_append hprefix tailTrace_1002836
  have hstable : (prefixWord ++ tailWord_1002836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002836).length < 2 ^ (prefixWord ++ tailWord_1002836).sum := by decide
  have hdescent : baseEnd_1002836 < baseStart_1002836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002859 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 3, 9]
def baseStart_1002859 : Nat := 118140960795 + 1002859 * 2 ^ 59
def prefixEnd_1002859 : Nat := 4983230072969 + 3 ^ 40 * 1002859 * 2
def baseEnd_1002859 : Nat := 171649565229132347750147

theorem tailTrace_1002859 : CollatzResearch.WordTrace tailWord_1002859 prefixEnd_1002859 171649565229132347750147 := by
  unfold tailWord_1002859
  simp only [CollatzResearch.WordTrace]
  refine ⟨36577272673820592526435631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24384848449213728350957087 36577272673820592526435631)
  ·
    refine ⟨54865909010730888789653447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36577272673820592526435631 54865909010730888789653447)
    ·
      refine ⟨82298863516096333184480171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54865909010730888789653447 82298863516096333184480171)
      ·
        refine ⟨123448295274144499776720257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82298863516096333184480171 123448295274144499776720257)
        ·
          refine ⟨92586221455608374832540193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123448295274144499776720257 92586221455608374832540193)
          ·
            refine ⟨69439666091706281124405145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92586221455608374832540193 69439666091706281124405145)
            ·
              refine ⟨52079749568779710843303859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69439666091706281124405145 52079749568779710843303859)
              ·
                refine ⟨78119624353169566264955789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52079749568779710843303859 78119624353169566264955789)
                ·
                  refine ⟨29294859132438587349358421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78119624353169566264955789 29294859132438587349358421)
                  ·
                    refine ⟨171649565229132347750147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29294859132438587349358421 171649565229132347750147)
                    ·
                      rfl

theorem cell23_1002859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 9].length) (baseStart_1002859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002859 prefixEnd_1002859 := by exact prefixLift 1002859
  have htrace : WordTrace (prefixWord ++ tailWord_1002859) baseStart_1002859 baseEnd_1002859 := by
    simpa [prefixWord, tailWord_1002859, baseEnd_1002859] using wordTrace_append hprefix tailTrace_1002859
  have hstable : (prefixWord ++ tailWord_1002859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002859).length < 2 ^ (prefixWord ++ tailWord_1002859).sum := by decide
  have hdescent : baseEnd_1002859 < baseStart_1002859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002873 : List Nat := [1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 3]
def baseStart_1002873 : Nat := 118140960795 + 1002873 * 2 ^ 59
def prefixEnd_1002873 : Nat := 4983230072969 + 3 ^ 40 * 1002873 * 2
def baseEnd_1002873 : Nat := 514955884416559988475377

theorem tailTrace_1002873 : CollatzResearch.WordTrace tailWord_1002873 prefixEnd_1002873 514955884416559988475377 := by
  unfold tailWord_1002873
  simp only [CollatzResearch.WordTrace]
  refine ⟨36577783295769872917445273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24385188863846581944963515 36577783295769872917445273)
  ·
    refine ⟨27433337471827404688083955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36577783295769872917445273 27433337471827404688083955)
    ·
      refine ⟨41150006207741107032125933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27433337471827404688083955 41150006207741107032125933)
      ·
        refine ⟨15431252327902915137047225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41150006207741107032125933 15431252327902915137047225)
        ·
          refine ⟨11573439245927186352785419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15431252327902915137047225 11573439245927186352785419)
          ·
            refine ⟨17360158868890779529178129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11573439245927186352785419 17360158868890779529178129)
            ·
              refine ⟨13020119151668084646883597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17360158868890779529178129 13020119151668084646883597)
              ·
                refine ⟨4882544681875531742581349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13020119151668084646883597 4882544681875531742581349)
                ·
                  refine ⟨915477127851662201734003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4882544681875531742581349 915477127851662201734003)
                  ·
                    refine ⟨1373215691777493302601005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915477127851662201734003 1373215691777493302601005)
                    ·
                      refine ⟨514955884416559988475377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1373215691777493302601005 514955884416559988475377)
                      ·
                        rfl

theorem cell23_1002873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_1002873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002873 prefixEnd_1002873 := by exact prefixLift 1002873
  have htrace : WordTrace (prefixWord ++ tailWord_1002873) baseStart_1002873 baseEnd_1002873 := by
    simpa [prefixWord, tailWord_1002873, baseEnd_1002873] using wordTrace_append hprefix tailTrace_1002873
  have hstable : (prefixWord ++ tailWord_1002873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002873).length < 2 ^ (prefixWord ++ tailWord_1002873).sum := by decide
  have hdescent : baseEnd_1002873 < baseStart_1002873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002906 : List Nat := [3, 1, 1, 4, 1, 1, 1, 2, 1, 8]
def baseStart_1002906 : Nat := 118140960795 + 1002906 * 2 ^ 59
def prefixEnd_1002906 : Nat := 4983230072969 + 3 ^ 40 * 1002906 * 2
def baseEnd_1002906 : Nat := 171657609759386119787575

theorem tailTrace_1002906 : CollatzResearch.WordTrace tailWord_1002906 prefixEnd_1002906 171657609759386119787575 := by
  unfold tailWord_1002906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144746726162579888349143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24385991269766879702264381 9144746726162579888349143)
  ·
    refine ⟨13717120089243869832523715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9144746726162579888349143 13717120089243869832523715)
    ·
      refine ⟨20575680133865804748785573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13717120089243869832523715 20575680133865804748785573)
      ·
        refine ⟨3857940025099838390397295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20575680133865804748785573 3857940025099838390397295)
        ·
          refine ⟨5786910037649757585595943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3857940025099838390397295 5786910037649757585595943)
          ·
            refine ⟨8680365056474636378393915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5786910037649757585595943 8680365056474636378393915)
            ·
              refine ⟨13020547584711954567590873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8680365056474636378393915 13020547584711954567590873)
              ·
                refine ⟨9765410688533965925693155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13020547584711954567590873 9765410688533965925693155)
                ·
                  refine ⟨14648116032800948888539733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765410688533965925693155 14648116032800948888539733)
                  ·
                    refine ⟨171657609759386119787575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 14648116032800948888539733 171657609759386119787575)
                    ·
                      rfl

theorem cell23_1002906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_1002906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002906 prefixEnd_1002906 := by exact prefixLift 1002906
  have htrace : WordTrace (prefixWord ++ tailWord_1002906) baseStart_1002906 baseEnd_1002906 := by
    simpa [prefixWord, tailWord_1002906, baseEnd_1002906] using wordTrace_append hprefix tailTrace_1002906
  have hstable : (prefixWord ++ tailWord_1002906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002906).length < 2 ^ (prefixWord ++ tailWord_1002906).sum := by decide
  have hdescent : baseEnd_1002906 < baseStart_1002906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002916 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1002916 : Nat := 118140960795 + 1002916 * 2 ^ 59
def prefixEnd_1002916 : Nat := 4983230072969 + 3 ^ 40 * 1002916 * 2
def baseEnd_1002916 : Nat := 514977964084703320237679

theorem tailTrace_1002916 : CollatzResearch.WordTrace tailWord_1002916 prefixEnd_1002916 514977964084703320237679 := by
  unfold tailWord_1002916
  simp only [CollatzResearch.WordTrace]
  refine ⟨18289675817307045630630301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24386234423076060840840401 18289675817307045630630301)
  ·
    refine ⟨6858628431490142111486363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18289675817307045630630301 6858628431490142111486363)
    ·
      refine ⟨10287942647235213167229545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6858628431490142111486363 10287942647235213167229545)
      ·
        refine ⟨7715956985426409875422159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10287942647235213167229545 7715956985426409875422159)
        ·
          refine ⟨11573935478139614813133239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7715956985426409875422159 11573935478139614813133239)
          ·
            refine ⟨17360903217209422219699859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11573935478139614813133239 17360903217209422219699859)
            ·
              refine ⟨26041354825814133329549789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17360903217209422219699859 26041354825814133329549789)
              ·
                refine ⟨9765508059680299998581171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26041354825814133329549789 9765508059680299998581171)
                ·
                  refine ⟨14648262089520449997871757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9765508059680299998581171 14648262089520449997871757)
                  ·
                    refine ⟨5493098283570168749201909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14648262089520449997871757 5493098283570168749201909)
                    ·
                      refine ⟨514977964084703320237679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5493098283570168749201909 514977964084703320237679)
                      ·
                        rfl

theorem cell23_1002916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1002916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002916 prefixEnd_1002916 := by exact prefixLift 1002916
  have htrace : WordTrace (prefixWord ++ tailWord_1002916) baseStart_1002916 baseEnd_1002916 := by
    simpa [prefixWord, tailWord_1002916, baseEnd_1002916] using wordTrace_append hprefix tailTrace_1002916
  have hstable : (prefixWord ++ tailWord_1002916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002916).length < 2 ^ (prefixWord ++ tailWord_1002916).sum := by decide
  have hdescent : baseEnd_1002916 < baseStart_1002916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002936 : List Nat := [2, 1, 2, 1, 2, 2, 3, 3, 7]
def baseStart_1002936 : Nat := 118140960795 + 1002936 * 2 ^ 59
def prefixEnd_1002936 : Nat := 4983230072969 + 3 ^ 40 * 1002936 * 2
def baseEnd_1002936 : Nat := 57220914855310360220843

theorem tailTrace_1002936 : CollatzResearch.WordTrace tailWord_1002936 prefixEnd_1002936 57220914855310360220843 := by
  unfold tailWord_1002936
  simp only [CollatzResearch.WordTrace]
  refine ⟨18290040547270817338494331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24386720729694423117992441 18290040547270817338494331)
  ·
    refine ⟨27435060820906226007741497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18290040547270817338494331 27435060820906226007741497)
    ·
      refine ⟨20576295615679669505806123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27435060820906226007741497 20576295615679669505806123)
      ·
        refine ⟨30864443423519504258709185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20576295615679669505806123 30864443423519504258709185)
        ·
          refine ⟨23148332567639628194031889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30864443423519504258709185 23148332567639628194031889)
          ·
            refine ⟨17361249425729721145523917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23148332567639628194031889 17361249425729721145523917)
            ·
              refine ⟨6510468534648645429571469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17361249425729721145523917 6510468534648645429571469)
              ·
                refine ⟨2441425700493242036089301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6510468534648645429571469 2441425700493242036089301)
                ·
                  refine ⟨57220914855310360220843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2441425700493242036089301 57220914855310360220843)
                  ·
                    rfl

theorem cell23_1002936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 3, 7].length) (baseStart_1002936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002936 prefixEnd_1002936 := by exact prefixLift 1002936
  have htrace : WordTrace (prefixWord ++ tailWord_1002936) baseStart_1002936 baseEnd_1002936 := by
    simpa [prefixWord, tailWord_1002936, baseEnd_1002936] using wordTrace_append hprefix tailTrace_1002936
  have hstable : (prefixWord ++ tailWord_1002936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002936).length < 2 ^ (prefixWord ++ tailWord_1002936).sum := by decide
  have hdescent : baseEnd_1002936 < baseStart_1002936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002970 : List Nat := [3, 1, 1, 2, 3, 2, 3, 3, 5]
def baseStart_1002970 : Nat := 118140960795 + 1002970 * 2 ^ 59
def prefixEnd_1002970 : Nat := 4983230072969 + 3 ^ 40 * 1002970 * 2
def baseEnd_1002970 : Nat := 57222854671116234329159

theorem tailTrace_1002970 : CollatzResearch.WordTrace tailWord_1002970 prefixEnd_1002970 57222854671116234329159 := by
  unfold tailWord_1002970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145330294104614620931591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24387547450945638989150909 9145330294104614620931591)
  ·
    refine ⟨13717995441156921931397387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9145330294104614620931591 13717995441156921931397387)
    ·
      refine ⟨20576993161735382897096081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13717995441156921931397387 20576993161735382897096081)
      ·
        refine ⟨15432744871301537172822061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20576993161735382897096081 15432744871301537172822061)
        ·
          refine ⟨5787279326738076439808273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15432744871301537172822061 5787279326738076439808273)
          ·
            refine ⟨4340459495053557329856205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787279326738076439808273 4340459495053557329856205)
            ·
              refine ⟨1627672310645083998696077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4340459495053557329856205 1627672310645083998696077)
              ·
                refine ⟨610377116491906499511029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1627672310645083998696077 610377116491906499511029)
                ·
                  refine ⟨57222854671116234329159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610377116491906499511029 57222854671116234329159)
                  ·
                    rfl

theorem cell23_1002970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 3, 5].length) (baseStart_1002970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002970 prefixEnd_1002970 := by exact prefixLift 1002970
  have htrace : WordTrace (prefixWord ++ tailWord_1002970) baseStart_1002970 baseEnd_1002970 := by
    simpa [prefixWord, tailWord_1002970, baseEnd_1002970] using wordTrace_append hprefix tailTrace_1002970
  have hstable : (prefixWord ++ tailWord_1002970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002970).length < 2 ^ (prefixWord ++ tailWord_1002970).sum := by decide
  have hdescent : baseEnd_1002970 < baseStart_1002970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002983 : List Nat := [1, 1, 5, 2, 1, 2, 1, 1, 4, 5]
def baseStart_1002983 : Nat := 118140960795 + 1002983 * 2 ^ 59
def prefixEnd_1002983 : Nat := 4983230072969 + 3 ^ 40 * 1002983 * 2
def baseEnd_1002983 : Nat := 171670789096184852699957

theorem tailTrace_1002983 : CollatzResearch.WordTrace tailWord_1002983 prefixEnd_1002983 171670789096184852699957 := by
  unfold tailWord_1002983
  simp only [CollatzResearch.WordTrace]
  refine ⟨36581795325371361703949603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24387863550247574469299735 36581795325371361703949603)
  ·
    refine ⟨54872692988057042555924405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36581795325371361703949603 54872692988057042555924405)
    ·
      refine ⟨5144314967630347739617913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54872692988057042555924405 5144314967630347739617913)
      ·
        refine ⟨3858236225722760804713435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5144314967630347739617913 3858236225722760804713435)
        ·
          refine ⟨5787354338584141207070153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858236225722760804713435 5787354338584141207070153)
          ·
            refine ⟨4340515753938105905302615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5787354338584141207070153 4340515753938105905302615)
            ·
              refine ⟨6510773630907158857953923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4340515753938105905302615 6510773630907158857953923)
              ·
                refine ⟨9766160446360738286930885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510773630907158857953923 9766160446360738286930885)
                ·
                  refine ⟨1831155083692638428799541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9766160446360738286930885 1831155083692638428799541)
                  ·
                    refine ⟨171670789096184852699957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1831155083692638428799541 171670789096184852699957)
                    ·
                      rfl

theorem cell23_1002983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 1, 4, 5].length) (baseStart_1002983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002983 prefixEnd_1002983 := by exact prefixLift 1002983
  have htrace : WordTrace (prefixWord ++ tailWord_1002983) baseStart_1002983 baseEnd_1002983 := by
    simpa [prefixWord, tailWord_1002983, baseEnd_1002983] using wordTrace_append hprefix tailTrace_1002983
  have hstable : (prefixWord ++ tailWord_1002983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002983).length < 2 ^ (prefixWord ++ tailWord_1002983).sum := by decide
  have hdescent : baseEnd_1002983 < baseStart_1002983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002990 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2]
def baseStart_1002990 : Nat := 118140960795 + 1002990 * 2 ^ 59
def prefixEnd_1002990 : Nat := 4983230072969 + 3 ^ 40 * 1002990 * 2
def baseEnd_1002990 : Nat := 515015961653136030712339

theorem tailTrace_1002990 : CollatzResearch.WordTrace tailWord_1002990 prefixEnd_1002990 515015961653136030712339 := by
  unfold tailWord_1002990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4572756329543250237431803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24388033757564001266302949 4572756329543250237431803)
  ·
    refine ⟨6859134494314875356147705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4572756329543250237431803 6859134494314875356147705)
    ·
      refine ⟨5144350870736156517110779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6859134494314875356147705 5144350870736156517110779)
      ·
        refine ⟨7716526306104234775666169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5144350870736156517110779 7716526306104234775666169)
        ·
          refine ⟨5787394729578176081749627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7716526306104234775666169 5787394729578176081749627)
          ·
            refine ⟨8681092094367264122624441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5787394729578176081749627 8681092094367264122624441)
            ·
              refine ⟨6510819070775448091968331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8681092094367264122624441 6510819070775448091968331)
              ·
                refine ⟨9766228606163172137952497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6510819070775448091968331 9766228606163172137952497)
                ·
                  refine ⟨7324671454622379103464373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9766228606163172137952497 7324671454622379103464373)
                  ·
                    refine ⟨686687948870848040949785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7324671454622379103464373 686687948870848040949785)
                    ·
                      refine ⟨515015961653136030712339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686687948870848040949785 515015961653136030712339)
                      ·
                        rfl

theorem cell23_1002990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_1002990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002990 prefixEnd_1002990 := by exact prefixLift 1002990
  have htrace : WordTrace (prefixWord ++ tailWord_1002990) baseStart_1002990 baseEnd_1002990 := by
    simpa [prefixWord, tailWord_1002990, baseEnd_1002990] using wordTrace_append hprefix tailTrace_1002990
  have hstable : (prefixWord ++ tailWord_1002990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002990).length < 2 ^ (prefixWord ++ tailWord_1002990).sum := by decide
  have hdescent : baseEnd_1002990 < baseStart_1002990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1002993 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_1002993 : Nat := 118140960795 + 1002993 * 2 ^ 59
def prefixEnd_1002993 : Nat := 4983230072969 + 3 ^ 40 * 1002993 * 2
def baseEnd_1002993 : Nat := 515017502095099518974825

theorem tailTrace_1002993 : CollatzResearch.WordTrace tailWord_1002993 prefixEnd_1002993 515017502095099518974825 := by
  unfold tailWord_1002993
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582160055335133411813633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24388106703556755607875755 36582160055335133411813633)
  ·
    refine ⟨27436620041501350058860225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36582160055335133411813633 27436620041501350058860225)
    ·
      refine ⟨20577465031126012544145169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27436620041501350058860225 20577465031126012544145169)
      ·
        refine ⟨15433098773344509408108877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20577465031126012544145169 15433098773344509408108877)
        ·
          refine ⟨5787412040004191028040829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15433098773344509408108877 5787412040004191028040829)
          ·
            refine ⟨2170279515001571635515311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5787412040004191028040829 2170279515001571635515311)
            ·
              refine ⟨3255419272502357453272967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170279515001571635515311 3255419272502357453272967)
              ·
                refine ⟨4883128908753536179909451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255419272502357453272967 4883128908753536179909451)
                ·
                  refine ⟨7324693363130304269864177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4883128908753536179909451 7324693363130304269864177)
                  ·
                    refine ⟨5493520022347728202398133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7324693363130304269864177 5493520022347728202398133)
                    ·
                      refine ⟨515017502095099518974825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5493520022347728202398133 515017502095099518974825)
                      ·
                        rfl

theorem cell23_1002993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_1002993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1002993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1002993 prefixEnd_1002993 := by exact prefixLift 1002993
  have htrace : WordTrace (prefixWord ++ tailWord_1002993) baseStart_1002993 baseEnd_1002993 := by
    simpa [prefixWord, tailWord_1002993, baseEnd_1002993] using wordTrace_append hprefix tailTrace_1002993
  have hstable : (prefixWord ++ tailWord_1002993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1002993).length < 2 ^ (prefixWord ++ tailWord_1002993).sum := by decide
  have hdescent : baseEnd_1002993 < baseStart_1002993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1002993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003013 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 5, 4]
def baseStart_1003013 : Nat := 118140960795 + 1003013 * 2 ^ 59
def prefixEnd_1003013 : Nat := 4983230072969 + 3 ^ 40 * 1003013 * 2
def baseEnd_1003013 : Nat := 171675923902729813574911

theorem tailTrace_1003013 : CollatzResearch.WordTrace tailWord_1003013 prefixEnd_1003013 171675923902729813574911 := by
  unfold tailWord_1003013
  simp only [CollatzResearch.WordTrace]
  refine ⟨36582889515262676827541693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24388593010175117885027795 36582889515262676827541693)
  ·
    refine ⟨13718583568223503810328135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36582889515262676827541693 13718583568223503810328135)
    ·
      refine ⟨20577875352335255715492203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13718583568223503810328135 20577875352335255715492203)
      ·
        refine ⟨30866813028502883573238305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20577875352335255715492203 30866813028502883573238305)
        ·
          refine ⟨23150109771377162679928729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30866813028502883573238305 23150109771377162679928729)
          ·
            refine ⟨17362582328532872009946547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23150109771377162679928729 17362582328532872009946547)
            ·
              refine ⟨26043873492799308014919821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17362582328532872009946547 26043873492799308014919821)
              ·
                refine ⟨9766452559799740505594933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26043873492799308014919821 9766452559799740505594933)
                ·
                  refine ⟨915604927481225672399525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9766452559799740505594933 915604927481225672399525)
                  ·
                    refine ⟨171675923902729813574911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 915604927481225672399525 171675923902729813574911)
                    ·
                      rfl

theorem cell23_1003013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 5, 4].length) (baseStart_1003013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003013 prefixEnd_1003013 := by exact prefixLift 1003013
  have htrace : WordTrace (prefixWord ++ tailWord_1003013) baseStart_1003013 baseEnd_1003013 := by
    simpa [prefixWord, tailWord_1003013, baseEnd_1003013] using wordTrace_append hprefix tailTrace_1003013
  have hstable : (prefixWord ++ tailWord_1003013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003013).length < 2 ^ (prefixWord ++ tailWord_1003013).sum := by decide
  have hdescent : baseEnd_1003013 < baseStart_1003013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003094 : List Nat := [5, 2, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1003094 : Nat := 118140960795 + 1003094 * 2 ^ 59
def prefixEnd_1003094 : Nat := 4983230072969 + 3 ^ 40 * 1003094 * 2
def baseEnd_1003094 : Nat := 57229929293467069312429

theorem tailTrace_1003094 : CollatzResearch.WordTrace tailWord_1003094 prefixEnd_1003094 57229929293467069312429 := by
  unfold tailWord_1003094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2286615239248076728827521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24390562551979485107493557 2286615239248076728827521)
  ·
    refine ⟨1714961429436057546620641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2286615239248076728827521 1714961429436057546620641)
    ·
      refine ⟨1286221072077043159965481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1714961429436057546620641 1286221072077043159965481)
      ·
        refine ⟨964665804057782369974111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1286221072077043159965481 964665804057782369974111)
        ·
          refine ⟨1446998706086673554961167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964665804057782369974111 1446998706086673554961167)
          ·
            refine ⟨2170498059130010332441751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446998706086673554961167 2170498059130010332441751)
            ·
              refine ⟨3255747088695015498662627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2170498059130010332441751 3255747088695015498662627)
              ·
                refine ⟨4883620633042523247993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3255747088695015498662627 4883620633042523247993941)
                ·
                  refine ⟨57229929293467069312429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4883620633042523247993941 57229929293467069312429)
                  ·
                    rfl

theorem cell23_1003094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1003094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003094 prefixEnd_1003094 := by exact prefixLift 1003094
  have htrace : WordTrace (prefixWord ++ tailWord_1003094) baseStart_1003094 baseEnd_1003094 := by
    simpa [prefixWord, tailWord_1003094, baseEnd_1003094] using wordTrace_append hprefix tailTrace_1003094
  have hstable : (prefixWord ++ tailWord_1003094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003094).length < 2 ^ (prefixWord ++ tailWord_1003094).sum := by decide
  have hdescent : baseEnd_1003094 < baseStart_1003094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003113 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_1003113 : Nat := 118140960795 + 1003113 * 2 ^ 59
def prefixEnd_1003113 : Nat := 4983230072969 + 3 ^ 40 * 1003113 * 2
def baseEnd_1003113 : Nat := 515079119773639049474273

theorem tailTrace_1003113 : CollatzResearch.WordTrace tailWord_1003113 prefixEnd_1003113 515079119773639049474273 := by
  unfold tailWord_1003113
  simp only [CollatzResearch.WordTrace]
  refine ⟨36586536814900393906181993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24391024543266929270787995 36586536814900393906181993)
  ·
    refine ⟨27439902611175295429636495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36586536814900393906181993 27439902611175295429636495)
    ·
      refine ⟨41159853916762943144454743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27439902611175295429636495 41159853916762943144454743)
      ·
        refine ⟨61739780875144414716682115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41159853916762943144454743 61739780875144414716682115)
        ·
          refine ⟨92609671312716622075023173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61739780875144414716682115 92609671312716622075023173)
          ·
            refine ⟨17364313371134366639066845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92609671312716622075023173 17364313371134366639066845)
            ·
              refine ⟨6511617514175387489650067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17364313371134366639066845 6511617514175387489650067)
              ·
                refine ⟨9767426271263081234475101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6511617514175387489650067 9767426271263081234475101)
                ·
                  refine ⟨3662784851723655462928163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9767426271263081234475101 3662784851723655462928163)
                  ·
                    refine ⟨5494177277585483194392245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3662784851723655462928163 5494177277585483194392245)
                    ·
                      refine ⟨515079119773639049474273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5494177277585483194392245 515079119773639049474273)
                      ·
                        rfl

theorem cell23_1003113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_1003113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003113 prefixEnd_1003113 := by exact prefixLift 1003113
  have htrace : WordTrace (prefixWord ++ tailWord_1003113) baseStart_1003113 baseEnd_1003113 := by
    simpa [prefixWord, tailWord_1003113, baseEnd_1003113] using wordTrace_append hprefix tailTrace_1003113
  have hstable : (prefixWord ++ tailWord_1003113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003113).length < 2 ^ (prefixWord ++ tailWord_1003113).sum := by decide
  have hdescent : baseEnd_1003113 < baseStart_1003113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003120 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 1, 6]
def baseStart_1003120 : Nat := 118140960795 + 1003120 * 2 ^ 59
def prefixEnd_1003120 : Nat := 4983230072969 + 3 ^ 40 * 1003120 * 2
def baseEnd_1003120 : Nat := 171694238046073507362247

theorem tailTrace_1003120 : CollatzResearch.WordTrace tailWord_1003120 prefixEnd_1003120 171694238046073507362247 := by
  unfold tailWord_1003120
  simp only [CollatzResearch.WordTrace]
  refine ⟨18293396062937517050843407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24391194750583356067791209 18293396062937517050843407)
  ·
    refine ⟨27440094094406275576265111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18293396062937517050843407 27440094094406275576265111)
    ·
      refine ⟨41160141141609413364397667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27440094094406275576265111 41160141141609413364397667)
      ·
        refine ⟨61740211712414120046596501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41160141141609413364397667 61740211712414120046596501)
        ·
          refine ⟨2894072424019411877184211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 61740211712414120046596501 2894072424019411877184211)
          ·
            refine ⟨4341108636029117815776317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894072424019411877184211 4341108636029117815776317)
            ·
              refine ⟨1627915738510919180916119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4341108636029117815776317 1627915738510919180916119)
              ·
                refine ⟨2441873607766378771374179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627915738510919180916119 2441873607766378771374179)
                ·
                  refine ⟨3662810411649568157061269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441873607766378771374179 3662810411649568157061269)
                  ·
                    refine ⟨171694238046073507362247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3662810411649568157061269 171694238046073507362247)
                    ·
                      rfl

theorem cell23_1003120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 6].length) (baseStart_1003120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003120 prefixEnd_1003120 := by exact prefixLift 1003120
  have htrace : WordTrace (prefixWord ++ tailWord_1003120) baseStart_1003120 baseEnd_1003120 := by
    simpa [prefixWord, tailWord_1003120, baseEnd_1003120] using wordTrace_append hprefix tailTrace_1003120
  have hstable : (prefixWord ++ tailWord_1003120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003120).length < 2 ^ (prefixWord ++ tailWord_1003120).sum := by decide
  have hdescent : baseEnd_1003120 < baseStart_1003120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003150 : List Nat := [4, 1, 1, 3, 1, 4, 9]
def baseStart_1003150 : Nat := 118140960795 + 1003150 * 2 ^ 59
def prefixEnd_1003150 : Nat := 4983230072969 + 3 ^ 40 * 1003150 * 2
def baseEnd_1003150 : Nat := 6359236031578461786563

theorem tailTrace_1003150 : CollatzResearch.WordTrace tailWord_1003150 prefixEnd_1003150 6359236031578461786563 := by
  unfold tailWord_1003150
  simp only [CollatzResearch.WordTrace]
  refine ⟨4573485789470793653159863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24391924210510899483519269 4573485789470793653159863)
  ·
    refine ⟨6860228684206190479739795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4573485789470793653159863 6860228684206190479739795)
    ·
      refine ⟨10290343026309285719609693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6860228684206190479739795 10290343026309285719609693)
      ·
        refine ⟨3858878634865982144853635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10290343026309285719609693 3858878634865982144853635)
        ·
          refine ⟨5788317952298973217280453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3858878634865982144853635 5788317952298973217280453)
          ·
            refine ⟨1085309616056057478240085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5788317952298973217280453 1085309616056057478240085)
            ·
              refine ⟨6359236031578461786563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1085309616056057478240085 6359236031578461786563)
              ·
                rfl

theorem cell23_1003150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 9].length) (baseStart_1003150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003150 prefixEnd_1003150 := by exact prefixLift 1003150
  have htrace : WordTrace (prefixWord ++ tailWord_1003150) baseStart_1003150 baseEnd_1003150 := by
    simpa [prefixWord, tailWord_1003150, baseEnd_1003150] using wordTrace_append hprefix tailTrace_1003150
  have hstable : (prefixWord ++ tailWord_1003150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003150).length < 2 ^ (prefixWord ++ tailWord_1003150).sum := by decide
  have hdescent : baseEnd_1003150 < baseStart_1003150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003167 : List Nat := [1, 1, 2, 7, 1, 1, 2, 8]
def baseStart_1003167 : Nat := 118140960795 + 1003167 * 2 ^ 59
def prefixEnd_1003167 : Nat := 4983230072969 + 3 ^ 40 * 1003167 * 2
def baseEnd_1003167 : Nat := 19078031397369697711075

theorem tailTrace_1003167 : CollatzResearch.WordTrace tailWord_1003167 prefixEnd_1003167 19078031397369697711075 := by
  unfold tailWord_1003167
  simp only [CollatzResearch.WordTrace]
  refine ⟨36588506356704761128647755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24392337571136507419098503 36588506356704761128647755)
  ·
    refine ⟨54882759535057141692971633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36588506356704761128647755 54882759535057141692971633)
    ·
      refine ⟨41162069651292856269728725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54882759535057141692971633 41162069651292856269728725)
      ·
        refine ⟨964736007452176318821767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41162069651292856269728725 964736007452176318821767)
        ·
          refine ⟨1447104011178264478232651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964736007452176318821767 1447104011178264478232651)
          ·
            refine ⟨2170656016767396717348977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447104011178264478232651 2170656016767396717348977)
            ·
              refine ⟨1627992012575547538011733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2170656016767396717348977 1627992012575547538011733)
              ·
                refine ⟨19078031397369697711075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1627992012575547538011733 19078031397369697711075)
                ·
                  rfl

theorem cell23_1003167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 8].length) (baseStart_1003167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003167 prefixEnd_1003167 := by exact prefixLift 1003167
  have htrace : WordTrace (prefixWord ++ tailWord_1003167) baseStart_1003167 baseEnd_1003167 := by
    simpa [prefixWord, tailWord_1003167, baseEnd_1003167] using wordTrace_append hprefix tailTrace_1003167
  have hstable : (prefixWord ++ tailWord_1003167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003167).length < 2 ^ (prefixWord ++ tailWord_1003167).sum := by decide
  have hdescent : baseEnd_1003167 < baseStart_1003167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003187 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 3, 3, 2]
def baseStart_1003187 : Nat := 118140960795 + 1003187 * 2 ^ 59
def prefixEnd_1003187 : Nat := 4983230072969 + 3 ^ 40 * 1003187 * 2
def baseEnd_1003187 : Nat := 515117117342071759948933

theorem tailTrace_1003187 : CollatzResearch.WordTrace tailWord_1003187 prefixEnd_1003187 515117117342071759948933 := by
  unfold tailWord_1003187
  simp only [CollatzResearch.WordTrace]
  refine ⟨36589235816632304544375815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24392823877754869696250543 36589235816632304544375815)
  ·
    refine ⟨54883853724948456816563723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36589235816632304544375815 54883853724948456816563723)
    ·
      refine ⟨82325780587422685224845585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54883853724948456816563723 82325780587422685224845585)
      ·
        refine ⟨61744335440567013918634189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82325780587422685224845585 61744335440567013918634189)
        ·
          refine ⟨23154125790212630219487821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61744335440567013918634189 23154125790212630219487821)
          ·
            refine ⟨8682797171329736332307933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23154125790212630219487821 8682797171329736332307933)
            ·
              refine ⟨3256048939248651124615475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8682797171329736332307933 3256048939248651124615475)
              ·
                refine ⟨4884073408872976686923213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3256048939248651124615475 4884073408872976686923213)
                ·
                  refine ⟨1831527528327366257596205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4884073408872976686923213 1831527528327366257596205)
                  ·
                    refine ⟨686822823122762346598577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831527528327366257596205 686822823122762346598577)
                    ·
                      refine ⟨515117117342071759948933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686822823122762346598577 515117117342071759948933)
                      ·
                        rfl

theorem cell23_1003187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3, 2].length) (baseStart_1003187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003187 prefixEnd_1003187 := by exact prefixLift 1003187
  have htrace : WordTrace (prefixWord ++ tailWord_1003187) baseStart_1003187 baseEnd_1003187 := by
    simpa [prefixWord, tailWord_1003187, baseEnd_1003187] using wordTrace_append hprefix tailTrace_1003187
  have hstable : (prefixWord ++ tailWord_1003187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003187).length < 2 ^ (prefixWord ++ tailWord_1003187).sum := by decide
  have hdescent : baseEnd_1003187 < baseStart_1003187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003212 : List Nat := [2, 2, 1, 5, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1003212 : Nat := 118140960795 + 1003212 * 2 ^ 59
def prefixEnd_1003212 : Nat := 4983230072969 + 3 ^ 40 * 1003212 * 2
def baseEnd_1003212 : Nat := 515129954358434162136319

theorem tailTrace_1003212 : CollatzResearch.WordTrace tailWord_1003212 prefixEnd_1003212 515129954358434162136319 := by
  unfold tailWord_1003212
  simp only [CollatzResearch.WordTrace]
  refine ⟨18295073820770866907017945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24393431761027822542690593 18295073820770866907017945)
  ·
    refine ⟨13721305365578150180263459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18295073820770866907017945 13721305365578150180263459)
    ·
      refine ⟨20581958048367225270395189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13721305365578150180263459 20581958048367225270395189)
      ·
        refine ⟨1929558567034427369099549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20581958048367225270395189 1929558567034427369099549)
        ·
          refine ⟨723584462637910263412331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1929558567034427369099549 723584462637910263412331)
          ·
            refine ⟨1085376693956865395118497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723584462637910263412331 1085376693956865395118497)
            ·
              refine ⟨814032520467649046338873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085376693956865395118497 814032520467649046338873)
              ·
                refine ⟨610524390350736784754155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814032520467649046338873 610524390350736784754155)
                ·
                  refine ⟨915786585526105177131233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610524390350736784754155 915786585526105177131233)
                  ·
                    refine ⟨686839939144578882848425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 915786585526105177131233 686839939144578882848425)
                    ·
                      refine ⟨515129954358434162136319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686839939144578882848425 515129954358434162136319)
                      ·
                        rfl

theorem cell23_1003212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1003212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003212 prefixEnd_1003212 := by exact prefixLift 1003212
  have htrace : WordTrace (prefixWord ++ tailWord_1003212) baseStart_1003212 baseEnd_1003212 := by
    simpa [prefixWord, tailWord_1003212, baseEnd_1003212] using wordTrace_append hprefix tailTrace_1003212
  have hstable : (prefixWord ++ tailWord_1003212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003212).length < 2 ^ (prefixWord ++ tailWord_1003212).sum := by decide
  have hdescent : baseEnd_1003212 < baseStart_1003212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003240 : List Nat := [2, 1, 4, 1, 3, 1, 1, 1, 9]
def baseStart_1003240 : Nat := 118140960795 + 1003240 * 2 ^ 59
def prefixEnd_1003240 : Nat := 4983230072969 + 3 ^ 40 * 1003240 * 2
def baseEnd_1003240 : Nat := 57238259090751116954021

theorem tailTrace_1003240 : CollatzResearch.WordTrace tailWord_1003240 prefixEnd_1003240 57238259090751116954021 := by
  unfold tailWord_1003240
  simp only [CollatzResearch.WordTrace]
  refine ⟨18295584442720147298027587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24394112590293529730703449 18295584442720147298027587)
  ·
    refine ⟨27443376664080220947041381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18295584442720147298027587 27443376664080220947041381)
    ·
      refine ⟨5145633124515041427570259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27443376664080220947041381 5145633124515041427570259)
      ·
        refine ⟨7718449686772562141355389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5145633124515041427570259 7718449686772562141355389)
        ·
          refine ⟨2894418632539710803008271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7718449686772562141355389 2894418632539710803008271)
          ·
            refine ⟨4341627948809566204512407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894418632539710803008271 4341627948809566204512407)
            ·
              refine ⟨6512441923214349306768611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4341627948809566204512407 6512441923214349306768611)
              ·
                refine ⟨9768662884821523960152917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6512441923214349306768611 9768662884821523960152917)
                ·
                  refine ⟨57238259090751116954021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 9768662884821523960152917 57238259090751116954021)
                  ·
                    rfl

theorem cell23_1003240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 9].length) (baseStart_1003240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003240 prefixEnd_1003240 := by exact prefixLift 1003240
  have htrace : WordTrace (prefixWord ++ tailWord_1003240) baseStart_1003240 baseEnd_1003240 := by
    simpa [prefixWord, tailWord_1003240, baseEnd_1003240] using wordTrace_append hprefix tailTrace_1003240
  have hstable : (prefixWord ++ tailWord_1003240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003240).length < 2 ^ (prefixWord ++ tailWord_1003240).sum := by decide
  have hdescent : baseEnd_1003240 < baseStart_1003240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003268 : List Nat := [2, 3, 2, 2, 1, 4, 1, 2, 2, 2, 2]
def baseStart_1003268 : Nat := 118140960795 + 1003268 * 2 ^ 59
def prefixEnd_1003268 : Nat := 4983230072969 + 3 ^ 40 * 1003268 * 2
def baseEnd_1003268 : Nat := 515158709275085943036061

theorem tailTrace_1003268 : CollatzResearch.WordTrace tailWord_1003268 prefixEnd_1003268 515158709275085943036061 := by
  unfold tailWord_1003268
  simp only [CollatzResearch.WordTrace]
  refine ⟨18296095064669427689037229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24394793419559236918716305 18296095064669427689037229)
  ·
    refine ⟨6861035649251035383388961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18296095064669427689037229 6861035649251035383388961)
    ·
      refine ⟨5145776736938276537541721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6861035649251035383388961 5145776736938276537541721)
      ·
        refine ⟨3859332552703707403156291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5145776736938276537541721 3859332552703707403156291)
        ·
          refine ⟨5788998829055561104734437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3859332552703707403156291 5788998829055561104734437)
          ·
            refine ⟨1085437280447917707137707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5788998829055561104734437 1085437280447917707137707)
            ·
              refine ⟨1628155920671876560706561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085437280447917707137707 1628155920671876560706561)
              ·
                refine ⟨1221116940503907420529921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628155920671876560706561 1221116940503907420529921)
                ·
                  refine ⟨915837705377930565397441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1221116940503907420529921 915837705377930565397441)
                  ·
                    refine ⟨686878279033447924048081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 915837705377930565397441 686878279033447924048081)
                    ·
                      refine ⟨515158709275085943036061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686878279033447924048081 515158709275085943036061)
                      ·
                        rfl

theorem cell23_1003268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_1003268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003268 prefixEnd_1003268 := by exact prefixLift 1003268
  have htrace : WordTrace (prefixWord ++ tailWord_1003268) baseStart_1003268 baseEnd_1003268 := by
    simpa [prefixWord, tailWord_1003268, baseEnd_1003268] using wordTrace_append hprefix tailTrace_1003268
  have hstable : (prefixWord ++ tailWord_1003268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003268).length < 2 ^ (prefixWord ++ tailWord_1003268).sum := by decide
  have hdescent : baseEnd_1003268 < baseStart_1003268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003397 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 4]
def baseStart_1003397 : Nat := 118140960795 + 1003397 * 2 ^ 59
def prefixEnd_1003397 : Nat := 4983230072969 + 3 ^ 40 * 1003397 * 2
def baseEnd_1003397 : Nat := 515224948279515938322967

theorem tailTrace_1003397 : CollatzResearch.WordTrace tailWord_1003397 prefixEnd_1003397 515224948279515938322967 := by
  unfold tailWord_1003397
  simp only [CollatzResearch.WordTrace]
  refine ⟨36596895145871510409520445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24397930097247673606346963 36596895145871510409520445)
  ·
    refine ⟨13723835679701816403570167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36596895145871510409520445 13723835679701816403570167)
    ·
      refine ⟨20585753519552724605355251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13723835679701816403570167 20585753519552724605355251)
      ·
        refine ⟨30878630279329086908032877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20585753519552724605355251 30878630279329086908032877)
        ·
          refine ⟨11579486354748407590512329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30878630279329086908032877 11579486354748407590512329)
          ·
            refine ⟨8684614766061305692884247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11579486354748407590512329 8684614766061305692884247)
            ·
              refine ⟨13026922149091958539326371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8684614766061305692884247 13026922149091958539326371)
              ·
                refine ⟨19540383223637937808989557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13026922149091958539326371 19540383223637937808989557)
                ·
                  refine ⟨1831910927216056669592771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 19540383223637937808989557 1831910927216056669592771)
                  ·
                    refine ⟨2747866390824085004389157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831910927216056669592771 2747866390824085004389157)
                    ·
                      refine ⟨515224948279515938322967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2747866390824085004389157 515224948279515938322967)
                      ·
                        rfl

theorem cell23_1003397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_1003397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003397 prefixEnd_1003397 := by exact prefixLift 1003397
  have htrace : WordTrace (prefixWord ++ tailWord_1003397) baseStart_1003397 baseEnd_1003397 := by
    simpa [prefixWord, tailWord_1003397, baseEnd_1003397] using wordTrace_append hprefix tailTrace_1003397
  have hstable : (prefixWord ++ tailWord_1003397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003397).length < 2 ^ (prefixWord ++ tailWord_1003397).sum := by decide
  have hdescent : baseEnd_1003397 < baseStart_1003397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003418 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2]
def baseStart_1003418 : Nat := 118140960795 + 1003418 * 2 ^ 59
def prefixEnd_1003418 : Nat := 4983230072969 + 3 ^ 40 * 1003418 * 2
def baseEnd_1003418 : Nat := 515235731373260356160371

theorem tailTrace_1003418 : CollatzResearch.WordTrace tailWord_1003418 prefixEnd_1003418 515235731373260356160371 := by
  unfold tailWord_1003418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149415269698857749008727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24398440719196953997356605 9149415269698857749008727)
  ·
    refine ⟨13724122904548286623513091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149415269698857749008727 13724122904548286623513091)
    ·
      refine ⟨20586184356822429935269637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13724122904548286623513091 20586184356822429935269637)
      ·
        refine ⟨3859909566904205612863057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20586184356822429935269637 3859909566904205612863057)
        ·
          refine ⟨2894932175178154209647293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3859909566904205612863057 2894932175178154209647293)
          ·
            refine ⟨1085599565691807828617735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2894932175178154209647293 1085599565691807828617735)
            ·
              refine ⟨1628399348537711742926603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085599565691807828617735 1628399348537711742926603)
              ·
                refine ⟨2442599022806567614389905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628399348537711742926603 2442599022806567614389905)
                ·
                  refine ⟨1831949267104925710792429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2442599022806567614389905 1831949267104925710792429)
                  ·
                    refine ⟨686980975164347141547161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1831949267104925710792429 686980975164347141547161)
                    ·
                      refine ⟨515235731373260356160371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 686980975164347141547161 515235731373260356160371)
                      ·
                        rfl

theorem cell23_1003418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_1003418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003418 prefixEnd_1003418 := by exact prefixLift 1003418
  have htrace : WordTrace (prefixWord ++ tailWord_1003418) baseStart_1003418 baseEnd_1003418 := by
    simpa [prefixWord, tailWord_1003418, baseEnd_1003418] using wordTrace_append hprefix tailTrace_1003418
  have hstable : (prefixWord ++ tailWord_1003418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003418).length < 2 ^ (prefixWord ++ tailWord_1003418).sum := by decide
  have hdescent : baseEnd_1003418 < baseStart_1003418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003425 : List Nat := [1, 2, 3, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1003425 : Nat := 118140960795 + 1003425 * 2 ^ 59
def prefixEnd_1003425 : Nat := 4983230072969 + 3 ^ 40 * 1003425 * 2
def baseEnd_1003425 : Nat := 515239325737841828772839

theorem tailTrace_1003425 : CollatzResearch.WordTrace tailWord_1003425 prefixEnd_1003425 515239325737841828772839 := by
  unfold tailWord_1003425
  simp only [CollatzResearch.WordTrace]
  refine ⟨36597916389770071191539729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24398610926513380794359819 36597916389770071191539729)
  ·
    refine ⟨27448437292327553393654797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36597916389770071191539729 27448437292327553393654797)
    ·
      refine ⟨10293163984622832522620549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27448437292327553393654797 10293163984622832522620549)
      ·
        refine ⟨1929968247116781097991353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10293163984622832522620549 1929968247116781097991353)
        ·
          refine ⟨1447476185337585823493515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1929968247116781097991353 1447476185337585823493515)
          ·
            refine ⟨2171214278006378735240273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447476185337585823493515 2171214278006378735240273)
            ·
              refine ⟨1628410708504784051430205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2171214278006378735240273 1628410708504784051430205)
              ·
                refine ⟨610654015689294019286327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628410708504784051430205 610654015689294019286327)
                ·
                  refine ⟨915981023533941028929491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610654015689294019286327 915981023533941028929491)
                  ·
                    refine ⟨1373971535300911543394237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 915981023533941028929491 1373971535300911543394237)
                    ·
                      refine ⟨515239325737841828772839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1373971535300911543394237 515239325737841828772839)
                      ·
                        rfl

theorem cell23_1003425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1003425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003425 prefixEnd_1003425 := by exact prefixLift 1003425
  have htrace : WordTrace (prefixWord ++ tailWord_1003425) baseStart_1003425 baseEnd_1003425 := by
    simpa [prefixWord, tailWord_1003425, baseEnd_1003425] using wordTrace_append hprefix tailTrace_1003425
  have hstable : (prefixWord ++ tailWord_1003425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003425).length < 2 ^ (prefixWord ++ tailWord_1003425).sum := by decide
  have hdescent : baseEnd_1003425 < baseStart_1003425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003431 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1003431 : Nat := 118140960795 + 1003431 * 2 ^ 59
def prefixEnd_1003431 : Nat := 4983230072969 + 3 ^ 40 * 1003431 * 2
def baseEnd_1003431 : Nat := 515242406621768805297811

theorem tailTrace_1003431 : CollatzResearch.WordTrace tailWord_1003431 prefixEnd_1003431 515242406621768805297811 := by
  unfold tailWord_1003431
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598135227748334216258147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24398756818498889477505431 36598135227748334216258147)
  ·
    refine ⟨54897202841622501324387221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36598135227748334216258147 54897202841622501324387221)
    ·
      refine ⟨2573306383201054749580651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54897202841622501324387221 2573306383201054749580651)
      ·
        refine ⟨3859959574801582124370977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2573306383201054749580651 3859959574801582124370977)
        ·
          refine ⟨2894969681101186593278233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3859959574801582124370977 2894969681101186593278233)
          ·
            refine ⟨2171227260825889944958675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2894969681101186593278233 2171227260825889944958675)
            ·
              refine ⟨3256840891238834917438013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171227260825889944958675 3256840891238834917438013)
              ·
                refine ⟨1221315334214563094039255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3256840891238834917438013 1221315334214563094039255)
                ·
                  refine ⟨1831973001321844641058883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221315334214563094039255 1831973001321844641058883)
                  ·
                    refine ⟨2747959501982766961588325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1831973001321844641058883 2747959501982766961588325)
                    ·
                      refine ⟨515242406621768805297811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2747959501982766961588325 515242406621768805297811)
                      ·
                        rfl

theorem cell23_1003431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1003431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003431 prefixEnd_1003431 := by exact prefixLift 1003431
  have htrace : WordTrace (prefixWord ++ tailWord_1003431) baseStart_1003431 baseEnd_1003431 := by
    simpa [prefixWord, tailWord_1003431, baseEnd_1003431] using wordTrace_append hprefix tailTrace_1003431
  have hstable : (prefixWord ++ tailWord_1003431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003431).length < 2 ^ (prefixWord ++ tailWord_1003431).sum := by decide
  have hdescent : baseEnd_1003431 < baseStart_1003431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003441 : List Nat := [1, 2, 2, 4, 2, 1, 3, 2, 2, 4]
def baseStart_1003441 : Nat := 118140960795 + 1003441 * 2 ^ 59
def prefixEnd_1003441 : Nat := 4983230072969 + 3 ^ 40 * 1003441 * 2
def baseEnd_1003441 : Nat := 171749180476104588724255

theorem tailTrace_1003441 : CollatzResearch.WordTrace tailWord_1003441 prefixEnd_1003441 171749180476104588724255 := by
  unfold tailWord_1003441
  simp only [CollatzResearch.WordTrace]
  refine ⟨36598499957712105924122177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24398999971808070616081451 36598499957712105924122177)
  ·
    refine ⟨27448874968284079443091633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36598499957712105924122177 27448874968284079443091633)
    ·
      refine ⟨20586656226213059582318725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27448874968284079443091633 20586656226213059582318725)
      ·
        refine ⟨3859998042414948671684761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20586656226213059582318725 3859998042414948671684761)
        ·
          refine ⟨2894998531811211503763571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3859998042414948671684761 2894998531811211503763571)
          ·
            refine ⟨4342497797716817255645357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2894998531811211503763571 4342497797716817255645357)
            ·
              refine ⟨1628436674143806470867009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4342497797716817255645357 1628436674143806470867009)
              ·
                refine ⟨1221327505607854853150257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628436674143806470867009 1221327505607854853150257)
                ·
                  refine ⟨915995629205891139862693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1221327505607854853150257 915995629205891139862693)
                  ·
                    refine ⟨171749180476104588724255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 915995629205891139862693 171749180476104588724255)
                    ·
                      rfl

theorem cell23_1003441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_1003441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003441 prefixEnd_1003441 := by exact prefixLift 1003441
  have htrace : WordTrace (prefixWord ++ tailWord_1003441) baseStart_1003441 baseEnd_1003441 := by
    simpa [prefixWord, tailWord_1003441, baseEnd_1003441] using wordTrace_append hprefix tailTrace_1003441
  have hstable : (prefixWord ++ tailWord_1003441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003441).length < 2 ^ (prefixWord ++ tailWord_1003441).sum := by decide
  have hdescent : baseEnd_1003441 < baseStart_1003441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003448 : List Nat := [2, 1, 2, 1, 2, 3, 1, 6, 1, 2, 2]
def baseStart_1003448 : Nat := 118140960795 + 1003448 * 2 ^ 59
def prefixEnd_1003448 : Nat := 4983230072969 + 3 ^ 40 * 1003448 * 2
def baseEnd_1003448 : Nat := 515251135792895238785233

theorem tailTrace_1003448 : CollatzResearch.WordTrace tailWord_1003448 prefixEnd_1003448 515251135792895238785233 := by
  unfold tailWord_1003448
  simp only [CollatzResearch.WordTrace]
  refine ⟨18299377634343373059813499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24399170179124497413084665 18299377634343373059813499)
  ·
    refine ⟨27449066451515059589720249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18299377634343373059813499 27449066451515059589720249)
    ·
      refine ⟨20586799838636294692290187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27449066451515059589720249 20586799838636294692290187)
      ·
        refine ⟨30880199757954442038435281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20586799838636294692290187 30880199757954442038435281)
        ·
          refine ⟨23160149818465831528826461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30880199757954442038435281 23160149818465831528826461)
          ·
            refine ⟨8685056181924686823309923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23160149818465831528826461 8685056181924686823309923)
            ·
              refine ⟨13027584272887030234964885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8685056181924686823309923 13027584272887030234964885)
              ·
                refine ⟨610668012791579542263979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13027584272887030234964885 610668012791579542263979)
                ·
                  refine ⟨916002019187369313395969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610668012791579542263979 916002019187369313395969)
                  ·
                    refine ⟨687001514390526985046977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 916002019187369313395969 687001514390526985046977)
                    ·
                      refine ⟨515251135792895238785233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687001514390526985046977 515251135792895238785233)
                      ·
                        rfl

theorem cell23_1003448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_1003448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003448 prefixEnd_1003448 := by exact prefixLift 1003448
  have htrace : WordTrace (prefixWord ++ tailWord_1003448) baseStart_1003448 baseEnd_1003448 := by
    simpa [prefixWord, tailWord_1003448, baseEnd_1003448] using wordTrace_append hprefix tailTrace_1003448
  have hstable : (prefixWord ++ tailWord_1003448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003448).length < 2 ^ (prefixWord ++ tailWord_1003448).sum := by decide
  have hdescent : baseEnd_1003448 < baseStart_1003448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003482 : List Nat := [3, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2]
def baseStart_1003482 : Nat := 118140960795 + 1003482 * 2 ^ 59
def prefixEnd_1003482 : Nat := 4983230072969 + 3 ^ 40 * 1003482 * 2
def baseEnd_1003482 : Nat := 515268594135148105760077

theorem tailTrace_1003482 : CollatzResearch.WordTrace tailWord_1003482 prefixEnd_1003482 515268594135148105760077 := by
  unfold tailWord_1003482
  simp only [CollatzResearch.WordTrace]
  refine ⟨9149998837640892481591175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24399996900375713284243133 9149998837640892481591175)
  ·
    refine ⟨13724998256461338722386763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9149998837640892481591175 13724998256461338722386763)
    ·
      refine ⟨20587497384692008083580145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13724998256461338722386763 20587497384692008083580145)
      ·
        refine ⟨15440623038519006062685109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20587497384692008083580145 15440623038519006062685109)
        ·
          refine ⟨1447558409861156818376729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15440623038519006062685109 1447558409861156818376729)
          ·
            refine ⟨1085668807395867613782547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1447558409861156818376729 1085668807395867613782547)
            ·
              refine ⟨1628503211093801420673821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085668807395867613782547 1628503211093801420673821)
              ·
                refine ⟨610688704160175532752683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1628503211093801420673821 610688704160175532752683)
                ·
                  refine ⟨916033056240263299129025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610688704160175532752683 916033056240263299129025)
                  ·
                    refine ⟨687024792180197474346769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 916033056240263299129025 687024792180197474346769)
                    ·
                      refine ⟨515268594135148105760077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687024792180197474346769 515268594135148105760077)
                      ·
                        rfl

theorem cell23_1003482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_1003482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003482 prefixEnd_1003482 := by exact prefixLift 1003482
  have htrace : WordTrace (prefixWord ++ tailWord_1003482) baseStart_1003482 baseEnd_1003482 := by
    simpa [prefixWord, tailWord_1003482, baseEnd_1003482] using wordTrace_append hprefix tailTrace_1003482
  have hstable : (prefixWord ++ tailWord_1003482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003482).length < 2 ^ (prefixWord ++ tailWord_1003482).sum := by decide
  have hdescent : baseEnd_1003482 < baseStart_1003482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003521 : List Nat := [1, 2, 4, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_1003521 : Nat := 118140960795 + 1003521 * 2 ^ 59
def prefixEnd_1003521 : Nat := 4983230072969 + 3 ^ 40 * 1003521 * 2
def baseEnd_1003521 : Nat := 515288619880673453172397

theorem tailTrace_1003521 : CollatzResearch.WordTrace tailWord_1003521 prefixEnd_1003521 515288619880673453172397 := by
  unfold tailWord_1003521
  simp only [CollatzResearch.WordTrace]
  refine ⟨36601417797422279587034417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24400945198281519724689611 36601417797422279587034417)
  ·
    refine ⟨27451063348066709690275813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36601417797422279587034417 27451063348066709690275813)
    ·
      refine ⟨5147074377762508066926715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27451063348066709690275813 5147074377762508066926715)
      ·
        refine ⟨7720611566643762100390073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5147074377762508066926715 7720611566643762100390073)
        ·
          refine ⟨5790458674982821575292555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7720611566643762100390073 5790458674982821575292555)
          ·
            refine ⟨8685688012474232362938833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790458674982821575292555 8685688012474232362938833)
            ·
              refine ⟨6514266009355674272204125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8685688012474232362938833 6514266009355674272204125)
              ·
                refine ⟨2442849753508377852076547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6514266009355674272204125 2442849753508377852076547)
                ·
                  refine ⟨3664274630262566778114821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2442849753508377852076547 3664274630262566778114821)
                  ·
                    refine ⟨687051493174231270896529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3664274630262566778114821 687051493174231270896529)
                    ·
                      refine ⟨515288619880673453172397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687051493174231270896529 515288619880673453172397)
                      ·
                        rfl

theorem cell23_1003521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_1003521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003521 prefixEnd_1003521 := by exact prefixLift 1003521
  have htrace : WordTrace (prefixWord ++ tailWord_1003521) baseStart_1003521 baseEnd_1003521 := by
    simpa [prefixWord, tailWord_1003521, baseEnd_1003521] using wordTrace_append hprefix tailTrace_1003521
  have hstable : (prefixWord ++ tailWord_1003521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003521).length < 2 ^ (prefixWord ++ tailWord_1003521).sum := by decide
  have hdescent : baseEnd_1003521 < baseStart_1003521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003567 : List Nat := [1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 7]
def baseStart_1003567 : Nat := 118140960795 + 1003567 * 2 ^ 59
def prefixEnd_1003567 : Nat := 4983230072969 + 3 ^ 40 * 1003567 * 2
def baseEnd_1003567 : Nat := 515312239990780273197185

theorem tailTrace_1003567 : CollatzResearch.WordTrace tailWord_1003567 prefixEnd_1003567 515312239990780273197185 := by
  unfold tailWord_1003567
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603095555255629443208955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24402063703503752962139303 36603095555255629443208955)
  ·
    refine ⟨54904643332883444164813433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36603095555255629443208955 54904643332883444164813433)
    ·
      refine ⟨41178482499662583123610075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54904643332883444164813433 41178482499662583123610075)
      ·
        refine ⟨61767723749493874685415113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41178482499662583123610075 61767723749493874685415113)
        ·
          refine ⟨46325792812120406014061335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61767723749493874685415113 46325792812120406014061335)
          ·
            refine ⟨69488689218180609021092003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46325792812120406014061335 69488689218180609021092003)
            ·
              refine ⟨104233033827270913531638005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69488689218180609021092003 104233033827270913531638005)
              ·
                refine ⟨9771846921306648143591063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104233033827270913531638005 9771846921306648143591063)
                ·
                  refine ⟨14657770381959972215386595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9771846921306648143591063 14657770381959972215386595)
                  ·
                    refine ⟨21986655572939958323079893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14657770381959972215386595 21986655572939958323079893)
                    ·
                      refine ⟨515312239990780273197185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 21986655572939958323079893 515312239990780273197185)
                      ·
                        rfl

theorem cell23_1003567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 7].length) (baseStart_1003567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003567 prefixEnd_1003567 := by exact prefixLift 1003567
  have htrace : WordTrace (prefixWord ++ tailWord_1003567) baseStart_1003567 baseEnd_1003567 := by
    simpa [prefixWord, tailWord_1003567, baseEnd_1003567] using wordTrace_append hprefix tailTrace_1003567
  have hstable : (prefixWord ++ tailWord_1003567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003567).length < 2 ^ (prefixWord ++ tailWord_1003567).sum := by decide
  have hdescent : baseEnd_1003567 < baseStart_1003567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003581 : List Nat := [1, 4, 1, 3, 1, 1, 1, 2, 2, 5, 2]
def baseStart_1003581 : Nat := 118140960795 + 1003581 * 2 ^ 59
def prefixEnd_1003581 : Nat := 4983230072969 + 3 ^ 40 * 1003581 * 2
def baseEnd_1003581 : Nat := 515319428719943218422121

theorem tailTrace_1003581 : CollatzResearch.WordTrace tailWord_1003581 prefixEnd_1003581 515319428719943218422121 := by
  unfold tailWord_1003581
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603606177204909834218597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24402404118136606556145731 36603606177204909834218597)
  ·
    refine ⟨6863176158225920593915987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36603606177204909834218597 6863176158225920593915987)
    ·
      refine ⟨10294764237338880890873981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6863176158225920593915987 10294764237338880890873981)
      ·
        refine ⟨3860536589002080334077743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10294764237338880890873981 3860536589002080334077743)
        ·
          refine ⟨5790804883503120501116615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860536589002080334077743 5790804883503120501116615)
          ·
            refine ⟨8686207325254680751674923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5790804883503120501116615 8686207325254680751674923)
            ·
              refine ⟨13029310987882021127512385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8686207325254680751674923 13029310987882021127512385)
              ·
                refine ⟨9771983240911515845634289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13029310987882021127512385 9771983240911515845634289)
                ·
                  refine ⟨7328987430683636884225717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9771983240911515845634289 7328987430683636884225717)
                  ·
                    refine ⟨687092571626590957896161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7328987430683636884225717 687092571626590957896161)
                    ·
                      refine ⟨515319428719943218422121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687092571626590957896161 515319428719943218422121)
                      ·
                        rfl

theorem cell23_1003581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_1003581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003581 prefixEnd_1003581 := by exact prefixLift 1003581
  have htrace : WordTrace (prefixWord ++ tailWord_1003581) baseStart_1003581 baseEnd_1003581 := by
    simpa [prefixWord, tailWord_1003581, baseEnd_1003581] using wordTrace_append hprefix tailTrace_1003581
  have hstable : (prefixWord ++ tailWord_1003581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003581).length < 2 ^ (prefixWord ++ tailWord_1003581).sum := by decide
  have hdescent : baseEnd_1003581 < baseStart_1003581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003587 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 10]
def baseStart_1003587 : Nat := 118140960795 + 1003587 * 2 ^ 59
def prefixEnd_1003587 : Nat := 4983230072969 + 3 ^ 40 * 1003587 * 2
def baseEnd_1003587 : Nat := 171774169867956731649031

theorem tailTrace_1003587 : CollatzResearch.WordTrace tailWord_1003587 prefixEnd_1003587 171774169867956731649031 := by
  unfold tailWord_1003587
  simp only [CollatzResearch.WordTrace]
  refine ⟨36603825015183172858937015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24402550010122115239291343 36603825015183172858937015)
  ·
    refine ⟨54905737522774759288405523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36603825015183172858937015 54905737522774759288405523)
    ·
      refine ⟨82358606284162138932608285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54905737522774759288405523 82358606284162138932608285)
      ·
        refine ⟨30884477356560802099728107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82358606284162138932608285 30884477356560802099728107)
        ·
          refine ⟨46326716034841203149592161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30884477356560802099728107 46326716034841203149592161)
          ·
            refine ⟨34745037026130902362194121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46326716034841203149592161 34745037026130902362194121)
            ·
              refine ⟨26058777769598176771645591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34745037026130902362194121 26058777769598176771645591)
              ·
                refine ⟨39088166654397265157468387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26058777769598176771645591 39088166654397265157468387)
                ·
                  refine ⟨58632249981595897736202581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39088166654397265157468387 58632249981595897736202581)
                  ·
                    refine ⟨171774169867956731649031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 58632249981595897736202581 171774169867956731649031)
                    ·
                      rfl

theorem cell23_1003587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 10].length) (baseStart_1003587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003587 prefixEnd_1003587 := by exact prefixLift 1003587
  have htrace : WordTrace (prefixWord ++ tailWord_1003587) baseStart_1003587 baseEnd_1003587 := by
    simpa [prefixWord, tailWord_1003587, baseEnd_1003587] using wordTrace_append hprefix tailTrace_1003587
  have hstable : (prefixWord ++ tailWord_1003587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003587).length < 2 ^ (prefixWord ++ tailWord_1003587).sum := by decide
  have hdescent : baseEnd_1003587 < baseStart_1003587 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003621 : List Nat := [1, 3, 1, 3, 2, 2, 1, 3, 3, 4]
def baseStart_1003621 : Nat := 118140960795 + 1003621 * 2 ^ 59
def prefixEnd_1003621 : Nat := 4983230072969 + 3 ^ 40 * 1003621 * 2
def baseEnd_1003621 : Nat := 171779989315374353973979

theorem tailTrace_1003621 : CollatzResearch.WordTrace tailWord_1003621 prefixEnd_1003621 171779989315374353973979 := by
  unfold tailWord_1003621
  simp only [CollatzResearch.WordTrace]
  refine ⟨36605065097059996665674717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24403376731373331110449811 36605065097059996665674717)
  ·
    refine ⟨13726899411397498749628019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36605065097059996665674717 13726899411397498749628019)
    ·
      refine ⟨20590349117096248124442029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13726899411397498749628019 20590349117096248124442029)
      ·
        refine ⟨7721380918911093046665761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20590349117096248124442029 7721380918911093046665761)
        ·
          refine ⟨5791035689183319784999321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7721380918911093046665761 5791035689183319784999321)
          ·
            refine ⟨4343276766887489838749491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5791035689183319784999321 4343276766887489838749491)
            ·
              refine ⟨6514915150331234758124237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4343276766887489838749491 6514915150331234758124237)
              ·
                refine ⟨2443093181374213034296589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6514915150331234758124237 2443093181374213034296589)
                ·
                  refine ⟨916159943015329887861221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2443093181374213034296589 916159943015329887861221)
                  ·
                    refine ⟨171779989315374353973979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916159943015329887861221 171779989315374353973979)
                    ·
                      rfl

theorem cell23_1003621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 3, 3, 4].length) (baseStart_1003621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003621 prefixEnd_1003621 := by exact prefixLift 1003621
  have htrace : WordTrace (prefixWord ++ tailWord_1003621) baseStart_1003621 baseEnd_1003621 := by
    simpa [prefixWord, tailWord_1003621, baseEnd_1003621] using wordTrace_append hprefix tailTrace_1003621
  have hstable : (prefixWord ++ tailWord_1003621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003621).length < 2 ^ (prefixWord ++ tailWord_1003621).sum := by decide
  have hdescent : baseEnd_1003621 < baseStart_1003621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003638 : List Nat := [5, 1, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_1003638 : Nat := 118140960795 + 1003638 * 2 ^ 59
def prefixEnd_1003638 : Nat := 4983230072969 + 3 ^ 40 * 1003638 * 2
def baseEnd_1003638 : Nat := 171782899039083165136453

theorem tailTrace_1003638 : CollatzResearch.WordTrace tailWord_1003638 prefixEnd_1003638 171782899039083165136453 := by
  unfold tailWord_1003638
  simp only [CollatzResearch.WordTrace]
  refine ⟨2287855321124900535565223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24403790091998939046029045 2287855321124900535565223)
  ·
    refine ⟨3431782981687350803347835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2287855321124900535565223 3431782981687350803347835)
    ·
      refine ⟨5147674472531026205021753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3431782981687350803347835 5147674472531026205021753)
      ·
        refine ⟨3860755854398269653766315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5147674472531026205021753 3860755854398269653766315)
        ·
          refine ⟨5791133781597404480649473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3860755854398269653766315 5791133781597404480649473)
          ·
            refine ⟨4343350336198053360487105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5791133781597404480649473 4343350336198053360487105)
            ·
              refine ⟨3257512752148540020365329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4343350336198053360487105 3257512752148540020365329)
              ·
                refine ⟨2443134564111405015273997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3257512752148540020365329 2443134564111405015273997)
                ·
                  refine ⟨916175461541776880727749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2443134564111405015273997 916175461541776880727749)
                  ·
                    refine ⟨171782899039083165136453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916175461541776880727749 171782899039083165136453)
                    ·
                      rfl

theorem cell23_1003638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_1003638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003638 prefixEnd_1003638 := by exact prefixLift 1003638
  have htrace : WordTrace (prefixWord ++ tailWord_1003638) baseStart_1003638 baseEnd_1003638 := by
    simpa [prefixWord, tailWord_1003638, baseEnd_1003638] using wordTrace_append hprefix tailTrace_1003638
  have hstable : (prefixWord ++ tailWord_1003638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003638).length < 2 ^ (prefixWord ++ tailWord_1003638).sum := by decide
  have hdescent : baseEnd_1003638 < baseStart_1003638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003672 : List Nat := [2, 1, 2, 4, 3, 1, 3, 2, 1, 4]
def baseStart_1003672 : Nat := 118140960795 + 1003672 * 2 ^ 59
def prefixEnd_1003672 : Nat := 4983230072969 + 3 ^ 40 * 1003672 * 2
def baseEnd_1003672 : Nat := 171788718486500787461401

theorem tailTrace_1003672 : CollatzResearch.WordTrace tailWord_1003672 prefixEnd_1003672 171788718486500787461401 := by
  unfold tailWord_1003672
  simp only [CollatzResearch.WordTrace]
  refine ⟨18303462609937616187890635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24404616813250154917187513 18303462609937616187890635)
  ·
    refine ⟨27455193914906424281835953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18303462609937616187890635 27455193914906424281835953)
    ·
      refine ⟨20591395436179818211376965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27455193914906424281835953 20591395436179818211376965)
      ·
        refine ⟨3860886644283715914633181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20591395436179818211376965 3860886644283715914633181)
        ·
          refine ⟨1447832491606393467987443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3860886644283715914633181 1447832491606393467987443)
          ·
            refine ⟨2171748737409590201981165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447832491606393467987443 2171748737409590201981165)
            ·
              refine ⟨814405776528596325742937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2171748737409590201981165 814405776528596325742937)
              ·
                refine ⟨610804332396447244307203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814405776528596325742937 610804332396447244307203)
                ·
                  refine ⟨916206498594670866460805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610804332396447244307203 916206498594670866460805)
                  ·
                    refine ⟨171788718486500787461401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916206498594670866460805 171788718486500787461401)
                    ·
                      rfl

theorem cell23_1003672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 3, 2, 1, 4].length) (baseStart_1003672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003672 prefixEnd_1003672 := by exact prefixLift 1003672
  have htrace : WordTrace (prefixWord ++ tailWord_1003672) baseStart_1003672 baseEnd_1003672 := by
    simpa [prefixWord, tailWord_1003672, baseEnd_1003672] using wordTrace_append hprefix tailTrace_1003672
  have hstable : (prefixWord ++ tailWord_1003672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003672).length < 2 ^ (prefixWord ++ tailWord_1003672).sum := by decide
  have hdescent : baseEnd_1003672 < baseStart_1003672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003772 : List Nat := [2, 2, 2, 1, 4, 3, 2, 1, 1, 2, 3]
def baseStart_1003772 : Nat := 118140960795 + 1003772 * 2 ^ 59
def prefixEnd_1003772 : Nat := 4983230072969 + 3 ^ 40 * 1003772 * 2
def baseEnd_1003772 : Nat := 515417503524951971133743

theorem tailTrace_1003772 : CollatzResearch.WordTrace tailWord_1003772 prefixEnd_1003772 515417503524951971133743 := by
  unfold tailWord_1003772
  simp only [CollatzResearch.WordTrace]
  refine ⟨18305286259756474727210785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24407048346341966302947713 18305286259756474727210785)
  ·
    refine ⟨13728964694817356045408089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18305286259756474727210785 13728964694817356045408089)
    ·
      refine ⟨10296723521113017034056067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13728964694817356045408089 10296723521113017034056067)
      ·
        refine ⟨15445085281669525551084101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10296723521113017034056067 15445085281669525551084101)
        ·
          refine ⟨2895953490313036040828269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15445085281669525551084101 2895953490313036040828269)
          ·
            refine ⟨1085982558867388515310601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2895953490313036040828269 1085982558867388515310601)
            ·
              refine ⟨814486919150541386482951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085982558867388515310601 814486919150541386482951)
              ·
                refine ⟨1221730378725812079724427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814486919150541386482951 1221730378725812079724427)
                ·
                  refine ⟨1832595568088718119586641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221730378725812079724427 1832595568088718119586641)
                  ·
                    refine ⟨1374446676066538589689981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1832595568088718119586641 1374446676066538589689981)
                    ·
                      refine ⟨515417503524951971133743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1374446676066538589689981 515417503524951971133743)
                      ·
                        rfl

theorem cell23_1003772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_1003772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003772 prefixEnd_1003772 := by exact prefixLift 1003772
  have htrace : WordTrace (prefixWord ++ tailWord_1003772) baseStart_1003772 baseEnd_1003772 := by
    simpa [prefixWord, tailWord_1003772, baseEnd_1003772] using wordTrace_append hprefix tailTrace_1003772
  have hstable : (prefixWord ++ tailWord_1003772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003772).length < 2 ^ (prefixWord ++ tailWord_1003772).sum := by decide
  have hdescent : baseEnd_1003772 < baseStart_1003772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003785 : List Nat := [1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 3]
def baseStart_1003785 : Nat := 118140960795 + 1003785 * 2 ^ 59
def prefixEnd_1003785 : Nat := 4983230072969 + 3 ^ 40 * 1003785 * 2
def baseEnd_1003785 : Nat := 515424178773460420271183

theorem tailTrace_1003785 : CollatzResearch.WordTrace tailWord_1003785 prefixEnd_1003785 515424178773460420271183 := by
  unfold tailWord_1003785
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611046668465852674644809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24407364445643901783096539 36611046668465852674644809)
  ·
    refine ⟨27458285001349389505983607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36611046668465852674644809 27458285001349389505983607)
    ·
      refine ⟨41187427502024084258975411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27458285001349389505983607 41187427502024084258975411)
      ·
        refine ⟨61781141253036126388463117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41187427502024084258975411 61781141253036126388463117)
        ·
          refine ⟨23167927969888547395673669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61781141253036126388463117 23167927969888547395673669)
          ·
            refine ⟨4343986494354102636688813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23167927969888547395673669 4343986494354102636688813)
            ·
              refine ⟨1628994935382788488758305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4343986494354102636688813 1628994935382788488758305)
              ·
                refine ⟨1221746201537091366568729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1628994935382788488758305 1221746201537091366568729)
                ·
                  refine ⟨916309651152818524926547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1221746201537091366568729 916309651152818524926547)
                  ·
                    refine ⟨1374464476729227787389821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 916309651152818524926547 1374464476729227787389821)
                    ·
                      refine ⟨515424178773460420271183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1374464476729227787389821 515424178773460420271183)
                      ·
                        rfl

theorem cell23_1003785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_1003785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003785 prefixEnd_1003785 := by exact prefixLift 1003785
  have htrace : WordTrace (prefixWord ++ tailWord_1003785) baseStart_1003785 baseEnd_1003785 := by
    simpa [prefixWord, tailWord_1003785, baseEnd_1003785] using wordTrace_append hprefix tailTrace_1003785
  have hstable : (prefixWord ++ tailWord_1003785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003785).length < 2 ^ (prefixWord ++ tailWord_1003785).sum := by decide
  have hdescent : baseEnd_1003785 < baseStart_1003785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003802 : List Nat := [3, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3]
def baseStart_1003802 : Nat := 118140960795 + 1003802 * 2 ^ 59
def prefixEnd_1003802 : Nat := 4983230072969 + 3 ^ 40 * 1003802 * 2
def baseEnd_1003802 : Nat := 515432907944586853758605

theorem tailTrace_1003802 : CollatzResearch.WordTrace tailWord_1003802 prefixEnd_1003802 515432907944586853758605 := by
  unfold tailWord_1003802
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152916677351066144503415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24407777806269509718675773 9152916677351066144503415)
  ·
    refine ⟨13729375016026599216755123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9152916677351066144503415 13729375016026599216755123)
    ·
      refine ⟨20594062524039898825132685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13729375016026599216755123 20594062524039898825132685)
      ·
        refine ⟨7722773446514962059424757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20594062524039898825132685 7722773446514962059424757)
        ·
          refine ⟨724010010610777693071071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7722773446514962059424757 724010010610777693071071)
          ·
            refine ⟨1086015015916166539606607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724010010610777693071071 1086015015916166539606607)
            ·
              refine ⟨1629022523874249809409911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086015015916166539606607 1629022523874249809409911)
              ·
                refine ⟨2443533785811374714114867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629022523874249809409911 2443533785811374714114867)
                ·
                  refine ⟨3665300678717062071172301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2443533785811374714114867 3665300678717062071172301)
                  ·
                    refine ⟨1374487754518898276689613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3665300678717062071172301 1374487754518898276689613)
                    ·
                      refine ⟨515432907944586853758605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1374487754518898276689613 515432907944586853758605)
                      ·
                        rfl

theorem cell23_1003802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_1003802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003802 prefixEnd_1003802 := by exact prefixLift 1003802
  have htrace : WordTrace (prefixWord ++ tailWord_1003802) baseStart_1003802 baseEnd_1003802 := by
    simpa [prefixWord, tailWord_1003802, baseEnd_1003802] using wordTrace_append hprefix tailTrace_1003802
  have hstable : (prefixWord ++ tailWord_1003802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003802).length < 2 ^ (prefixWord ++ tailWord_1003802).sum := by decide
  have hdescent : baseEnd_1003802 < baseStart_1003802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003811 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5]
def baseStart_1003811 : Nat := 118140960795 + 1003811 * 2 ^ 59
def prefixEnd_1003811 : Nat := 4983230072969 + 3 ^ 40 * 1003811 * 2
def baseEnd_1003811 : Nat := 515437529270477318546063

theorem tailTrace_1003811 : CollatzResearch.WordTrace tailWord_1003811 prefixEnd_1003811 515437529270477318546063 := by
  unfold tailWord_1003811
  simp only [CollatzResearch.WordTrace]
  refine ⟨36611994966371659115091287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24407996644247772743394191 36611994966371659115091287)
  ·
    refine ⟨54917992449557488672636931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36611994966371659115091287 54917992449557488672636931)
    ·
      refine ⟨82376988674336233008955397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54917992449557488672636931 82376988674336233008955397)
      ·
        refine ⟨15445685376438043689179137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82376988674336233008955397 15445685376438043689179137)
        ·
          refine ⟨11584264032328532766884353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15445685376438043689179137 11584264032328532766884353)
          ·
            refine ⟨8688198024246399575163265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11584264032328532766884353 8688198024246399575163265)
            ·
              refine ⟨6516148518184799681372449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8688198024246399575163265 6516148518184799681372449)
              ·
                refine ⟨4887111388638599761029337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516148518184799681372449 4887111388638599761029337)
                ·
                  refine ⟨3665333541478949820772003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4887111388638599761029337 3665333541478949820772003)
                  ·
                    refine ⟨5498000312218424731158005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3665333541478949820772003 5498000312218424731158005)
                    ·
                      refine ⟨515437529270477318546063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5498000312218424731158005 515437529270477318546063)
                      ·
                        rfl

theorem cell23_1003811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_1003811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003811 prefixEnd_1003811 := by exact prefixLift 1003811
  have htrace : WordTrace (prefixWord ++ tailWord_1003811) baseStart_1003811 baseEnd_1003811 := by
    simpa [prefixWord, tailWord_1003811, baseEnd_1003811] using wordTrace_append hprefix tailTrace_1003811
  have hstable : (prefixWord ++ tailWord_1003811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003811).length < 2 ^ (prefixWord ++ tailWord_1003811).sum := by decide
  have hdescent : baseEnd_1003811 < baseStart_1003811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003812 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 1, 3, 2]
def baseStart_1003812 : Nat := 118140960795 + 1003812 * 2 ^ 59
def prefixEnd_1003812 : Nat := 4983230072969 + 3 ^ 40 * 1003812 * 2
def baseEnd_1003812 : Nat := 515438042751131814633559

theorem tailTrace_1003812 : CollatzResearch.WordTrace tailWord_1003812 prefixEnd_1003812 515438042751131814633559 := by
  unfold tailWord_1003812
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306015719684018142938845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24408020959578690857251793 18306015719684018142938845)
  ·
    refine ⟨6864755894881506803602067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18306015719684018142938845 6864755894881506803602067)
    ·
      refine ⟨10297133842322260205403101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6864755894881506803602067 10297133842322260205403101)
      ·
        refine ⟨3861425190870847577026163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10297133842322260205403101 3861425190870847577026163)
        ·
          refine ⟨5792137786306271365539245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861425190870847577026163 5792137786306271365539245)
          ·
            refine ⟨2172051669864851762077217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5792137786306271365539245 2172051669864851762077217)
            ·
              refine ⟨1629038752398638821557913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2172051669864851762077217 1629038752398638821557913)
              ·
                refine ⟨1221779064298979116168435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629038752398638821557913 1221779064298979116168435)
                ·
                  refine ⟨1832668596448468674252653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1221779064298979116168435 1832668596448468674252653)
                  ·
                    refine ⟨687250723668175752844745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1832668596448468674252653 687250723668175752844745)
                    ·
                      refine ⟨515438042751131814633559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687250723668175752844745 515438042751131814633559)
                      ·
                        rfl

theorem cell23_1003812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_1003812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003812 prefixEnd_1003812 := by exact prefixLift 1003812
  have htrace : WordTrace (prefixWord ++ tailWord_1003812) baseStart_1003812 baseEnd_1003812 := by
    simpa [prefixWord, tailWord_1003812, baseEnd_1003812] using wordTrace_append hprefix tailTrace_1003812
  have hstable : (prefixWord ++ tailWord_1003812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003812).length < 2 ^ (prefixWord ++ tailWord_1003812).sum := by decide
  have hdescent : baseEnd_1003812 < baseStart_1003812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003828 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1003828 : Nat := 118140960795 + 1003828 * 2 ^ 59
def prefixEnd_1003828 : Nat := 4983230072969 + 3 ^ 40 * 1003828 * 2
def baseEnd_1003828 : Nat := 515446258441603752033485

theorem tailTrace_1003828 : CollatzResearch.WordTrace tailWord_1003828 prefixEnd_1003828 515446258441603752033485 := by
  unfold tailWord_1003828
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306307503655035509230069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24408410004873380678973425 18306307503655035509230069)
  ·
    refine ⟨1716216328467659578990319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18306307503655035509230069 1716216328467659578990319)
    ·
      refine ⟨2574324492701489368485479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716216328467659578990319 2574324492701489368485479)
      ·
        refine ⟨3861486739052234052728219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2574324492701489368485479 3861486739052234052728219)
        ·
          refine ⟨5792230108578351079092329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861486739052234052728219 5792230108578351079092329)
          ·
            refine ⟨4344172581433763309319247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5792230108578351079092329 4344172581433763309319247)
            ·
              refine ⟨6516258872150644963978871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344172581433763309319247 6516258872150644963978871)
              ·
                refine ⟨9774388308225967445968307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6516258872150644963978871 9774388308225967445968307)
                ·
                  refine ⟨14661582462338951168952461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9774388308225967445968307 14661582462338951168952461)
                  ·
                    refine ⟨5498093423377106688357173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14661582462338951168952461 5498093423377106688357173)
                    ·
                      refine ⟨515446258441603752033485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5498093423377106688357173 515446258441603752033485)
                      ·
                        rfl

theorem cell23_1003828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1003828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003828 prefixEnd_1003828 := by exact prefixLift 1003828
  have htrace : WordTrace (prefixWord ++ tailWord_1003828) baseStart_1003828 baseEnd_1003828 := by
    simpa [prefixWord, tailWord_1003828, baseEnd_1003828] using wordTrace_append hprefix tailTrace_1003828
  have hstable : (prefixWord ++ tailWord_1003828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003828).length < 2 ^ (prefixWord ++ tailWord_1003828).sum := by decide
  have hdescent : baseEnd_1003828 < baseStart_1003828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003848 : List Nat := [2, 1, 3, 1, 1, 2, 2, 6, 5]
def baseStart_1003848 : Nat := 118140960795 + 1003848 * 2 ^ 59
def prefixEnd_1003848 : Nat := 4983230072969 + 3 ^ 40 * 1003848 * 2
def baseEnd_1003848 : Nat := 57272947561632630420377

theorem tailTrace_1003848 : CollatzResearch.WordTrace tailWord_1003848 prefixEnd_1003848 57272947561632630420377 := by
  unfold tailWord_1003848
  simp only [CollatzResearch.WordTrace]
  refine ⟨18306672233618807217094099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24408896311491742956125465 18306672233618807217094099)
  ·
    refine ⟨27460008350428210825641149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18306672233618807217094099 27460008350428210825641149)
    ·
      refine ⟨10297503131410579059615431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27460008350428210825641149 10297503131410579059615431)
      ·
        refine ⟨15446254697115868589423147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10297503131410579059615431 15446254697115868589423147)
        ·
          refine ⟨23169382045673802884134721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15446254697115868589423147 23169382045673802884134721)
          ·
            refine ⟨17377036534255352163101041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23169382045673802884134721 17377036534255352163101041)
            ·
              refine ⟨13032777400691514122325781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17377036534255352163101041 13032777400691514122325781)
              ·
                refine ⟨610911440657414724484021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13032777400691514122325781 610911440657414724484021)
                ·
                  refine ⟨57272947561632630420377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610911440657414724484021 57272947561632630420377)
                  ·
                    rfl

theorem cell23_1003848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 6, 5].length) (baseStart_1003848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003848 prefixEnd_1003848 := by exact prefixLift 1003848
  have htrace : WordTrace (prefixWord ++ tailWord_1003848) baseStart_1003848 baseEnd_1003848 := by
    simpa [prefixWord, tailWord_1003848, baseEnd_1003848] using wordTrace_append hprefix tailTrace_1003848
  have hstable : (prefixWord ++ tailWord_1003848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003848).length < 2 ^ (prefixWord ++ tailWord_1003848).sum := by decide
  have hdescent : baseEnd_1003848 < baseStart_1003848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003858 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3]
def baseStart_1003858 : Nat := 118140960795 + 1003858 * 2 ^ 59
def prefixEnd_1003858 : Nat := 4983230072969 + 3 ^ 40 * 1003858 * 2
def baseEnd_1003858 : Nat := 515461662861238634658347

theorem tailTrace_1003858 : CollatzResearch.WordTrace tailWord_1003858 prefixEnd_1003858 515461662861238634658347 := by
  unfold tailWord_1003858
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153427299300346535513057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24409139464800924094701485 9153427299300346535513057)
  ·
    refine ⟨6865070474475259901634793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9153427299300346535513057 6865070474475259901634793)
    ·
      refine ⟨5148802855856444926226095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6865070474475259901634793 5148802855856444926226095)
      ·
        refine ⟨7723204283784667389339143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5148802855856444926226095 7723204283784667389339143)
        ·
          refine ⟨11584806425677001084008715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7723204283784667389339143 11584806425677001084008715)
          ·
            refine ⟨17377209638515501626013073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11584806425677001084008715 17377209638515501626013073)
            ·
              refine ⟨13032907228886626219509805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17377209638515501626013073 13032907228886626219509805)
              ·
                refine ⟨4887340210832484832316177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13032907228886626219509805 4887340210832484832316177)
                ·
                  refine ⟨3665505158124363624237133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4887340210832484832316177 3665505158124363624237133)
                  ·
                    refine ⟨1374564434296636359088925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3665505158124363624237133 1374564434296636359088925)
                    ·
                      refine ⟨515461662861238634658347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1374564434296636359088925 515461662861238634658347)
                      ·
                        rfl

theorem cell23_1003858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_1003858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003858 prefixEnd_1003858 := by exact prefixLift 1003858
  have htrace : WordTrace (prefixWord ++ tailWord_1003858) baseStart_1003858 baseEnd_1003858 := by
    simpa [prefixWord, tailWord_1003858, baseEnd_1003858] using wordTrace_append hprefix tailTrace_1003858
  have hstable : (prefixWord ++ tailWord_1003858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003858).length < 2 ^ (prefixWord ++ tailWord_1003858).sum := by decide
  have hdescent : baseEnd_1003858 < baseStart_1003858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003915 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 2, 4, 2]
def baseStart_1003915 : Nat := 118140960795 + 1003915 * 2 ^ 59
def prefixEnd_1003915 : Nat := 4983230072969 + 3 ^ 40 * 1003915 * 2
def baseEnd_1003915 : Nat := 515490931258544911645585

theorem tailTrace_1003915 : CollatzResearch.WordTrace tailWord_1003915 prefixEnd_1003915 515490931258544911645585 := by
  unfold tailWord_1003915
  simp only [CollatzResearch.WordTrace]
  refine ⟨36615788157994884876877199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24410525438663256584584799 36615788157994884876877199)
  ·
    refine ⟨54923682236992327315315799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36615788157994884876877199 54923682236992327315315799)
    ·
      refine ⟨82385523355488490972973699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54923682236992327315315799 82385523355488490972973699)
      ·
        refine ⟨123578285033232736459460549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82385523355488490972973699 123578285033232736459460549)
        ·
          refine ⟨23170928443731138086148853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123578285033232736459460549 23170928443731138086148853)
          ·
            refine ⟨2172274541599794195576455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23170928443731138086148853 2172274541599794195576455)
            ·
              refine ⟨3258411812399691293364683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172274541599794195576455 3258411812399691293364683)
              ·
                refine ⟨4887617718599536940047025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3258411812399691293364683 4887617718599536940047025)
                ·
                  refine ⟨3665713288949652705035269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4887617718599536940047025 3665713288949652705035269)
                  ·
                    refine ⟨687321241678059882194113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3665713288949652705035269 687321241678059882194113)
                    ·
                      refine ⟨515490931258544911645585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687321241678059882194113 515490931258544911645585)
                      ·
                        rfl

theorem cell23_1003915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 2, 4, 2].length) (baseStart_1003915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003915 prefixEnd_1003915 := by exact prefixLift 1003915
  have htrace : WordTrace (prefixWord ++ tailWord_1003915) baseStart_1003915 baseEnd_1003915 := by
    simpa [prefixWord, tailWord_1003915, baseEnd_1003915] using wordTrace_append hprefix tailTrace_1003915
  have hstable : (prefixWord ++ tailWord_1003915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003915).length < 2 ^ (prefixWord ++ tailWord_1003915).sum := by decide
  have hdescent : baseEnd_1003915 < baseStart_1003915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003938 : List Nat := [3, 3, 1, 2, 1, 1, 2, 2, 8]
def baseStart_1003938 : Nat := 118140960795 + 1003938 * 2 ^ 59
def prefixEnd_1003938 : Nat := 4983230072969 + 3 ^ 40 * 1003938 * 2
def baseEnd_1003938 : Nat := 57278082368177591295331

theorem tailTrace_1003938 : CollatzResearch.WordTrace tailWord_1003938 prefixEnd_1003938 57278082368177591295331 := by
  unfold tailWord_1003938
  simp only [CollatzResearch.WordTrace]
  refine ⟨9154156759227889951241117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24411084691274373203309645 9154156759227889951241117)
  ·
    refine ⟨3432808784710458731715419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9154156759227889951241117 3432808784710458731715419)
    ·
      refine ⟨5149213177065688097573129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3432808784710458731715419 5149213177065688097573129)
      ·
        refine ⟨3861909882799266073179847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5149213177065688097573129 3861909882799266073179847)
        ·
          refine ⟨5792864824198899109769771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3861909882799266073179847 5792864824198899109769771)
          ·
            refine ⟨8689297236298348664654657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5792864824198899109769771 8689297236298348664654657)
            ·
              refine ⟨6516972927223761498490993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8689297236298348664654657 6516972927223761498490993)
              ·
                refine ⟨4887729695417821123868245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6516972927223761498490993 4887729695417821123868245)
                ·
                  refine ⟨57278082368177591295331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4887729695417821123868245 57278082368177591295331)
                  ·
                    rfl

theorem cell23_1003938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 8].length) (baseStart_1003938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003938 prefixEnd_1003938 := by exact prefixLift 1003938
  have htrace : WordTrace (prefixWord ++ tailWord_1003938) baseStart_1003938 baseEnd_1003938 := by
    simpa [prefixWord, tailWord_1003938, baseEnd_1003938] using wordTrace_append hprefix tailTrace_1003938
  have hstable : (prefixWord ++ tailWord_1003938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003938).length < 2 ^ (prefixWord ++ tailWord_1003938).sum := by decide
  have hdescent : baseEnd_1003938 < baseStart_1003938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003975 : List Nat := [1, 1, 4, 1, 1, 4, 1, 2, 1, 5, 2]
def baseStart_1003975 : Nat := 118140960795 + 1003975 * 2 ^ 59
def prefixEnd_1003975 : Nat := 4983230072969 + 3 ^ 40 * 1003975 * 2
def baseEnd_1003975 : Nat := 515521740097814676895309

theorem tailTrace_1003975 : CollatzResearch.WordTrace tailWord_1003975 prefixEnd_1003975 515521740097814676895309 := by
  unfold tailWord_1003975
  simp only [CollatzResearch.WordTrace]
  refine ⟨36617976537777515124061379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24411984358518343416040919 36617976537777515124061379)
  ·
    refine ⟨54926964806666272686092069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36617976537777515124061379 54926964806666272686092069)
    ·
      refine ⟨10298805901249926128642263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54926964806666272686092069 10298805901249926128642263)
      ·
        refine ⟨15448208851874889192963395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10298805901249926128642263 15448208851874889192963395)
        ·
          refine ⟨23172313277812333789445093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15448208851874889192963395 23172313277812333789445093)
          ·
            refine ⟨4344808739589812585520955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23172313277812333789445093 4344808739589812585520955)
            ·
              refine ⟨6517213109384718878281433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4344808739589812585520955 6517213109384718878281433)
              ·
                refine ⟨4887909832038539158711075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517213109384718878281433 4887909832038539158711075)
                ·
                  refine ⟨7331864748057808738066613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4887909832038539158711075 7331864748057808738066613)
                  ·
                    refine ⟨687362320130419569193745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7331864748057808738066613 687362320130419569193745)
                    ·
                      refine ⟨515521740097814676895309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687362320130419569193745 515521740097814676895309)
                      ·
                        rfl

theorem cell23_1003975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 2, 1, 5, 2].length) (baseStart_1003975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003975 prefixEnd_1003975 := by exact prefixLift 1003975
  have htrace : WordTrace (prefixWord ++ tailWord_1003975) baseStart_1003975 baseEnd_1003975 := by
    simpa [prefixWord, tailWord_1003975, baseEnd_1003975] using wordTrace_append hprefix tailTrace_1003975
  have hstable : (prefixWord ++ tailWord_1003975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003975).length < 2 ^ (prefixWord ++ tailWord_1003975).sum := by decide
  have hdescent : baseEnd_1003975 < baseStart_1003975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1003999 : List Nat := [1, 1, 2, 3, 3, 2, 3, 3, 1, 1, 3]
def baseStart_1003999 : Nat := 118140960795 + 1003999 * 2 ^ 59
def prefixEnd_1003999 : Nat := 4983230072969 + 3 ^ 40 * 1003999 * 2
def baseEnd_1003999 : Nat := 515534063633522582995199

theorem tailTrace_1003999 : CollatzResearch.WordTrace tailWord_1003999 prefixEnd_1003999 515534063633522582995199 := by
  unfold tailWord_1003999
  simp only [CollatzResearch.WordTrace]
  refine ⟨36618851889690567222935051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24412567926460378148623367 36618851889690567222935051)
  ·
    refine ⟨54928277834535850834402577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36618851889690567222935051 54928277834535850834402577)
    ·
      refine ⟨41196208375901888125801933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54928277834535850834402577 41196208375901888125801933)
      ·
        refine ⟨15448578140963208047175725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41196208375901888125801933 15448578140963208047175725)
        ·
          refine ⟨5793216802861203017690897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15448578140963208047175725 5793216802861203017690897)
          ·
            refine ⟨4344912602145902263268173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5793216802861203017690897 4344912602145902263268173)
            ·
              refine ⟨1629342225804713348725565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4344912602145902263268173 1629342225804713348725565)
              ·
                refine ⟨611003334676767505772087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1629342225804713348725565 611003334676767505772087)
                ·
                  refine ⟨916505002015151258658131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611003334676767505772087 916505002015151258658131)
                  ·
                    refine ⟨1374757503022726887987197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 916505002015151258658131 1374757503022726887987197)
                    ·
                      refine ⟨515534063633522582995199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1374757503022726887987197 515534063633522582995199)
                      ·
                        rfl

theorem cell23_1003999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 1, 1, 3].length) (baseStart_1003999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1003999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1003999 prefixEnd_1003999 := by exact prefixLift 1003999
  have htrace : WordTrace (prefixWord ++ tailWord_1003999) baseStart_1003999 baseEnd_1003999 := by
    simpa [prefixWord, tailWord_1003999, baseEnd_1003999] using wordTrace_append hprefix tailTrace_1003999
  have hstable : (prefixWord ++ tailWord_1003999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1003999).length < 2 ^ (prefixWord ++ tailWord_1003999).sum := by decide
  have hdescent : baseEnd_1003999 < baseStart_1003999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1003999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004015 : List Nat := [1, 1, 2, 1, 4, 1, 1, 6, 2, 4]
def baseStart_1004015 : Nat := 118140960795 + 1004015 * 2 ^ 59
def prefixEnd_1004015 : Nat := 4983230072969 + 3 ^ 40 * 1004015 * 2
def baseEnd_1004015 : Nat := 171847426441331506798375

theorem tailTrace_1004015 : CollatzResearch.WordTrace tailWord_1004015 prefixEnd_1004015 171847426441331506798375 := by
  unfold tailWord_1004015
  simp only [CollatzResearch.WordTrace]
  refine ⟨36619435457632601955517499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24412956971755067970344999 36619435457632601955517499)
  ·
    refine ⟨54929153186448902933276249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36619435457632601955517499 54929153186448902933276249)
    ·
      refine ⟨41196864889836677199957187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54929153186448902933276249 41196864889836677199957187)
      ·
        refine ⟨61795297334755015799935781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41196864889836677199957187 61795297334755015799935781)
        ·
          refine ⟨11586618250266565462487959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61795297334755015799935781 11586618250266565462487959)
          ·
            refine ⟨17379927375399848193731939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11586618250266565462487959 17379927375399848193731939)
            ·
              refine ⟨26069891063099772290597909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17379927375399848193731939 26069891063099772290597909)
              ·
                refine ⟨1222026143582801826121777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26069891063099772290597909 1222026143582801826121777)
                ·
                  refine ⟨916519607687101369591333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222026143582801826121777 916519607687101369591333)
                  ·
                    refine ⟨171847426441331506798375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 916519607687101369591333 171847426441331506798375)
                    ·
                      rfl

theorem cell23_1004015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 6, 2, 4].length) (baseStart_1004015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004015 prefixEnd_1004015 := by exact prefixLift 1004015
  have htrace : WordTrace (prefixWord ++ tailWord_1004015) baseStart_1004015 baseEnd_1004015 := by
    simpa [prefixWord, tailWord_1004015, baseEnd_1004015] using wordTrace_append hprefix tailTrace_1004015
  have hstable : (prefixWord ++ tailWord_1004015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004015).length < 2 ^ (prefixWord ++ tailWord_1004015).sum := by decide
  have hdescent : baseEnd_1004015 < baseStart_1004015 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004039 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1004039 : Nat := 118140960795 + 1004039 * 2 ^ 59
def prefixEnd_1004039 : Nat := 4983230072969 + 3 ^ 40 * 1004039 * 2
def baseEnd_1004039 : Nat := 515554602859702426495015

theorem tailTrace_1004039 : CollatzResearch.WordTrace tailWord_1004039 prefixEnd_1004039 515554602859702426495015 := by
  unfold tailWord_1004039
  simp only [CollatzResearch.WordTrace]
  refine ⟨36620310809545654054391171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24413540539697102702927447 36620310809545654054391171)
  ·
    refine ⟨54930466214318481081586757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36620310809545654054391171 54930466214318481081586757)
    ·
      refine ⟨10299462415184715202797517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 54930466214318481081586757 10299462415184715202797517)
      ·
        refine ⟨3862298405694268201049069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10299462415184715202797517 3862298405694268201049069)
        ·
          refine ⟨1448361902135350575393401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3862298405694268201049069 1448361902135350575393401)
          ·
            refine ⟨1086271426601512931545051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448361902135350575393401 1086271426601512931545051)
            ·
              refine ⟨1629407139902269397317577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086271426601512931545051 1629407139902269397317577)
              ·
                refine ⟨1222055354926702047988183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1629407139902269397317577 1222055354926702047988183)
                ·
                  refine ⟨1833083032390053071982275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222055354926702047988183 1833083032390053071982275)
                  ·
                    refine ⟨2749624548585079607973413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1833083032390053071982275 2749624548585079607973413)
                    ·
                      refine ⟨515554602859702426495015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2749624548585079607973413 515554602859702426495015)
                      ·
                        rfl

theorem cell23_1004039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1004039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004039 prefixEnd_1004039 := by exact prefixLift 1004039
  have htrace : WordTrace (prefixWord ++ tailWord_1004039) baseStart_1004039 baseEnd_1004039 := by
    simpa [prefixWord, tailWord_1004039, baseEnd_1004039] using wordTrace_append hprefix tailTrace_1004039
  have hstable : (prefixWord ++ tailWord_1004039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004039).length < 2 ^ (prefixWord ++ tailWord_1004039).sum := by decide
  have hdescent : baseEnd_1004039 < baseStart_1004039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004052 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 3, 2, 4]
def baseStart_1004052 : Nat := 118140960795 + 1004052 * 2 ^ 59
def prefixEnd_1004052 : Nat := 4983230072969 + 3 ^ 40 * 1004052 * 2
def baseEnd_1004052 : Nat := 515561278108210875632455

theorem tailTrace_1004052 : CollatzResearch.WordTrace tailWord_1004052 prefixEnd_1004052 515561278108210875632455 := by
  unfold tailWord_1004052
  simp only [CollatzResearch.WordTrace]
  refine ⟨18310392479249278637307205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24413856638999038183076273 18310392479249278637307205)
  ·
    refine ⟨3433198589859239744495101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18310392479249278637307205 3433198589859239744495101)
    ·
      refine ⟨1287449471197214904185663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3433198589859239744495101 1287449471197214904185663)
      ·
        refine ⟨1931174206795822356278495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1287449471197214904185663 1931174206795822356278495)
        ·
          refine ⟨2896761310193733534417743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1931174206795822356278495 2896761310193733534417743)
          ·
            refine ⟨4345141965290600301626615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2896761310193733534417743 4345141965290600301626615)
            ·
              refine ⟨6517712947935900452439923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4345141965290600301626615 6517712947935900452439923)
              ·
                refine ⟨9776569421903850678659885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6517712947935900452439923 9776569421903850678659885)
                ·
                  refine ⟨3666213533213944004497457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9776569421903850678659885 3666213533213944004497457)
                  ·
                    refine ⟨2749660149910458003373093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666213533213944004497457 2749660149910458003373093)
                    ·
                      refine ⟨515561278108210875632455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2749660149910458003373093 515561278108210875632455)
                      ·
                        rfl

theorem cell23_1004052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_1004052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004052 prefixEnd_1004052 := by exact prefixLift 1004052
  have htrace : WordTrace (prefixWord ++ tailWord_1004052) baseStart_1004052 baseEnd_1004052 := by
    simpa [prefixWord, tailWord_1004052, baseEnd_1004052] using wordTrace_append hprefix tailTrace_1004052
  have hstable : (prefixWord ++ tailWord_1004052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004052).length < 2 ^ (prefixWord ++ tailWord_1004052).sum := by decide
  have hdescent : baseEnd_1004052 < baseStart_1004052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004082 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2]
def baseStart_1004082 : Nat := 118140960795 + 1004082 * 2 ^ 59
def prefixEnd_1004082 : Nat := 4983230072969 + 3 ^ 40 * 1004082 * 2
def baseEnd_1004082 : Nat := 515576682527845758257317

theorem tailTrace_1004082 : CollatzResearch.WordTrace tailWord_1004082 prefixEnd_1004082 515576682527845758257317 := by
  unfold tailWord_1004082
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155469787097468099551625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24414586098926581598804333 9155469787097468099551625)
  ·
    refine ⟨6866602340323101074663719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9155469787097468099551625 6866602340323101074663719)
    ·
      refine ⟨10299903510484651611995579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6866602340323101074663719 10299903510484651611995579)
      ·
        refine ⟨15449855265726977417993369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10299903510484651611995579 15449855265726977417993369)
        ·
          refine ⟨11587391449295233063495027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15449855265726977417993369 11587391449295233063495027)
          ·
            refine ⟨17381087173942849595242541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11587391449295233063495027 17381087173942849595242541)
            ·
              refine ⟨6517907690228568598215953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17381087173942849595242541 6517907690228568598215953)
              ·
                refine ⟨4888430767671426448661965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6517907690228568598215953 4888430767671426448661965)
                ·
                  refine ⟨1833161537876784918248237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4888430767671426448661965 1833161537876784918248237)
                  ·
                    refine ⟨687435576703794344343089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833161537876784918248237 687435576703794344343089)
                    ·
                      refine ⟨515576682527845758257317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687435576703794344343089 515576682527845758257317)
                      ·
                        rfl

theorem cell23_1004082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_1004082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004082 prefixEnd_1004082 := by exact prefixLift 1004082
  have htrace : WordTrace (prefixWord ++ tailWord_1004082) baseStart_1004082 baseEnd_1004082 := by
    simpa [prefixWord, tailWord_1004082, baseEnd_1004082] using wordTrace_append hprefix tailTrace_1004082
  have hstable : (prefixWord ++ tailWord_1004082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004082).length < 2 ^ (prefixWord ++ tailWord_1004082).sum := by decide
  have hdescent : baseEnd_1004082 < baseStart_1004082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004116 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 1, 3, 2]
def baseStart_1004116 : Nat := 118140960795 + 1004116 * 2 ^ 59
def prefixEnd_1004116 : Nat := 4983230072969 + 3 ^ 40 * 1004116 * 2
def baseEnd_1004116 : Nat := 515594140870098625232161

theorem tailTrace_1004116 : CollatzResearch.WordTrace tailWord_1004116 prefixEnd_1004116 515594140870098625232161 := by
  unfold tailWord_1004116
  simp only [CollatzResearch.WordTrace]
  refine ⟨18311559615133348102472101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24415412820177797469962801 18311559615133348102472101)
  ·
    refine ⟨3433417427837502769213519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18311559615133348102472101 3433417427837502769213519)
    ·
      refine ⟨5150126141756254153820279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3433417427837502769213519 5150126141756254153820279)
      ·
        refine ⟨7725189212634381230730419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5150126141756254153820279 7725189212634381230730419)
        ·
          refine ⟨11587783818951571846095629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7725189212634381230730419 11587783818951571846095629)
          ·
            refine ⟨4345418932106839442285861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11587783818951571846095629 4345418932106839442285861)
            ·
              refine ⟨814766049770032395428599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4345418932106839442285861 814766049770032395428599)
              ·
                refine ⟨1222149074655048593142899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 814766049770032395428599 1222149074655048593142899)
                ·
                  refine ⟨1833223611982572889714349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222149074655048593142899 1833223611982572889714349)
                  ·
                    refine ⟨687458854493464833642881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1833223611982572889714349 687458854493464833642881)
                    ·
                      refine ⟨515594140870098625232161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687458854493464833642881 515594140870098625232161)
                      ·
                        rfl

theorem cell23_1004116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_1004116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004116 prefixEnd_1004116 := by exact prefixLift 1004116
  have htrace : WordTrace (prefixWord ++ tailWord_1004116) baseStart_1004116 baseEnd_1004116 := by
    simpa [prefixWord, tailWord_1004116, baseEnd_1004116] using wordTrace_append hprefix tailTrace_1004116
  have hstable : (prefixWord ++ tailWord_1004116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004116).length < 2 ^ (prefixWord ++ tailWord_1004116).sum := by decide
  have hdescent : baseEnd_1004116 < baseStart_1004116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004129 : List Nat := [1, 2, 3, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_1004129 : Nat := 118140960795 + 1004129 * 2 ^ 59
def prefixEnd_1004129 : Nat := 4983230072969 + 3 ^ 40 * 1004129 * 2
def baseEnd_1004129 : Nat := 515600816118607074369601

theorem tailTrace_1004129 : CollatzResearch.WordTrace tailWord_1004129 prefixEnd_1004129 515600816118607074369601 := by
  unfold tailWord_1004129
  simp only [CollatzResearch.WordTrace]
  refine ⟨36623593379219599425167441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24415728919479732950111627 36623593379219599425167441)
  ·
    refine ⟨27467695034414699568875581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36623593379219599425167441 27467695034414699568875581)
    ·
      refine ⟨10300385637905512338328343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27467695034414699568875581 10300385637905512338328343)
      ·
        refine ⟨15450578456858268507492515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10300385637905512338328343 15450578456858268507492515)
        ·
          refine ⟨23175867685287402761238773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15450578456858268507492515 23175867685287402761238773)
          ·
            refine ⟨2172737595495694008866135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 23175867685287402761238773 2172737595495694008866135)
            ·
              refine ⟨3259106393243541013299203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172737595495694008866135 3259106393243541013299203)
              ·
                refine ⟨4888659589865311519948805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259106393243541013299203 4888659589865311519948805)
                ·
                  refine ⟨916623673099745909990401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4888659589865311519948805 916623673099745909990401)
                  ·
                    refine ⟨687467754824809432492801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 916623673099745909990401 687467754824809432492801)
                    ·
                      refine ⟨515600816118607074369601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687467754824809432492801 515600816118607074369601)
                      ·
                        rfl

theorem cell23_1004129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_1004129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004129 prefixEnd_1004129 := by exact prefixLift 1004129
  have htrace : WordTrace (prefixWord ++ tailWord_1004129) baseStart_1004129 baseEnd_1004129 := by
    simpa [prefixWord, tailWord_1004129, baseEnd_1004129] using wordTrace_append hprefix tailTrace_1004129
  have hstable : (prefixWord ++ tailWord_1004129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004129).length < 2 ^ (prefixWord ++ tailWord_1004129).sum := by decide
  have hdescent : baseEnd_1004129 < baseStart_1004129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004142 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1004142 : Nat := 118140960795 + 1004142 * 2 ^ 59
def prefixEnd_1004142 : Nat := 4983230072969 + 3 ^ 40 * 1004142 * 2
def baseEnd_1004142 : Nat := 515607491367115523507041

theorem tailTrace_1004142 : CollatzResearch.WordTrace tailWord_1004142 prefixEnd_1004142 515607491367115523507041 := by
  unfold tailWord_1004142
  simp only [CollatzResearch.WordTrace]
  refine ⟨4578008441021562830673835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24416045018781668430260453 4578008441021562830673835)
  ·
    refine ⟨6867012661532344246010753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4578008441021562830673835 6867012661532344246010753)
    ·
      refine ⟨5150259496149258184508065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6867012661532344246010753 5150259496149258184508065)
      ·
        refine ⟨3862694622111943638381049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5150259496149258184508065 3862694622111943638381049)
        ·
          refine ⟨2897020966583957728785787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3862694622111943638381049 2897020966583957728785787)
          ·
            refine ⟨4345531449875936593178681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2897020966583957728785787 4345531449875936593178681)
            ·
              refine ⟨3259148587406952444884011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345531449875936593178681 3259148587406952444884011)
              ·
                refine ⟨4888722881110428667326017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259148587406952444884011 4888722881110428667326017)
                ·
                  refine ⟨3666542160832821500494513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4888722881110428667326017 3666542160832821500494513)
                  ·
                    refine ⟨2749906620624616125370885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3666542160832821500494513 2749906620624616125370885)
                    ·
                      refine ⟨515607491367115523507041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2749906620624616125370885 515607491367115523507041)
                      ·
                        rfl

theorem cell23_1004142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1004142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004142 prefixEnd_1004142 := by exact prefixLift 1004142
  have htrace : WordTrace (prefixWord ++ tailWord_1004142) baseStart_1004142 baseEnd_1004142 := by
    simpa [prefixWord, tailWord_1004142, baseEnd_1004142] using wordTrace_append hprefix tailTrace_1004142
  have hstable : (prefixWord ++ tailWord_1004142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004142).length < 2 ^ (prefixWord ++ tailWord_1004142).sum := by decide
  have hdescent : baseEnd_1004142 < baseStart_1004142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004146 : List Nat := [3, 2, 1, 2, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1004146 : Nat := 118140960795 + 1004146 * 2 ^ 59
def prefixEnd_1004146 : Nat := 4983230072969 + 3 ^ 40 * 1004146 * 2
def baseEnd_1004146 : Nat := 515609545289733507857023

theorem tailTrace_1004146 : CollatzResearch.WordTrace tailWord_1004146 prefixEnd_1004146 515609545289733507857023 := by
  unfold tailWord_1004146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156053355039502832134073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24416142280105340885690861 9156053355039502832134073)
  ·
    refine ⟨6867040016279627124100555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9156053355039502832134073 6867040016279627124100555)
    ·
      refine ⟨10300560024419440686150833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6867040016279627124100555 10300560024419440686150833)
      ·
        refine ⟨7725420018314580514613125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10300560024419440686150833 7725420018314580514613125)
        ·
          refine ⟨1448516253433983846489961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7725420018314580514613125 1448516253433983846489961)
          ·
            refine ⟨1086387190075487884867471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448516253433983846489961 1086387190075487884867471)
            ·
              refine ⟨1629580785113231827301207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086387190075487884867471 1629580785113231827301207)
              ·
                refine ⟨2444371177669847740951811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629580785113231827301207 2444371177669847740951811)
                ·
                  refine ⟨3666556766504771611427717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444371177669847740951811 3666556766504771611427717)
                  ·
                    refine ⟨687479393719644677142697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3666556766504771611427717 687479393719644677142697)
                    ·
                      refine ⟨515609545289733507857023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687479393719644677142697 515609545289733507857023)
                      ·
                        rfl

theorem cell23_1004146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1004146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004146 prefixEnd_1004146 := by exact prefixLift 1004146
  have htrace : WordTrace (prefixWord ++ tailWord_1004146) baseStart_1004146 baseEnd_1004146 := by
    simpa [prefixWord, tailWord_1004146, baseEnd_1004146] using wordTrace_append hprefix tailTrace_1004146
  have hstable : (prefixWord ++ tailWord_1004146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004146).length < 2 ^ (prefixWord ++ tailWord_1004146).sum := by decide
  have hdescent : baseEnd_1004146 < baseStart_1004146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004165 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 1, 7]
def baseStart_1004165 : Nat := 118140960795 + 1004165 * 2 ^ 59
def prefixEnd_1004165 : Nat := 4983230072969 + 3 ^ 40 * 1004165 * 2
def baseEnd_1004165 : Nat := 171873100474056311173145

theorem tailTrace_1004165 : CollatzResearch.WordTrace tailWord_1004165 prefixEnd_1004165 171873100474056311173145 := by
  unfold tailWord_1004165
  simp only [CollatzResearch.WordTrace]
  refine ⟨36624906407089177573477949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24416604271392785048985299 36624906407089177573477949)
  ·
    refine ⟨13734339902658441590054231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36624906407089177573477949 13734339902658441590054231)
    ·
      refine ⟨20601509853987662385081347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734339902658441590054231 20601509853987662385081347)
      ·
        refine ⟨30902264780981493577622021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20601509853987662385081347 30902264780981493577622021)
        ·
          refine ⟨5794174646434030045804129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30902264780981493577622021 5794174646434030045804129)
          ·
            refine ⟨4345630984825522534353097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5794174646434030045804129 4345630984825522534353097)
            ·
              refine ⟨3259223238619141900764823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4345630984825522534353097 3259223238619141900764823)
              ·
                refine ⟨4888834857928712851147235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259223238619141900764823 4888834857928712851147235)
                ·
                  refine ⟨7333252286893069276720853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888834857928712851147235 7333252286893069276720853)
                  ·
                    refine ⟨171873100474056311173145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7333252286893069276720853 171873100474056311173145)
                    ·
                      rfl

theorem cell23_1004165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_1004165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004165 prefixEnd_1004165 := by exact prefixLift 1004165
  have htrace : WordTrace (prefixWord ++ tailWord_1004165) baseStart_1004165 baseEnd_1004165 := by
    simpa [prefixWord, tailWord_1004165, baseEnd_1004165] using wordTrace_append hprefix tailTrace_1004165
  have hstable : (prefixWord ++ tailWord_1004165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004165).length < 2 ^ (prefixWord ++ tailWord_1004165).sum := by decide
  have hdescent : baseEnd_1004165 < baseStart_1004165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004186 : List Nat := [3, 1, 1, 6, 2, 1, 1, 1, 7]
def baseStart_1004186 : Nat := 118140960795 + 1004186 * 2 ^ 59
def prefixEnd_1004186 : Nat := 4983230072969 + 3 ^ 40 * 1004186 * 2
def baseEnd_1004186 : Nat := 57292231612879261261871

theorem tailTrace_1004186 : CollatzResearch.WordTrace tailWord_1004186 prefixEnd_1004186 57292231612879261261871 := by
  unfold tailWord_1004186
  simp only [CollatzResearch.WordTrace]
  refine ⟨9156418085003274539998103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24417114893342065439994941 9156418085003274539998103)
  ·
    refine ⟨13734627127504911809997155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9156418085003274539998103 13734627127504911809997155)
    ·
      refine ⟨20601940691257367714995733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13734627127504911809997155 20601940691257367714995733)
      ·
        refine ⟨965715969902689111640425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20601940691257367714995733 965715969902689111640425)
        ·
          refine ⟨724286977427016833730319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965715969902689111640425 724286977427016833730319)
          ·
            refine ⟨1086430466140525250595479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724286977427016833730319 1086430466140525250595479)
            ·
              refine ⟨1629645699210787875893219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086430466140525250595479 1629645699210787875893219)
              ·
                refine ⟨2444468548816181813839829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629645699210787875893219 2444468548816181813839829)
                ·
                  refine ⟨57292231612879261261871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2444468548816181813839829 57292231612879261261871)
                  ·
                    rfl

theorem cell23_1004186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 1, 1, 7].length) (baseStart_1004186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004186 prefixEnd_1004186 := by exact prefixLift 1004186
  have htrace : WordTrace (prefixWord ++ tailWord_1004186) baseStart_1004186 baseEnd_1004186 := by
    simpa [prefixWord, tailWord_1004186, baseEnd_1004186] using wordTrace_append hprefix tailTrace_1004186
  have hstable : (prefixWord ++ tailWord_1004186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004186).length < 2 ^ (prefixWord ++ tailWord_1004186).sum := by decide
  have hdescent : baseEnd_1004186 < baseStart_1004186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004192 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1004192 : Nat := 118140960795 + 1004192 * 2 ^ 59
def prefixEnd_1004192 : Nat := 4983230072969 + 3 ^ 40 * 1004192 * 2
def baseEnd_1004192 : Nat := 515633165399840327881811

theorem tailTrace_1004192 : CollatzResearch.WordTrace tailWord_1004192 prefixEnd_1004192 515633165399840327881811 := by
  unfold tailWord_1004192
  simp only [CollatzResearch.WordTrace]
  refine ⟨18312945588995680592355415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24417260785327574123140553 18312945588995680592355415)
  ·
    refine ⟨27469418383493520888533123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18312945588995680592355415 27469418383493520888533123)
    ·
      refine ⟨41204127575240281332799685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27469418383493520888533123 41204127575240281332799685)
      ·
        refine ⟨7725773920357552749899941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41204127575240281332799685 7725773920357552749899941)
        ·
          refine ⟨1448582610067041140606239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7725773920357552749899941 1448582610067041140606239)
          ·
            refine ⟨2172873915100561710909359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1448582610067041140606239 2172873915100561710909359)
            ·
              refine ⟨3259310872650842566364039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2172873915100561710909359 3259310872650842566364039)
              ·
                refine ⟨4888966308976263849546059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3259310872650842566364039 4888966308976263849546059)
                ·
                  refine ⟨7333449463464395774319089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4888966308976263849546059 7333449463464395774319089)
                  ·
                    refine ⟨5500087097598296830739317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7333449463464395774319089 5500087097598296830739317)
                    ·
                      refine ⟨515633165399840327881811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5500087097598296830739317 515633165399840327881811)
                      ·
                        rfl

theorem cell23_1004192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1004192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004192 prefixEnd_1004192 := by exact prefixLift 1004192
  have htrace : WordTrace (prefixWord ++ tailWord_1004192) baseStart_1004192 baseEnd_1004192 := by
    simpa [prefixWord, tailWord_1004192, baseEnd_1004192] using wordTrace_append hprefix tailTrace_1004192
  have hstable : (prefixWord ++ tailWord_1004192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004192).length < 2 ^ (prefixWord ++ tailWord_1004192).sum := by decide
  have hdescent : baseEnd_1004192 < baseStart_1004192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004272 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 1, 5]
def baseStart_1004272 : Nat := 118140960795 + 1004272 * 2 ^ 59
def prefixEnd_1004272 : Nat := 4983230072969 + 3 ^ 40 * 1004272 * 2
def baseEnd_1004272 : Nat := 171891414617400004960481

theorem tailTrace_1004272 : CollatzResearch.WordTrace tailWord_1004272 prefixEnd_1004272 171891414617400004960481 := by
  unfold tailWord_1004272
  simp only [CollatzResearch.WordTrace]
  refine ⟨18314404508850767423811535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24419206011801023231748713 18314404508850767423811535)
  ·
    refine ⟨27471606763276151135717303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18314404508850767423811535 27471606763276151135717303)
    ·
      refine ⟨41207410144914226703575955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27471606763276151135717303 41207410144914226703575955)
      ·
        refine ⟨61811115217371340055363933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41207410144914226703575955 61811115217371340055363933)
        ·
          refine ⟨23179168206514252520761475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61811115217371340055363933 23179168206514252520761475)
          ·
            refine ⟨34768752309771378781142213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23179168206514252520761475 34768752309771378781142213)
            ·
              refine ⟨6519141058082133521464165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34768752309771378781142213 6519141058082133521464165)
              ·
                refine ⟨1222338948390400035274531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6519141058082133521464165 1222338948390400035274531)
                ·
                  refine ⟨1833508422585600052911797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1222338948390400035274531 1833508422585600052911797)
                  ·
                    refine ⟨171891414617400004960481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1833508422585600052911797 171891414617400004960481)
                    ·
                      rfl

theorem cell23_1004272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 5].length) (baseStart_1004272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004272 prefixEnd_1004272 := by exact prefixLift 1004272
  have htrace : WordTrace (prefixWord ++ tailWord_1004272) baseStart_1004272 baseEnd_1004272 := by
    simpa [prefixWord, tailWord_1004272, baseEnd_1004272] using wordTrace_append hprefix tailTrace_1004272
  have hstable : (prefixWord ++ tailWord_1004272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004272).length < 2 ^ (prefixWord ++ tailWord_1004272).sum := by decide
  have hdescent : baseEnd_1004272 < baseStart_1004272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004319 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 1, 6]
def baseStart_1004319 : Nat := 118140960795 + 1004319 * 2 ^ 59
def prefixEnd_1004319 : Nat := 4983230072969 + 3 ^ 40 * 1004319 * 2
def baseEnd_1004319 : Nat := 171899459147653776997909

theorem tailTrace_1004319 : CollatzResearch.WordTrace tailWord_1004319 prefixEnd_1004319 171899459147653776997909 := by
  unfold tailWord_1004319
  simp only [CollatzResearch.WordTrace]
  refine ⟨36630523248531261874584011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24420348832354174583056007 36630523248531261874584011)
  ·
    refine ⟨54945784872796892811876017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36630523248531261874584011 54945784872796892811876017)
    ·
      refine ⟨41209338654597669608907013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54945784872796892811876017 41209338654597669608907013)
      ·
        refine ⟨7726750997737063051670065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41209338654597669608907013 7726750997737063051670065)
        ·
          refine ⟨5795063248302797288752549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7726750997737063051670065 5795063248302797288752549)
          ·
            refine ⟨1086574359056774491641103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5795063248302797288752549 1086574359056774491641103)
            ·
              refine ⟨1629861538585161737461655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1086574359056774491641103 1629861538585161737461655)
              ·
                refine ⟨2444792307877742606192483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1629861538585161737461655 2444792307877742606192483)
                ·
                  refine ⟨3667188461816613909288725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2444792307877742606192483 3667188461816613909288725)
                  ·
                    refine ⟨171899459147653776997909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3667188461816613909288725 171899459147653776997909)
                    ·
                      rfl

theorem cell23_1004319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 6].length) (baseStart_1004319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004319 prefixEnd_1004319 := by exact prefixLift 1004319
  have htrace : WordTrace (prefixWord ++ tailWord_1004319) baseStart_1004319 baseEnd_1004319 := by
    simpa [prefixWord, tailWord_1004319, baseEnd_1004319] using wordTrace_append hprefix tailTrace_1004319
  have hstable : (prefixWord ++ tailWord_1004319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004319).length < 2 ^ (prefixWord ++ tailWord_1004319).sum := by decide
  have hdescent : baseEnd_1004319 < baseStart_1004319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004349 : List Nat := [1, 4, 1, 4, 2, 2, 9]
def baseStart_1004349 : Nat := 118140960795 + 1004349 * 2 ^ 59
def prefixEnd_1004349 : Nat := 4983230072969 + 3 ^ 40 * 1004349 * 2
def baseEnd_1004349 : Nat := 6366836813118471773069

theorem tailTrace_1004349 : CollatzResearch.WordTrace tailWord_1004349 prefixEnd_1004349 6366836813118471773069 := by
  unfold tailWord_1004349
  simp only [CollatzResearch.WordTrace]
  refine ⟨36631617438422576998176101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24421078292281717998784067 36631617438422576998176101)
  ·
    refine ⟨6868428269704233187158019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36631617438422576998176101 6868428269704233187158019)
    ·
      refine ⟨10302642404556349780737029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6868428269704233187158019 10302642404556349780737029)
      ·
        refine ⟨1931745450854315583888193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10302642404556349780737029 1931745450854315583888193)
        ·
          refine ⟨1448809088140736687916145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1931745450854315583888193 1448809088140736687916145)
          ·
            refine ⟨1086606816105552515937109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1448809088140736687916145 1086606816105552515937109)
            ·
              refine ⟨6366836813118471773069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1086606816105552515937109 6366836813118471773069)
              ·
                rfl

theorem cell23_1004349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 9].length) (baseStart_1004349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004349 prefixEnd_1004349 := by exact prefixLift 1004349
  have htrace : WordTrace (prefixWord ++ tailWord_1004349) baseStart_1004349 baseEnd_1004349 := by
    simpa [prefixWord, tailWord_1004349, baseEnd_1004349] using wordTrace_append hprefix tailTrace_1004349
  have hstable : (prefixWord ++ tailWord_1004349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004349).length < 2 ^ (prefixWord ++ tailWord_1004349).sum := by decide
  have hdescent : baseEnd_1004349 < baseStart_1004349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004360 : List Nat := [2, 1, 3, 1, 1, 3, 5, 2, 1, 2, 2]
def baseStart_1004360 : Nat := 118140960795 + 1004360 * 2 ^ 59
def prefixEnd_1004360 : Nat := 4983230072969 + 3 ^ 40 * 1004360 * 2
def baseEnd_1004360 : Nat := 515719430149795670581039

theorem tailTrace_1004360 : CollatzResearch.WordTrace tailWord_1004360 prefixEnd_1004360 515719430149795670581039 := by
  unfold tailWord_1004360
  simp only [CollatzResearch.WordTrace]
  refine ⟨18316009320691362938413267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24421345760921817251217689 18316009320691362938413267)
  ·
    refine ⟨27474013981037044407619901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18316009320691362938413267 27474013981037044407619901)
    ·
      refine ⟨10302755242888891652857463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27474013981037044407619901 10302755242888891652857463)
      ·
        refine ⟨15454132864333337479286195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10302755242888891652857463 15454132864333337479286195)
        ·
          refine ⟨23181199296500006218929293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454132864333337479286195 23181199296500006218929293)
          ·
            refine ⟨8692949736187502332098485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23181199296500006218929293 8692949736187502332098485)
            ·
              refine ⟨814964037767578343634233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8692949736187502332098485 814964037767578343634233)
              ·
                refine ⟨611223028325683757725675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814964037767578343634233 611223028325683757725675)
                ·
                  refine ⟨916834542488525636588513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611223028325683757725675 916834542488525636588513)
                  ·
                    refine ⟨687625906866394227441385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 916834542488525636588513 687625906866394227441385)
                    ·
                      refine ⟨515719430149795670581039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687625906866394227441385 515719430149795670581039)
                      ·
                        rfl

theorem cell23_1004360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 5, 2, 1, 2, 2].length) (baseStart_1004360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004360 prefixEnd_1004360 := by exact prefixLift 1004360
  have htrace : WordTrace (prefixWord ++ tailWord_1004360) baseStart_1004360 baseEnd_1004360 := by
    simpa [prefixWord, tailWord_1004360, baseEnd_1004360] using wordTrace_append hprefix tailTrace_1004360
  have hstable : (prefixWord ++ tailWord_1004360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004360).length < 2 ^ (prefixWord ++ tailWord_1004360).sum := by decide
  have hdescent : baseEnd_1004360 < baseStart_1004360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004412 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_1004412 : Nat := 118140960795 + 1004412 * 2 ^ 59
def prefixEnd_1004412 : Nat := 4983230072969 + 3 ^ 40 * 1004412 * 2
def baseEnd_1004412 : Nat := 515746131143829467130799

theorem tailTrace_1004412 : CollatzResearch.WordTrace tailWord_1004412 prefixEnd_1004412 515746131143829467130799 := by
  unfold tailWord_1004412
  simp only [CollatzResearch.WordTrace]
  refine ⟨18316957618597169378859745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24422610158129559171812993 18316957618597169378859745)
  ·
    refine ⟨13737718213947877034144809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18316957618597169378859745 13737718213947877034144809)
    ·
      refine ⟨10303288660460907775608607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13737718213947877034144809 10303288660460907775608607)
      ·
        refine ⟨15454932990691361663412911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10303288660460907775608607 15454932990691361663412911)
        ·
          refine ⟨23182399486037042495119367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15454932990691361663412911 23182399486037042495119367)
          ·
            refine ⟨34773599229055563742679051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23182399486037042495119367 34773599229055563742679051)
            ·
              refine ⟨52160398843583345614018577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34773599229055563742679051 52160398843583345614018577)
              ·
                refine ⟨39120299132687509210513933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52160398843583345614018577 39120299132687509210513933)
                ·
                  refine ⟨14670112174757815953942725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39120299132687509210513933 14670112174757815953942725)
                  ·
                    refine ⟨2750646032767090491364261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14670112174757815953942725 2750646032767090491364261)
                    ·
                      refine ⟨515746131143829467130799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2750646032767090491364261 515746131143829467130799)
                      ·
                        rfl

theorem cell23_1004412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_1004412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004412 prefixEnd_1004412 := by exact prefixLift 1004412
  have htrace : WordTrace (prefixWord ++ tailWord_1004412) baseStart_1004412 baseEnd_1004412 := by
    simpa [prefixWord, tailWord_1004412, baseEnd_1004412] using wordTrace_append hprefix tailTrace_1004412
  have hstable : (prefixWord ++ tailWord_1004412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004412).length < 2 ^ (prefixWord ++ tailWord_1004412).sum := by decide
  have hdescent : baseEnd_1004412 < baseStart_1004412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004459 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 4, 5, 2]
def baseStart_1004459 : Nat := 118140960795 + 1004459 * 2 ^ 59
def prefixEnd_1004459 : Nat := 4983230072969 + 3 ^ 40 * 1004459 * 2
def baseEnd_1004459 : Nat := 515770264734590783243083

theorem tailTrace_1004459 : CollatzResearch.WordTrace tailWord_1004459 prefixEnd_1004459 515770264734590783243083 := by
  unfold tailWord_1004459
  simp only [CollatzResearch.WordTrace]
  refine ⟨36635629468024065784680431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24423752978682710523120287 36635629468024065784680431)
  ·
    refine ⟨54953444202036098677020647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36635629468024065784680431 54953444202036098677020647)
    ·
      refine ⟨82430166303054148015530971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54953444202036098677020647 82430166303054148015530971)
      ·
        refine ⟨123645249454581222023296457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82430166303054148015530971 123645249454581222023296457)
        ·
          refine ⟨92733937090935916517472343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123645249454581222023296457 92733937090935916517472343)
          ·
            refine ⟨139100905636403874776208515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92733937090935916517472343 139100905636403874776208515)
            ·
              refine ⟨208651358454605812164312773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139100905636403874776208515 208651358454605812164312773)
              ·
                refine ⟨39122129710238589780808645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208651358454605812164312773 39122129710238589780808645)
                ·
                  refine ⟨7335399320669735583901621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39122129710238589780808645 7335399320669735583901621)
                  ·
                    refine ⟨687693686312787710990777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7335399320669735583901621 687693686312787710990777)
                    ·
                      refine ⟨515770264734590783243083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687693686312787710990777 515770264734590783243083)
                      ·
                        rfl

theorem cell23_1004459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5, 2].length) (baseStart_1004459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004459 prefixEnd_1004459 := by exact prefixLift 1004459
  have htrace : WordTrace (prefixWord ++ tailWord_1004459) baseStart_1004459 baseEnd_1004459 := by
    simpa [prefixWord, tailWord_1004459, baseEnd_1004459] using wordTrace_append hprefix tailTrace_1004459
  have hstable : (prefixWord ++ tailWord_1004459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004459).length < 2 ^ (prefixWord ++ tailWord_1004459).sum := by decide
  have hdescent : baseEnd_1004459 < baseStart_1004459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004469 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1004469 : Nat := 118140960795 + 1004469 * 2 ^ 59
def prefixEnd_1004469 : Nat := 4983230072969 + 3 ^ 40 * 1004469 * 2
def baseEnd_1004469 : Nat := 171925133180378581372679

theorem tailTrace_1004469 : CollatzResearch.WordTrace tailWord_1004469 prefixEnd_1004469 171925133180378581372679 := by
  unfold tailWord_1004469
  simp only [CollatzResearch.WordTrace]
  refine ⟨36635994197987837492544461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24423996131991891661696307 36635994197987837492544461)
  ·
    refine ⟨13738497824245439059704173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36635994197987837492544461 13738497824245439059704173)
    ·
      refine ⟨5151936684092039647389065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13738497824245439059704173 5151936684092039647389065)
      ·
        refine ⟨3863952513069029735541799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5151936684092039647389065 3863952513069029735541799)
        ·
          refine ⟨5795928769603544603312699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3863952513069029735541799 5795928769603544603312699)
          ·
            refine ⟨8693893154405316904969049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5795928769603544603312699 8693893154405316904969049)
            ·
              refine ⟨6520419865803987678726787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8693893154405316904969049 6520419865803987678726787)
              ·
                refine ⟨9780629798705981518090181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6520419865803987678726787 9780629798705981518090181)
                ·
                  refine ⟨1833868087257371534641909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9780629798705981518090181 1833868087257371534641909)
                  ·
                    refine ⟨171925133180378581372679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1833868087257371534641909 171925133180378581372679)
                    ·
                      rfl

theorem cell23_1004469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1004469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004469 prefixEnd_1004469 := by exact prefixLift 1004469
  have htrace : WordTrace (prefixWord ++ tailWord_1004469) baseStart_1004469 baseEnd_1004469 := by
    simpa [prefixWord, tailWord_1004469, baseEnd_1004469] using wordTrace_append hprefix tailTrace_1004469
  have hstable : (prefixWord ++ tailWord_1004469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004469).length < 2 ^ (prefixWord ++ tailWord_1004469).sum := by decide
  have hdescent : baseEnd_1004469 < baseStart_1004469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004484 : List Nat := [2, 3, 3, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1004484 : Nat := 118140960795 + 1004484 * 2 ^ 59
def prefixEnd_1004484 : Nat := 4983230072969 + 3 ^ 40 * 1004484 * 2
def baseEnd_1004484 : Nat := 515783101750953185430469

theorem tailTrace_1004484 : CollatzResearch.WordTrace tailWord_1004484 prefixEnd_1004484 515783101750953185430469 := by
  unfold tailWord_1004484
  simp only [CollatzResearch.WordTrace]
  refine ⟨18318270646466747527170253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24424360861955663369560337 18318270646466747527170253)
  ·
    refine ⟨6869351492425030322688845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18318270646466747527170253 6869351492425030322688845)
    ·
      refine ⟨2576006809659386371008317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6869351492425030322688845 2576006809659386371008317)
      ·
        refine ⟨966002553622269889128119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2576006809659386371008317 966002553622269889128119)
        ·
          refine ⟨1449003830433404833692179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 966002553622269889128119 1449003830433404833692179)
          ·
            refine ⟨2173505745650107250538269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449003830433404833692179 2173505745650107250538269)
            ·
              refine ⟨815064654618790218951851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2173505745650107250538269 815064654618790218951851)
              ·
                refine ⟨1222596981928185328427777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815064654618790218951851 1222596981928185328427777)
                ·
                  refine ⟨916947736446138996320833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222596981928185328427777 916947736446138996320833)
                  ·
                    refine ⟨687710802334604247240625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 916947736446138996320833 687710802334604247240625)
                    ·
                      refine ⟨515783101750953185430469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687710802334604247240625 515783101750953185430469)
                      ·
                        rfl

theorem cell23_1004484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1004484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004484 prefixEnd_1004484 := by exact prefixLift 1004484
  have htrace : WordTrace (prefixWord ++ tailWord_1004484) baseStart_1004484 baseEnd_1004484 := by
    simpa [prefixWord, tailWord_1004484, baseEnd_1004484] using wordTrace_append hprefix tailTrace_1004484
  have hstable : (prefixWord ++ tailWord_1004484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004484).length < 2 ^ (prefixWord ++ tailWord_1004484).sum := by decide
  have hdescent : baseEnd_1004484 < baseStart_1004484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004529 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 8]
def baseStart_1004529 : Nat := 118140960795 + 1004529 * 2 ^ 59
def prefixEnd_1004529 : Nat := 4983230072969 + 3 ^ 40 * 1004529 * 2
def baseEnd_1004529 : Nat := 57311800931156167707529

theorem tailTrace_1004529 : CollatzResearch.WordTrace tailWord_1004529 prefixEnd_1004529 57311800931156167707529 := by
  unfold tailWord_1004529
  simp only [CollatzResearch.WordTrace]
  refine ⟨36638182577770467739728641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24425455051846978493152427 36638182577770467739728641)
  ·
    refine ⟨27478636933327850804796481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36638182577770467739728641 27478636933327850804796481)
    ·
      refine ⟨20608977699995888103597361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27478636933327850804796481 20608977699995888103597361)
      ·
        refine ⟨15456733274996916077698021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20608977699995888103597361 15456733274996916077698021)
        ·
          refine ⟨2898137489061921764568379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15456733274996916077698021 2898137489061921764568379)
          ·
            refine ⟨4347206233592882646852569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898137489061921764568379 4347206233592882646852569)
            ·
              refine ⟨3260404675194661985139427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4347206233592882646852569 3260404675194661985139427)
              ·
                refine ⟨4890607012791992977709141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3260404675194661985139427 4890607012791992977709141)
                ·
                  refine ⟨57311800931156167707529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4890607012791992977709141 57311800931156167707529)
                  ·
                    rfl

theorem cell23_1004529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_1004529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004529 prefixEnd_1004529 := by exact prefixLift 1004529
  have htrace : WordTrace (prefixWord ++ tailWord_1004529) baseStart_1004529 baseEnd_1004529 := by
    simpa [prefixWord, tailWord_1004529, baseEnd_1004529] using wordTrace_append hprefix tailTrace_1004529
  have hstable : (prefixWord ++ tailWord_1004529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004529).length < 2 ^ (prefixWord ++ tailWord_1004529).sum := by decide
  have hdescent : baseEnd_1004529 < baseStart_1004529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004599 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1004599 : Nat := 118140960795 + 1004599 * 2 ^ 59
def prefixEnd_1004599 : Nat := 4983230072969 + 3 ^ 40 * 1004599 * 2
def baseEnd_1004599 : Nat := 515842152026220235492439

theorem tailTrace_1004599 : CollatzResearch.WordTrace tailWord_1004599 prefixEnd_1004599 515842152026220235492439 := by
  unfold tailWord_1004599
  simp only [CollatzResearch.WordTrace]
  refine ⟨36640735687516869694776851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24427157125011246463184567 36640735687516869694776851)
  ·
    refine ⟨54961103531275304542165277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36640735687516869694776851 54961103531275304542165277)
    ·
      refine ⟨20610413824228239203311979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54961103531275304542165277 20610413824228239203311979)
      ·
        refine ⟨30915620736342358804967969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20610413824228239203311979 30915620736342358804967969)
        ·
          refine ⟨23186715552256769103725977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30915620736342358804967969 23186715552256769103725977)
          ·
            refine ⟨17390036664192576827794483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23186715552256769103725977 17390036664192576827794483)
            ·
              refine ⟨26085054996288865241691725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17390036664192576827794483 26085054996288865241691725)
              ·
                refine ⟨9781895623608324465634397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26085054996288865241691725 9781895623608324465634397)
                ·
                  refine ⟨3668210858853121674612899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9781895623608324465634397 3668210858853121674612899)
                  ·
                    refine ⟨5502316288279682511919349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3668210858853121674612899 5502316288279682511919349)
                    ·
                      refine ⟨515842152026220235492439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5502316288279682511919349 515842152026220235492439)
                      ·
                        rfl

theorem cell23_1004599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1004599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004599 prefixEnd_1004599 := by exact prefixLift 1004599
  have htrace : WordTrace (prefixWord ++ tailWord_1004599) baseStart_1004599 baseEnd_1004599 := by
    simpa [prefixWord, tailWord_1004599, baseEnd_1004599] using wordTrace_append hprefix tailTrace_1004599
  have hstable : (prefixWord ++ tailWord_1004599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004599).length < 2 ^ (prefixWord ++ tailWord_1004599).sum := by decide
  have hdescent : baseEnd_1004599 < baseStart_1004599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004613 : List Nat := [1, 3, 1, 1, 1, 3, 3, 1, 5, 2, 2]
def baseStart_1004613 : Nat := 118140960795 + 1004613 * 2 ^ 59
def prefixEnd_1004613 : Nat := 4983230072969 + 3 ^ 40 * 1004613 * 2
def baseEnd_1004613 : Nat := 515849340755383180717375

theorem tailTrace_1004613 : CollatzResearch.WordTrace tailWord_1004613 prefixEnd_1004613 515849340755383180717375 := by
  unfold tailWord_1004613
  simp only [CollatzResearch.WordTrace]
  refine ⟨36641246309466150085786493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24427497539644100057190995 36641246309466150085786493)
  ·
    refine ⟨13740467366049806282169935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36641246309466150085786493 13740467366049806282169935)
    ·
      refine ⟨20610701049074709423254903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13740467366049806282169935 20610701049074709423254903)
      ·
        refine ⟨30916051573612064134882355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20610701049074709423254903 30916051573612064134882355)
        ·
          refine ⟨46374077360418096202323533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30916051573612064134882355 46374077360418096202323533)
          ·
            refine ⟨17390279010156786075871325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46374077360418096202323533 17390279010156786075871325)
            ·
              refine ⟨6521354628808794778451747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17390279010156786075871325 6521354628808794778451747)
              ·
                refine ⟨9782031943213192167677621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521354628808794778451747 9782031943213192167677621)
                ·
                  refine ⟨917065494676236765719777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9782031943213192167677621 917065494676236765719777)
                  ·
                    refine ⟨687799121007177574289833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 917065494676236765719777 687799121007177574289833)
                    ·
                      refine ⟨515849340755383180717375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687799121007177574289833 515849340755383180717375)
                      ·
                        rfl

theorem cell23_1004613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 1, 5, 2, 2].length) (baseStart_1004613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004613 prefixEnd_1004613 := by exact prefixLift 1004613
  have htrace : WordTrace (prefixWord ++ tailWord_1004613) baseStart_1004613 baseEnd_1004613 := by
    simpa [prefixWord, tailWord_1004613, baseEnd_1004613] using wordTrace_append hprefix tailTrace_1004613
  have hstable : (prefixWord ++ tailWord_1004613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004613).length < 2 ^ (prefixWord ++ tailWord_1004613).sum := by decide
  have hdescent : baseEnd_1004613 < baseStart_1004613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004616 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 3, 2, 3]
def baseStart_1004616 : Nat := 118140960795 + 1004616 * 2 ^ 59
def prefixEnd_1004616 : Nat := 4983230072969 + 3 ^ 40 * 1004616 * 2
def baseEnd_1004616 : Nat := 515850881197346668979861

theorem tailTrace_1004616 : CollatzResearch.WordTrace tailWord_1004616 prefixEnd_1004616 515850881197346668979861 := by
  unfold tailWord_1004616
  simp only [CollatzResearch.WordTrace]
  refine ⟨18320677864227640799072851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24427570485636854398763801 18320677864227640799072851)
  ·
    refine ⟨27481016796341461198609277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18320677864227640799072851 27481016796341461198609277)
    ·
      refine ⟨10305381298628047949478479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27481016796341461198609277 10305381298628047949478479)
      ·
        refine ⟨15458071947942071924217719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10305381298628047949478479 15458071947942071924217719)
        ·
          refine ⟨23187107921913107886326579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15458071947942071924217719 23187107921913107886326579)
          ·
            refine ⟨34780661882869661829489869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23187107921913107886326579 34780661882869661829489869)
            ·
              refine ⟨13042748206076123186058701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34780661882869661829489869 13042748206076123186058701)
              ·
                refine ⟨4891030577278546194772013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13042748206076123186058701 4891030577278546194772013)
                ·
                  refine ⟨1834136466479454823039505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4891030577278546194772013 1834136466479454823039505)
                  ·
                    refine ⟨1375602349859591117279629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1834136466479454823039505 1375602349859591117279629)
                    ·
                      refine ⟨515850881197346668979861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1375602349859591117279629 515850881197346668979861)
                      ·
                        rfl

theorem cell23_1004616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 3, 2, 3].length) (baseStart_1004616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004616 prefixEnd_1004616 := by exact prefixLift 1004616
  have htrace : WordTrace (prefixWord ++ tailWord_1004616) baseStart_1004616 baseEnd_1004616 := by
    simpa [prefixWord, tailWord_1004616, baseEnd_1004616] using wordTrace_append hprefix tailTrace_1004616
  have hstable : (prefixWord ++ tailWord_1004616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004616).length < 2 ^ (prefixWord ++ tailWord_1004616).sum := by decide
  have hdescent : baseEnd_1004616 < baseStart_1004616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004647 : List Nat := [1, 1, 5, 1, 1, 3, 2, 4, 1, 2, 2]
def baseStart_1004647 : Nat := 118140960795 + 1004647 * 2 ^ 59
def prefixEnd_1004647 : Nat := 4983230072969 + 3 ^ 40 * 1004647 * 2
def baseEnd_1004647 : Nat := 515866799097636047692219

theorem tailTrace_1004647 : CollatzResearch.WordTrace tailWord_1004647 prefixEnd_1004647 515866799097636047692219 := by
  unfold tailWord_1004647
  simp only [CollatzResearch.WordTrace]
  refine ⟨36642486391342973892524195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24428324260895315928349463 36642486391342973892524195)
  ·
    refine ⟨54963729587014460838786293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36642486391342973892524195 54963729587014460838786293)
    ·
      refine ⟨5152849648782605703636215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 54963729587014460838786293 5152849648782605703636215)
      ·
        refine ⟨7729274473173908555454323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152849648782605703636215 7729274473173908555454323)
        ·
          refine ⟨11593911709760862833181485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7729274473173908555454323 11593911709760862833181485)
          ·
            refine ⟨4347716891160323562443057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11593911709760862833181485 4347716891160323562443057)
            ·
              refine ⟨3260787668370242671832293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4347716891160323562443057 3260787668370242671832293)
              ·
                refine ⟨611397687819420500968555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3260787668370242671832293 611397687819420500968555)
                ·
                  refine ⟨917096531729130751452833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611397687819420500968555 917096531729130751452833)
                  ·
                    refine ⟨687822398796848063589625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 917096531729130751452833 687822398796848063589625)
                    ·
                      refine ⟨515866799097636047692219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687822398796848063589625 515866799097636047692219)
                      ·
                        rfl

theorem cell23_1004647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 4, 1, 2, 2].length) (baseStart_1004647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004647 prefixEnd_1004647 := by exact prefixLift 1004647
  have htrace : WordTrace (prefixWord ++ tailWord_1004647) baseStart_1004647 baseEnd_1004647 := by
    simpa [prefixWord, tailWord_1004647, baseEnd_1004647] using wordTrace_append hprefix tailTrace_1004647
  have hstable : (prefixWord ++ tailWord_1004647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004647).length < 2 ^ (prefixWord ++ tailWord_1004647).sum := by decide
  have hdescent : baseEnd_1004647 < baseStart_1004647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004659 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5]
def baseStart_1004659 : Nat := 118140960795 + 1004659 * 2 ^ 59
def prefixEnd_1004659 : Nat := 4983230072969 + 3 ^ 40 * 1004659 * 2
def baseEnd_1004659 : Nat := 515872960865490000742163

theorem tailTrace_1004659 : CollatzResearch.WordTrace tailWord_1004659 prefixEnd_1004659 515872960865490000742163 := by
  unfold tailWord_1004659
  simp only [CollatzResearch.WordTrace]
  refine ⟨36642924067299499941961031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24428616044866333294640687 36642924067299499941961031)
  ·
    refine ⟨54964386100949249912941547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36642924067299499941961031 54964386100949249912941547)
    ·
      refine ⟨82446579151423874869412321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54964386100949249912941547 82446579151423874869412321)
      ·
        refine ⟨61834934363567906152059241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82446579151423874869412321 61834934363567906152059241)
        ·
          refine ⟨46376200772675929614044431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61834934363567906152059241 46376200772675929614044431)
          ·
            refine ⟨69564301159013894421066647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46376200772675929614044431 69564301159013894421066647)
            ·
              refine ⟨104346451738520841631599971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69564301159013894421066647 104346451738520841631599971)
              ·
                refine ⟨156519677607781262447399957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104346451738520841631599971 156519677607781262447399957)
                ·
                  refine ⟨7336859887864746677221873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156519677607781262447399957 7336859887864746677221873)
                  ·
                    refine ⟨5502644915898560007916405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336859887864746677221873 5502644915898560007916405)
                    ·
                      refine ⟨515872960865490000742163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5502644915898560007916405 515872960865490000742163)
                      ·
                        rfl

theorem cell23_1004659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_1004659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004659 prefixEnd_1004659 := by exact prefixLift 1004659
  have htrace : WordTrace (prefixWord ++ tailWord_1004659) baseStart_1004659 baseEnd_1004659 := by
    simpa [prefixWord, tailWord_1004659, baseEnd_1004659] using wordTrace_append hprefix tailTrace_1004659
  have hstable : (prefixWord ++ tailWord_1004659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004659).length < 2 ^ (prefixWord ++ tailWord_1004659).sum := by decide
  have hdescent : baseEnd_1004659 < baseStart_1004659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004676 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_1004676 : Nat := 118140960795 + 1004676 * 2 ^ 59
def prefixEnd_1004676 : Nat := 4983230072969 + 3 ^ 40 * 1004676 * 2
def baseEnd_1004676 : Nat := 515881690036616434229585

theorem tailTrace_1004676 : CollatzResearch.WordTrace tailWord_1004676 prefixEnd_1004676 515881690036616434229585 := by
  unfold tailWord_1004676
  simp only [CollatzResearch.WordTrace]
  refine ⟨18321772054118955922664941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24429029405491941230219921 18321772054118955922664941)
  ·
    refine ⟨6870664520294608470999353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18321772054118955922664941 6870664520294608470999353)
    ·
      refine ⟨5152998390220956353249515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6870664520294608470999353 5152998390220956353249515)
      ·
        refine ⟨7729497585331434529874273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5152998390220956353249515 7729497585331434529874273)
        ·
          refine ⟨5797123188998575897405705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7729497585331434529874273 5797123188998575897405705)
          ·
            refine ⟨4347842391748931923054279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5797123188998575897405705 4347842391748931923054279)
            ·
              refine ⟨6521763587623397884581419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4347842391748931923054279 6521763587623397884581419)
              ·
                refine ⟨9782645381435096826872129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6521763587623397884581419 9782645381435096826872129)
                ·
                  refine ⟨7336984036076322620154097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9782645381435096826872129 7336984036076322620154097)
                  ·
                    refine ⟨5502738027057241965115573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7336984036076322620154097 5502738027057241965115573)
                    ·
                      refine ⟨515881690036616434229585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5502738027057241965115573 515881690036616434229585)
                      ·
                        rfl

theorem cell23_1004676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_1004676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004676 prefixEnd_1004676 := by exact prefixLift 1004676
  have htrace : WordTrace (prefixWord ++ tailWord_1004676) baseStart_1004676 baseEnd_1004676 := by
    simpa [prefixWord, tailWord_1004676, baseEnd_1004676] using wordTrace_append hprefix tailTrace_1004676
  have hstable : (prefixWord ++ tailWord_1004676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004676).length < 2 ^ (prefixWord ++ tailWord_1004676).sum := by decide
  have hdescent : baseEnd_1004676 < baseStart_1004676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004699 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6]
def baseStart_1004699 : Nat := 118140960795 + 1004699 * 2 ^ 59
def prefixEnd_1004699 : Nat := 4983230072969 + 3 ^ 40 * 1004699 * 2
def baseEnd_1004699 : Nat := 515893500091669844241979

theorem tailTrace_1004699 : CollatzResearch.WordTrace tailWord_1004699 prefixEnd_1004699 515893500091669844241979 := by
  unfold tailWord_1004699
  simp only [CollatzResearch.WordTrace]
  refine ⟨36644382987154586773417151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24429588658103057848944767 36644382987154586773417151)
  ·
    refine ⟨54966574480731880160125727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36644382987154586773417151 54966574480731880160125727)
    ·
      refine ⟨82449861721097820240188591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54966574480731880160125727 82449861721097820240188591)
      ·
        refine ⟨123674792581646730360282887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82449861721097820240188591 123674792581646730360282887)
        ·
          refine ⟨185512188872470095540424331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123674792581646730360282887 185512188872470095540424331)
          ·
            refine ⟨278268283308705143310636497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185512188872470095540424331 278268283308705143310636497)
            ·
              refine ⟨208701212481528857482977373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278268283308705143310636497 208701212481528857482977373)
              ·
                refine ⟨78262954680573321556116515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208701212481528857482977373 78262954680573321556116515)
                ·
                  refine ⟨117394432020859982334174773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78262954680573321556116515 117394432020859982334174773)
                  ·
                    refine ⟨11005728001955623343828885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117394432020859982334174773 11005728001955623343828885)
                    ·
                      refine ⟨515893500091669844241979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11005728001955623343828885 515893500091669844241979)
                      ·
                        rfl

theorem cell23_1004699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 6].length) (baseStart_1004699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004699 prefixEnd_1004699 := by exact prefixLift 1004699
  have htrace : WordTrace (prefixWord ++ tailWord_1004699) baseStart_1004699 baseEnd_1004699 := by
    simpa [prefixWord, tailWord_1004699, baseEnd_1004699] using wordTrace_append hprefix tailTrace_1004699
  have hstable : (prefixWord ++ tailWord_1004699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004699).length < 2 ^ (prefixWord ++ tailWord_1004699).sum := by decide
  have hdescent : baseEnd_1004699 < baseStart_1004699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004714 : List Nat := [3, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1004714 : Nat := 118140960795 + 1004714 * 2 ^ 59
def prefixEnd_1004714 : Nat := 4983230072969 + 3 ^ 40 * 1004714 * 2
def baseEnd_1004714 : Nat := 515901202301487285554411

theorem tailTrace_1004714 : CollatzResearch.WordTrace tailWord_1004714 prefixEnd_1004714 515901202301487285554411 := by
  unfold tailWord_1004714
  simp only [CollatzResearch.WordTrace]
  refine ⟨9161232520525061083803299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24429953388066829556808797 9161232520525061083803299)
  ·
    refine ⟨13741848780787591625704949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9161232520525061083803299 13741848780787591625704949)
    ·
      refine ⟨1288298323198836714909839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13741848780787591625704949 1288298323198836714909839)
      ·
        refine ⟨1932447484798255072364759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288298323198836714909839 1932447484798255072364759)
        ·
          refine ⟨2898671227197382608547139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932447484798255072364759 2898671227197382608547139)
          ·
            refine ⟨4348006840796073912820709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898671227197382608547139 4348006840796073912820709)
            ·
              refine ⟨815251282649263858653883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4348006840796073912820709 815251282649263858653883)
              ·
                refine ⟨1222876923973895787980825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815251282649263858653883 1222876923973895787980825)
                ·
                  refine ⟨917157692980421840985619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222876923973895787980825 917157692980421840985619)
                  ·
                    refine ⟨1375736539470632761478429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917157692980421840985619 1375736539470632761478429)
                    ·
                      refine ⟨515901202301487285554411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1375736539470632761478429 515901202301487285554411)
                      ·
                        rfl

theorem cell23_1004714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1004714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004714 prefixEnd_1004714 := by exact prefixLift 1004714
  have htrace : WordTrace (prefixWord ++ tailWord_1004714) baseStart_1004714 baseEnd_1004714 := by
    simpa [prefixWord, tailWord_1004714, baseEnd_1004714] using wordTrace_append hprefix tailTrace_1004714
  have hstable : (prefixWord ++ tailWord_1004714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004714).length < 2 ^ (prefixWord ++ tailWord_1004714).sum := by decide
  have hdescent : baseEnd_1004714 < baseStart_1004714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004720 : List Nat := [2, 1, 1, 1, 2, 1, 2, 7, 2, 2, 2]
def baseStart_1004720 : Nat := 118140960795 + 1004720 * 2 ^ 59
def prefixEnd_1004720 : Nat := 4983230072969 + 3 ^ 40 * 1004720 * 2
def baseEnd_1004720 : Nat := 515904283185414262079383

theorem tailTrace_1004720 : CollatzResearch.WordTrace tailWord_1004720 prefixEnd_1004720 515904283185414262079383 := by
  unfold tailWord_1004720
  simp only [CollatzResearch.WordTrace]
  refine ⟨18322574460039253679965807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24430099280052338239954409 18322574460039253679965807)
  ·
    refine ⟨27483861690058880519948711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18322574460039253679965807 27483861690058880519948711)
    ·
      refine ⟨41225792535088320779923067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27483861690058880519948711 41225792535088320779923067)
      ·
        refine ⟨61838688802632481169884601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41225792535088320779923067 61838688802632481169884601)
        ·
          refine ⟨46379016601974360877413451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61838688802632481169884601 46379016601974360877413451)
          ·
            refine ⟨69568524902961541316120177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46379016601974360877413451 69568524902961541316120177)
            ·
              refine ⟨52176393677221155987090133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69568524902961541316120177 52176393677221155987090133)
              ·
                refine ⟨1222884226809870843447425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 52176393677221155987090133 1222884226809870843447425)
                ·
                  refine ⟨917163170107403132585569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1222884226809870843447425 917163170107403132585569)
                  ·
                    refine ⟨687872377580552349439177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 917163170107403132585569 687872377580552349439177)
                    ·
                      refine ⟨515904283185414262079383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687872377580552349439177 515904283185414262079383)
                      ·
                        rfl

theorem cell23_1004720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 7, 2, 2, 2].length) (baseStart_1004720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004720 prefixEnd_1004720 := by exact prefixLift 1004720
  have htrace : WordTrace (prefixWord ++ tailWord_1004720) baseStart_1004720 baseEnd_1004720 := by
    simpa [prefixWord, tailWord_1004720, baseEnd_1004720] using wordTrace_append hprefix tailTrace_1004720
  have hstable : (prefixWord ++ tailWord_1004720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004720).length < 2 ^ (prefixWord ++ tailWord_1004720).sum := by decide
  have hdescent : baseEnd_1004720 < baseStart_1004720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004737 : List Nat := [1, 2, 6, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1004737 : Nat := 118140960795 + 1004737 * 2 ^ 59
def prefixEnd_1004737 : Nat := 4983230072969 + 3 ^ 40 * 1004737 * 2
def baseEnd_1004737 : Nat := 515913012356540695566805

theorem tailTrace_1004737 : CollatzResearch.WordTrace tailWord_1004737 prefixEnd_1004737 515913012356540695566805 := by
  unfold tailWord_1004737
  simp only [CollatzResearch.WordTrace]
  refine ⟨36645768961016919263300465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24430512640677946175533643 36645768961016919263300465)
  ·
    refine ⟨27484326720762689447475349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36645768961016919263300465 27484326720762689447475349)
    ·
      refine ⟨1288327815035751067850407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27484326720762689447475349 1288327815035751067850407)
      ·
        refine ⟨1932491722553626601775611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288327815035751067850407 1932491722553626601775611)
        ·
          refine ⟨2898737583830439902663417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932491722553626601775611 2898737583830439902663417)
          ·
            refine ⟨2174053187872829926997563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2898737583830439902663417 2174053187872829926997563)
            ·
              refine ⟨3261079781809244890496345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174053187872829926997563 3261079781809244890496345)
              ·
                refine ⟨2445809836356933667872259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3261079781809244890496345 2445809836356933667872259)
                ·
                  refine ⟨3668714754535400501808389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445809836356933667872259 3668714754535400501808389)
                  ·
                    refine ⟨687884016475387594089073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3668714754535400501808389 687884016475387594089073)
                    ·
                      refine ⟨515913012356540695566805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687884016475387594089073 515913012356540695566805)
                      ·
                        rfl

theorem cell23_1004737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1004737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004737 prefixEnd_1004737 := by exact prefixLift 1004737
  have htrace : WordTrace (prefixWord ++ tailWord_1004737) baseStart_1004737 baseEnd_1004737 := by
    simpa [prefixWord, tailWord_1004737, baseEnd_1004737] using wordTrace_append hprefix tailTrace_1004737
  have hstable : (prefixWord ++ tailWord_1004737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004737).length < 2 ^ (prefixWord ++ tailWord_1004737).sum := by decide
  have hdescent : baseEnd_1004737 < baseStart_1004737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004760 : List Nat := [2, 1, 2, 2, 5, 1, 1, 4, 5]
def baseStart_1004760 : Nat := 118140960795 + 1004760 * 2 ^ 59
def prefixEnd_1004760 : Nat := 4983230072969 + 3 ^ 40 * 1004760 * 2
def baseEnd_1004760 : Nat := 57324980267954900619911

theorem tailTrace_1004760 : CollatzResearch.WordTrace tailWord_1004760 prefixEnd_1004760 57324980267954900619911 := by
  unfold tailWord_1004760
  simp only [CollatzResearch.WordTrace]
  refine ⟨18323303919966797095693867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24431071893289062794258489 18323303919966797095693867)
  ·
    refine ⟨27484955879950195643540801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18323303919966797095693867 27484955879950195643540801)
    ·
      refine ⟨20613716909962646732655601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27484955879950195643540801 20613716909962646732655601)
      ·
        refine ⟨15460287682471985049491701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20613716909962646732655601 15460287682471985049491701)
        ·
          refine ⟨1449401970231748598389847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15460287682471985049491701 1449401970231748598389847)
          ·
            refine ⟨2174102955347622897584771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449401970231748598389847 2174102955347622897584771)
            ·
              refine ⟨3261154433021434346377157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174102955347622897584771 3261154433021434346377157)
              ·
                refine ⟨611466456191518939945717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3261154433021434346377157 611466456191518939945717)
                ·
                  refine ⟨57324980267954900619911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 611466456191518939945717 57324980267954900619911)
                  ·
                    rfl

theorem cell23_1004760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 4, 5].length) (baseStart_1004760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004760 prefixEnd_1004760 := by exact prefixLift 1004760
  have htrace : WordTrace (prefixWord ++ tailWord_1004760) baseStart_1004760 baseEnd_1004760 := by
    simpa [prefixWord, tailWord_1004760, baseEnd_1004760] using wordTrace_append hprefix tailTrace_1004760
  have hstable : (prefixWord ++ tailWord_1004760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004760).length < 2 ^ (prefixWord ++ tailWord_1004760).sum := by decide
  have hdescent : baseEnd_1004760 < baseStart_1004760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004793 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 1, 6, 2]
def baseStart_1004793 : Nat := 118140960795 + 1004793 * 2 ^ 59
def prefixEnd_1004793 : Nat := 4983230072969 + 3 ^ 40 * 1004793 * 2
def baseEnd_1004793 : Nat := 515941767273192476466547

theorem tailTrace_1004793 : CollatzResearch.WordTrace tailWord_1004793 prefixEnd_1004793 515941767273192476466547 := by
  unfold tailWord_1004793
  simp only [CollatzResearch.WordTrace]
  refine ⟨36647811448814040827339033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24431874299209360551559355 36647811448814040827339033)
  ·
    refine ⟨27485858586610530620504275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36647811448814040827339033 27485858586610530620504275)
    ·
      refine ⟨41228787879915795930756413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27485858586610530620504275 41228787879915795930756413)
      ·
        refine ⟨15460795454968423474033655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41228787879915795930756413 15460795454968423474033655)
        ·
          refine ⟨23191193182452635211050483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15460795454968423474033655 23191193182452635211050483)
          ·
            refine ⟨34786789773678952816575725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23191193182452635211050483 34786789773678952816575725)
            ·
              refine ⟨13045046165129607306215897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34786789773678952816575725 13045046165129607306215897)
              ·
                refine ⟨9783784623847205479661923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13045046165129607306215897 9783784623847205479661923)
                ·
                  refine ⟨14675676935770808219492885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9783784623847205479661923 14675676935770808219492885)
                  ·
                    refine ⟨687922356364256635288729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14675676935770808219492885 687922356364256635288729)
                    ·
                      refine ⟨515941767273192476466547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687922356364256635288729 515941767273192476466547)
                      ·
                        rfl

theorem cell23_1004793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_1004793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004793 prefixEnd_1004793 := by exact prefixLift 1004793
  have htrace : WordTrace (prefixWord ++ tailWord_1004793) baseStart_1004793 baseEnd_1004793 := by
    simpa [prefixWord, tailWord_1004793, baseEnd_1004793] using wordTrace_append hprefix tailTrace_1004793
  have hstable : (prefixWord ++ tailWord_1004793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004793).length < 2 ^ (prefixWord ++ tailWord_1004793).sum := by decide
  have hdescent : baseEnd_1004793 < baseStart_1004793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004883 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 4]
def baseStart_1004883 : Nat := 118140960795 + 1004883 * 2 ^ 59
def prefixEnd_1004883 : Nat := 4983230072969 + 3 ^ 40 * 1004883 * 2
def baseEnd_1004883 : Nat := 515987980532097124341133

theorem tailTrace_1004883 : CollatzResearch.WordTrace tailWord_1004883 prefixEnd_1004883 515987980532097124341133 := by
  unfold tailWord_1004883
  simp only [CollatzResearch.WordTrace]
  refine ⟨36651094018487986198115303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24434062678991990798743535 36651094018487986198115303)
  ·
    refine ⟨54976641027731979297172955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36651094018487986198115303 54976641027731979297172955)
    ·
      refine ⟨82464961541597968945759433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54976641027731979297172955 82464961541597968945759433)
      ·
        refine ⟨61848721156198476709319575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82464961541597968945759433 61848721156198476709319575)
        ·
          refine ⟨92773081734297715063979363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61848721156198476709319575 92773081734297715063979363)
          ·
            refine ⟨139159622601446572595969045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92773081734297715063979363 139159622601446572595969045)
            ·
              refine ⟨6523107309442808090436049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139159622601446572595969045 6523107309442808090436049)
              ·
                refine ⟨4892330482082106067827037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523107309442808090436049 4892330482082106067827037)
                ·
                  refine ⟨1834623930780789775435139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4892330482082106067827037 1834623930780789775435139)
                  ·
                    refine ⟨2751935896171184663152709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834623930780789775435139 2751935896171184663152709)
                    ·
                      refine ⟨515987980532097124341133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2751935896171184663152709 515987980532097124341133)
                      ·
                        rfl

theorem cell23_1004883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_1004883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004883 prefixEnd_1004883 := by exact prefixLift 1004883
  have htrace : WordTrace (prefixWord ++ tailWord_1004883) baseStart_1004883 baseEnd_1004883 := by
    simpa [prefixWord, tailWord_1004883, baseEnd_1004883] using wordTrace_append hprefix tailTrace_1004883
  have hstable : (prefixWord ++ tailWord_1004883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004883).length < 2 ^ (prefixWord ++ tailWord_1004883).sum := by decide
  have hdescent : baseEnd_1004883 < baseStart_1004883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004900 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1004900 : Nat := 118140960795 + 1004900 * 2 ^ 59
def prefixEnd_1004900 : Nat := 4983230072969 + 3 ^ 40 * 1004900 * 2
def baseEnd_1004900 : Nat := 515996709703223557828555

theorem tailTrace_1004900 : CollatzResearch.WordTrace tailWord_1004900 prefixEnd_1004900 515996709703223557828555 := by
  unfold tailWord_1004900
  simp only [CollatzResearch.WordTrace]
  refine ⟨18325857029713199050742077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24434476039617598734322769 18325857029713199050742077)
  ·
    refine ⟨6872196386142449644028279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18325857029713199050742077 6872196386142449644028279)
    ·
      refine ⟨10308294579213674466042419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6872196386142449644028279 10308294579213674466042419)
      ·
        refine ⟨15462441868820511699063629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10308294579213674466042419 15462441868820511699063629)
        ·
          refine ⟨5798415700807691887148861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15462441868820511699063629 5798415700807691887148861)
          ·
            refine ⟨2174405887802884457680823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5798415700807691887148861 2174405887802884457680823)
            ·
              refine ⟨3261608831704326686521235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174405887802884457680823 3261608831704326686521235)
              ·
                refine ⟨4892413247556490029781853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261608831704326686521235 4892413247556490029781853)
                ·
                  refine ⟨1834654967833683761168195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4892413247556490029781853 1834654967833683761168195)
                  ·
                    refine ⟨2751982451750525641752293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834654967833683761168195 2751982451750525641752293)
                    ·
                      refine ⟨515996709703223557828555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2751982451750525641752293 515996709703223557828555)
                      ·
                        rfl

theorem cell23_1004900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1004900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004900 prefixEnd_1004900 := by exact prefixLift 1004900
  have htrace : WordTrace (prefixWord ++ tailWord_1004900) baseStart_1004900 baseEnd_1004900 := by
    simpa [prefixWord, tailWord_1004900, baseEnd_1004900] using wordTrace_append hprefix tailTrace_1004900
  have hstable : (prefixWord ++ tailWord_1004900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004900).length < 2 ^ (prefixWord ++ tailWord_1004900).sum := by decide
  have hdescent : baseEnd_1004900 < baseStart_1004900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004904 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_1004904 : Nat := 118140960795 + 1004904 * 2 ^ 59
def prefixEnd_1004904 : Nat := 4983230072969 + 3 ^ 40 * 1004904 * 2
def baseEnd_1004904 : Nat := 515998763625841542178537

theorem tailTrace_1004904 : CollatzResearch.WordTrace tailWord_1004904 prefixEnd_1004904 515998763625841542178537 := by
  unfold tailWord_1004904
  simp only [CollatzResearch.WordTrace]
  refine ⟨18325929975705953392314883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24434573300941271189753177 18325929975705953392314883)
  ·
    refine ⟨27488894963558930088472325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18325929975705953392314883 27488894963558930088472325)
    ·
      refine ⟨5154167805667299391588561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27488894963558930088472325 5154167805667299391588561)
      ·
        refine ⟨3865625854250474543691421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5154167805667299391588561 3865625854250474543691421)
        ·
          refine ⟨1449609695343927953884283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3865625854250474543691421 1449609695343927953884283)
          ·
            refine ⟨2174414543015891930826425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1449609695343927953884283 2174414543015891930826425)
            ·
              refine ⟨1630810907261918948119819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174414543015891930826425 1630810907261918948119819)
              ·
                refine ⟨2446216360892878422179729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630810907261918948119819 2446216360892878422179729)
                ·
                  refine ⟨1834662270669658816634797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2446216360892878422179729 1834662270669658816634797)
                  ·
                    refine ⟨687998351501122056238049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834662270669658816634797 687998351501122056238049)
                    ·
                      refine ⟨515998763625841542178537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 687998351501122056238049 515998763625841542178537)
                      ·
                        rfl

theorem cell23_1004904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_1004904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004904 prefixEnd_1004904 := by exact prefixLift 1004904
  have htrace : WordTrace (prefixWord ++ tailWord_1004904) baseStart_1004904 baseEnd_1004904 := by
    simpa [prefixWord, tailWord_1004904, baseEnd_1004904] using wordTrace_append hprefix tailTrace_1004904
  have hstable : (prefixWord ++ tailWord_1004904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004904).length < 2 ^ (prefixWord ++ tailWord_1004904).sum := by decide
  have hdescent : baseEnd_1004904 < baseStart_1004904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004913 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_1004913 : Nat := 118140960795 + 1004913 * 2 ^ 59
def prefixEnd_1004913 : Nat := 4983230072969 + 3 ^ 40 * 1004913 * 2
def baseEnd_1004913 : Nat := 516003384951732006965995

theorem tailTrace_1004913 : CollatzResearch.WordTrace tailWord_1004913 prefixEnd_1004913 516003384951732006965995 := by
  unfold tailWord_1004913
  simp only [CollatzResearch.WordTrace]
  refine ⟨36652188208379301321707393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24434792138919534214471595 36652188208379301321707393)
  ·
    refine ⟨27489141156284475991280545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36652188208379301321707393 27489141156284475991280545)
    ·
      refine ⟨20616855867213356993460409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27489141156284475991280545 20616855867213356993460409)
      ·
        refine ⟨15462641900410017745095307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20616855867213356993460409 15462641900410017745095307)
        ·
          refine ⟨23193962850615026617642961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15462641900410017745095307 23193962850615026617642961)
          ·
            refine ⟨17395472137961269963232221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23193962850615026617642961 17395472137961269963232221)
            ·
              refine ⟨6523302051735476236212083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17395472137961269963232221 6523302051735476236212083)
              ·
                refine ⟨9784953077603214354318125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523302051735476236212083 9784953077603214354318125)
                ·
                  refine ⟨3669357404101205382869297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9784953077603214354318125 3669357404101205382869297)
                  ·
                    refine ⟨2752018053075904037151973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3669357404101205382869297 2752018053075904037151973)
                    ·
                      refine ⟨516003384951732006965995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2752018053075904037151973 516003384951732006965995)
                      ·
                        rfl

theorem cell23_1004913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_1004913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004913 prefixEnd_1004913 := by exact prefixLift 1004913
  have htrace : WordTrace (prefixWord ++ tailWord_1004913) baseStart_1004913 baseEnd_1004913 := by
    simpa [prefixWord, tailWord_1004913, baseEnd_1004913] using wordTrace_append hprefix tailTrace_1004913
  have hstable : (prefixWord ++ tailWord_1004913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004913).length < 2 ^ (prefixWord ++ tailWord_1004913).sum := by decide
  have hdescent : baseEnd_1004913 < baseStart_1004913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004963 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5]
def baseStart_1004963 : Nat := 118140960795 + 1004963 * 2 ^ 59
def prefixEnd_1004963 : Nat := 4983230072969 + 3 ^ 40 * 1004963 * 2
def baseEnd_1004963 : Nat := 516029058984456811340765

theorem tailTrace_1004963 : CollatzResearch.WordTrace tailWord_1004963 prefixEnd_1004963 516029058984456811340765 := by
  unfold tailWord_1004963
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654011858198159861027543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24436007905465439907351695 36654011858198159861027543)
  ·
    refine ⟨54981017787297239791541315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36654011858198159861027543 54981017787297239791541315)
    ·
      refine ⟨82471526680945859687311973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54981017787297239791541315 82471526680945859687311973)
      ·
        refine ⟨15463411252677348691370995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82471526680945859687311973 15463411252677348691370995)
        ·
          refine ⟨23195116879016023037056493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15463411252677348691370995 23195116879016023037056493)
          ·
            refine ⟨8698168829631008638896185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23195116879016023037056493 8698168829631008638896185)
            ·
              refine ⟨6523626622223256479172139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8698168829631008638896185 6523626622223256479172139)
              ·
                refine ⟨9785439933334884718758209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6523626622223256479172139 9785439933334884718758209)
                ·
                  refine ⟨7339079950001163539068657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9785439933334884718758209 7339079950001163539068657)
                  ·
                    refine ⟨5504309962500872654301493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7339079950001163539068657 5504309962500872654301493)
                    ·
                      refine ⟨516029058984456811340765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5504309962500872654301493 516029058984456811340765)
                      ·
                        rfl

theorem cell23_1004963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_1004963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004963 prefixEnd_1004963 := by exact prefixLift 1004963
  have htrace : WordTrace (prefixWord ++ tailWord_1004963) baseStart_1004963 baseEnd_1004963 := by
    simpa [prefixWord, tailWord_1004963, baseEnd_1004963] using wordTrace_append hprefix tailTrace_1004963
  have hstable : (prefixWord ++ tailWord_1004963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004963).length < 2 ^ (prefixWord ++ tailWord_1004963).sum := by decide
  have hdescent : baseEnd_1004963 < baseStart_1004963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004967 : List Nat := [1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1004967 : Nat := 118140960795 + 1004967 * 2 ^ 59
def prefixEnd_1004967 : Nat := 4983230072969 + 3 ^ 40 * 1004967 * 2
def baseEnd_1004967 : Nat := 516031112907074795690747

theorem tailTrace_1004967 : CollatzResearch.WordTrace tailWord_1004967 prefixEnd_1004967 516031112907074795690747 := by
  unfold tailWord_1004967
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654157750183668544173155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24436105166789112362782103 36654157750183668544173155)
  ·
    refine ⟨54981236625275502816259733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36654157750183668544173155 54981236625275502816259733)
    ·
      refine ⟨2577245466809789194512175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 54981236625275502816259733 2577245466809789194512175)
      ·
        refine ⟨3865868200214683791768263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2577245466809789194512175 3865868200214683791768263)
        ·
          refine ⟨5798802300322025687652395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865868200214683791768263 5798802300322025687652395)
          ·
            refine ⟨8698203450483038531478593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5798802300322025687652395 8698203450483038531478593)
            ·
              refine ⟨6523652587862278898608945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8698203450483038531478593 6523652587862278898608945)
              ·
                refine ⟨4892739440896709173956709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6523652587862278898608945 4892739440896709173956709)
                ·
                  refine ⟨917388645168132970116883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4892739440896709173956709 917388645168132970116883)
                  ·
                    refine ⟨1376082967752199455175325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917388645168132970116883 1376082967752199455175325)
                    ·
                      refine ⟨516031112907074795690747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376082967752199455175325 516031112907074795690747)
                      ·
                        rfl

theorem cell23_1004967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1004967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004967 prefixEnd_1004967 := by exact prefixLift 1004967
  have htrace : WordTrace (prefixWord ++ tailWord_1004967) baseStart_1004967 baseEnd_1004967 := by
    simpa [prefixWord, tailWord_1004967, baseEnd_1004967] using wordTrace_append hprefix tailTrace_1004967
  have hstable : (prefixWord ++ tailWord_1004967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004967).length < 2 ^ (prefixWord ++ tailWord_1004967).sum := by decide
  have hdescent : baseEnd_1004967 < baseStart_1004967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004968 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1004968 : Nat := 118140960795 + 1004968 * 2 ^ 59
def prefixEnd_1004968 : Nat := 4983230072969 + 3 ^ 40 * 1004968 * 2
def baseEnd_1004968 : Nat := 516031626387729291778243

theorem tailTrace_1004968 : CollatzResearch.WordTrace tailWord_1004968 prefixEnd_1004968 516031626387729291778243 := by
  unfold tailWord_1004968
  simp only [CollatzResearch.WordTrace]
  refine ⟨18327097111590022857479779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24436129482120030476639705 18327097111590022857479779)
  ·
    refine ⟨27490645667385034286219669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18327097111590022857479779 27490645667385034286219669)
    ·
      refine ⟨1288624015658673482166547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 27490645667385034286219669 1288624015658673482166547)
      ·
        refine ⟨1932936023488010223249821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288624015658673482166547 1932936023488010223249821)
        ·
          refine ⟨724851008808003833718683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1932936023488010223249821 724851008808003833718683)
          ·
            refine ⟨1087276513212005750578025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724851008808003833718683 1087276513212005750578025)
            ·
              refine ⟨815457384909004312933519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1087276513212005750578025 815457384909004312933519)
              ·
                refine ⟨1223186077363506469400279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815457384909004312933519 1223186077363506469400279)
                ·
                  refine ⟨1834779116045259704100419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223186077363506469400279 1834779116045259704100419)
                  ·
                    refine ⟨2752168674067889556150629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1834779116045259704100419 2752168674067889556150629)
                    ·
                      refine ⟨516031626387729291778243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2752168674067889556150629 516031626387729291778243)
                      ·
                        rfl

theorem cell23_1004968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1004968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004968 prefixEnd_1004968 := by exact prefixLift 1004968
  have htrace : WordTrace (prefixWord ++ tailWord_1004968) baseStart_1004968 baseEnd_1004968 := by
    simpa [prefixWord, tailWord_1004968, baseEnd_1004968] using wordTrace_append hprefix tailTrace_1004968
  have hstable : (prefixWord ++ tailWord_1004968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004968).length < 2 ^ (prefixWord ++ tailWord_1004968).sum := by decide
  have hdescent : baseEnd_1004968 < baseStart_1004968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1004983 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 4, 6]
def baseStart_1004983 : Nat := 118140960795 + 1004983 * 2 ^ 59
def prefixEnd_1004983 : Nat := 4983230072969 + 3 ^ 40 * 1004983 * 2
def baseEnd_1004983 : Nat := 172013109532515577696891

theorem tailTrace_1004983 : CollatzResearch.WordTrace tailWord_1004983 prefixEnd_1004983 172013109532515577696891 := by
  unfold tailWord_1004983
  simp only [CollatzResearch.WordTrace]
  refine ⟨36654741318125703276755603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24436494212083802184503735 36654741318125703276755603)
  ·
    refine ⟨54982111977188554915133405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36654741318125703276755603 54982111977188554915133405)
    ·
      refine ⟨20618291991445708093175027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54982111977188554915133405 20618291991445708093175027)
      ·
        refine ⟨30927437987168562139762541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20618291991445708093175027 30927437987168562139762541)
        ·
          refine ⟨11597789245188210802410953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30927437987168562139762541 11597789245188210802410953)
          ·
            refine ⟨8698341933891158101808215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11597789245188210802410953 8698341933891158101808215)
            ·
              refine ⟨13047512900836737152712323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8698341933891158101808215 13047512900836737152712323)
              ·
                refine ⟨19571269351255105729068485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13047512900836737152712323 19571269351255105729068485)
                ·
                  refine ⟨3669613003360332324200341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19571269351255105729068485 3669613003360332324200341)
                  ·
                    refine ⟨172013109532515577696891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3669613003360332324200341 172013109532515577696891)
                    ·
                      rfl

theorem cell23_1004983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 6].length) (baseStart_1004983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1004983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1004983 prefixEnd_1004983 := by exact prefixLift 1004983
  have htrace : WordTrace (prefixWord ++ tailWord_1004983) baseStart_1004983 baseEnd_1004983 := by
    simpa [prefixWord, tailWord_1004983, baseEnd_1004983] using wordTrace_append hprefix tailTrace_1004983
  have hstable : (prefixWord ++ tailWord_1004983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1004983).length < 2 ^ (prefixWord ++ tailWord_1004983).sum := by decide
  have hdescent : baseEnd_1004983 < baseStart_1004983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1004983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005007 : List Nat := [1, 1, 2, 1, 1, 4, 5, 1, 1, 4, 2]
def baseStart_1005007 : Nat := 118140960795 + 1005007 * 2 ^ 59
def prefixEnd_1005007 : Nat := 4983230072969 + 3 ^ 40 * 1005007 * 2
def baseEnd_1005007 : Nat := 516051652133254639190563

theorem tailTrace_1005007 : CollatzResearch.WordTrace tailWord_1005007 prefixEnd_1005007 516051652133254639190563 := by
  unfold tailWord_1005007
  simp only [CollatzResearch.WordTrace]
  refine ⟨36655616670038755375629275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24437077780025836917086183 36655616670038755375629275)
  ·
    refine ⟨54983425005058133063443913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36655616670038755375629275 54983425005058133063443913)
    ·
      refine ⟨41237568753793599797582935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54983425005058133063443913 41237568753793599797582935)
      ·
        refine ⟨61856353130690399696374403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41237568753793599797582935 61856353130690399696374403)
        ·
          refine ⟨92784529696035599544561605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61856353130690399696374403 92784529696035599544561605)
          ·
            refine ⟨17397099318006674914605301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92784529696035599544561605 17397099318006674914605301)
            ·
              refine ⟨1630978061063125773244247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17397099318006674914605301 1630978061063125773244247)
              ·
                refine ⟨2446467091594688659866371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1630978061063125773244247 2446467091594688659866371)
                ·
                  refine ⟨3669700637392032989799557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446467091594688659866371 3669700637392032989799557)
                  ·
                    refine ⟨688068869511006185587417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3669700637392032989799557 688068869511006185587417)
                    ·
                      refine ⟨516051652133254639190563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688068869511006185587417 516051652133254639190563)
                      ·
                        rfl

theorem cell23_1005007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 4, 2].length) (baseStart_1005007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005007 prefixEnd_1005007 := by exact prefixLift 1005007
  have htrace : WordTrace (prefixWord ++ tailWord_1005007) baseStart_1005007 baseEnd_1005007 := by
    simpa [prefixWord, tailWord_1005007, baseEnd_1005007] using wordTrace_append hprefix tailTrace_1005007
  have hstable : (prefixWord ++ tailWord_1005007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005007).length < 2 ^ (prefixWord ++ tailWord_1005007).sum := by decide
  have hdescent : baseEnd_1005007 < baseStart_1005007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005043 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 3, 7]
def baseStart_1005043 : Nat := 118140960795 + 1005043 * 2 ^ 59
def prefixEnd_1005043 : Nat := 4983230072969 + 3 ^ 40 * 1005043 * 2
def baseEnd_1005043 : Nat := 172023379145605499446799

theorem tailTrace_1005043 : CollatzResearch.WordTrace tailWord_1005043 prefixEnd_1005043 172023379145605499446799 := by
  unfold tailWord_1005043
  simp only [CollatzResearch.WordTrace]
  refine ⟨36656929697908333523939783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24437953131938889015959855 36656929697908333523939783)
  ·
    refine ⟨54985394546862500285909675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36656929697908333523939783 54985394546862500285909675)
    ·
      refine ⟨82478091820293750428864513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54985394546862500285909675 82478091820293750428864513)
      ·
        refine ⟨61858568865220312821648385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82478091820293750428864513 61858568865220312821648385)
        ·
          refine ⟨46393926648915234616236289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61858568865220312821648385 46393926648915234616236289)
          ·
            refine ⟨34795444986686425962177217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46393926648915234616236289 34795444986686425962177217)
            ·
              refine ⟨26096583740014819471632913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34795444986686425962177217 26096583740014819471632913)
              ·
                refine ⟨19572437805011114603724685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26096583740014819471632913 19572437805011114603724685)
                ·
                  refine ⟨7339664176879167976396757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19572437805011114603724685 7339664176879167976396757)
                  ·
                    refine ⟨172023379145605499446799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7339664176879167976396757 172023379145605499446799)
                    ·
                      rfl

theorem cell23_1005043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 7].length) (baseStart_1005043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005043 prefixEnd_1005043 := by exact prefixLift 1005043
  have htrace : WordTrace (prefixWord ++ tailWord_1005043) baseStart_1005043 baseEnd_1005043 := by
    simpa [prefixWord, tailWord_1005043, baseEnd_1005043] using wordTrace_append hprefix tailTrace_1005043
  have hstable : (prefixWord ++ tailWord_1005043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005043).length < 2 ^ (prefixWord ++ tailWord_1005043).sum := by decide
  have hdescent : baseEnd_1005043 < baseStart_1005043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005058 : List Nat := [3, 4, 1, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1005058 : Nat := 118140960795 + 1005058 * 2 ^ 59
def prefixEnd_1005058 : Nat := 4983230072969 + 3 ^ 40 * 1005058 * 2
def baseEnd_1005058 : Nat := 516077839646633939652829

theorem tailTrace_1005058 : CollatzResearch.WordTrace tailWord_1005058 prefixEnd_1005058 516077839646633939652829 := by
  unfold tailWord_1005058
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164369198213497771433957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24438317861902660723823885 9164369198213497771433957)
  ·
    refine ⟨1718319224665030832143867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9164369198213497771433957 1718319224665030832143867)
    ·
      refine ⟨2577478836997546248215801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718319224665030832143867 2577478836997546248215801)
      ·
        refine ⟨1933109127748159686161851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2577478836997546248215801 1933109127748159686161851)
        ·
          refine ⟨2899663691622239529242777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933109127748159686161851 2899663691622239529242777)
          ·
            refine ⟨2174747768716679646932083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2899663691622239529242777 2174747768716679646932083)
            ·
              refine ⟨3262121653075019470398125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2174747768716679646932083 3262121653075019470398125)
              ·
                refine ⟨1223295619903132301399297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3262121653075019470398125 1223295619903132301399297)
                ·
                  refine ⟨917471714927349226049473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223295619903132301399297 917471714927349226049473)
                  ·
                    refine ⟨688103786195511919537105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 917471714927349226049473 688103786195511919537105)
                    ·
                      refine ⟨516077839646633939652829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688103786195511919537105 516077839646633939652829)
                      ·
                        rfl

theorem cell23_1005058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1005058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005058 prefixEnd_1005058 := by exact prefixLift 1005058
  have htrace : WordTrace (prefixWord ++ tailWord_1005058) baseStart_1005058 baseEnd_1005058 := by
    simpa [prefixWord, tailWord_1005058, baseEnd_1005058] using wordTrace_append hprefix tailTrace_1005058
  have hstable : (prefixWord ++ tailWord_1005058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005058).length < 2 ^ (prefixWord ++ tailWord_1005058).sum := by decide
  have hdescent : baseEnd_1005058 < baseStart_1005058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005062 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1005062 : Nat := 118140960795 + 1005062 * 2 ^ 59
def prefixEnd_1005062 : Nat := 4983230072969 + 3 ^ 40 * 1005062 * 2
def baseEnd_1005062 : Nat := 516079893569251924002811

theorem tailTrace_1005062 : CollatzResearch.WordTrace tailWord_1005062 prefixEnd_1005062 516079893569251924002811 := by
  unfold tailWord_1005062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145550708901234367777545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 24438415123226333179254293 1145550708901234367777545)
  ·
    refine ⟨859163031675925775833159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1145550708901234367777545 859163031675925775833159)
    ·
      refine ⟨1288744547513888663749739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859163031675925775833159 1288744547513888663749739)
      ·
        refine ⟨1933116821270832995624609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288744547513888663749739 1933116821270832995624609)
        ·
          refine ⟨1449837615953124746718457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1933116821270832995624609 1449837615953124746718457)
          ·
            refine ⟨1087378211964843560038843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1449837615953124746718457 1087378211964843560038843)
            ·
              refine ⟨1631067317947265340058265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087378211964843560038843 1631067317947265340058265)
              ·
                refine ⟨1223300488460449005043699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631067317947265340058265 1223300488460449005043699)
                ·
                  refine ⟨1834950732690673507565549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223300488460449005043699 1834950732690673507565549)
                  ·
                    refine ⟨688106524759002565337081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1834950732690673507565549 688106524759002565337081)
                    ·
                      refine ⟨516079893569251924002811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688106524759002565337081 516079893569251924002811)
                      ·
                        rfl

theorem cell23_1005062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1005062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005062 prefixEnd_1005062 := by exact prefixLift 1005062
  have htrace : WordTrace (prefixWord ++ tailWord_1005062) baseStart_1005062 baseEnd_1005062 := by
    simpa [prefixWord, tailWord_1005062, baseEnd_1005062] using wordTrace_append hprefix tailTrace_1005062
  have hstable : (prefixWord ++ tailWord_1005062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005062).length < 2 ^ (prefixWord ++ tailWord_1005062).sum := by decide
  have hdescent : baseEnd_1005062 < baseStart_1005062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005077 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1005077 : Nat := 118140960795 + 1005077 * 2 ^ 59
def prefixEnd_1005077 : Nat := 4983230072969 + 3 ^ 40 * 1005077 * 2
def baseEnd_1005077 : Nat := 172029198593023121771747

theorem tailTrace_1005077 : CollatzResearch.WordTrace tailWord_1005077 prefixEnd_1005077 172029198593023121771747 := by
  unfold tailWord_1005077
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658169779785157330677485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24438779853190104887118323 36658169779785157330677485)
  ·
    refine ⟨13746813667419433999004057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36658169779785157330677485 13746813667419433999004057)
    ·
      refine ⟨10310110250564575499253043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13746813667419433999004057 10310110250564575499253043)
      ·
        refine ⟨15465165375846863248879565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310110250564575499253043 15465165375846863248879565)
        ·
          refine ⟨5799437015942573718329837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15465165375846863248879565 5799437015942573718329837)
          ·
            refine ⟨2174788880978465144373689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5799437015942573718329837 2174788880978465144373689)
            ·
              refine ⟨1631091660733848858280267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2174788880978465144373689 1631091660733848858280267)
              ·
                refine ⟨2446637491100773287420401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631091660733848858280267 2446637491100773287420401)
                ·
                  refine ⟨1834978118325579965565301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2446637491100773287420401 1834978118325579965565301)
                  ·
                    refine ⟨172029198593023121771747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1834978118325579965565301 172029198593023121771747)
                    ·
                      rfl

theorem cell23_1005077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1005077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005077 prefixEnd_1005077 := by exact prefixLift 1005077
  have htrace : WordTrace (prefixWord ++ tailWord_1005077) baseStart_1005077 baseEnd_1005077 := by
    simpa [prefixWord, tailWord_1005077, baseEnd_1005077] using wordTrace_append hprefix tailTrace_1005077
  have hstable : (prefixWord ++ tailWord_1005077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005077).length < 2 ^ (prefixWord ++ tailWord_1005077).sum := by decide
  have hdescent : baseEnd_1005077 < baseStart_1005077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005083 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11]
def baseStart_1005083 : Nat := 118140960795 + 1005083 * 2 ^ 59
def prefixEnd_1005083 : Nat := 4983230072969 + 3 ^ 40 * 1005083 * 2
def baseEnd_1005083 : Nat := 516090676662996341840213

theorem tailTrace_1005083 : CollatzResearch.WordTrace tailWord_1005083 prefixEnd_1005083 516090676662996341840213 := by
  unfold tailWord_1005083
  simp only [CollatzResearch.WordTrace]
  refine ⟨36658388617763420355395903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24438925745175613570263935 36658388617763420355395903)
  ·
    refine ⟨54987582926645130533093855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36658388617763420355395903 54987582926645130533093855)
    ·
      refine ⟨82481374389967695799640783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54987582926645130533093855 82481374389967695799640783)
      ·
        refine ⟨123722061584951543699461175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82481374389967695799640783 123722061584951543699461175)
        ·
          refine ⟨185583092377427315549191763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123722061584951543699461175 185583092377427315549191763)
          ·
            refine ⟨278374638566140973323787645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185583092377427315549191763 278374638566140973323787645)
            ·
              refine ⟨104390489462302864996420367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278374638566140973323787645 104390489462302864996420367)
              ·
                refine ⟨156585734193454297494630551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104390489462302864996420367 156585734193454297494630551)
                ·
                  refine ⟨234878601290181446241945827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156585734193454297494630551 234878601290181446241945827)
                  ·
                    refine ⟨352317901935272169362918741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 234878601290181446241945827 352317901935272169362918741)
                    ·
                      refine ⟨516090676662996341840213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 352317901935272169362918741 516090676662996341840213)
                      ·
                        rfl

theorem cell23_1005083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 11].length) (baseStart_1005083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005083 prefixEnd_1005083 := by exact prefixLift 1005083
  have htrace : WordTrace (prefixWord ++ tailWord_1005083) baseStart_1005083 baseEnd_1005083 := by
    simpa [prefixWord, tailWord_1005083, baseEnd_1005083] using wordTrace_append hprefix tailTrace_1005083
  have hstable : (prefixWord ++ tailWord_1005083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005083).length < 2 ^ (prefixWord ++ tailWord_1005083).sum := by decide
  have hdescent : baseEnd_1005083 < baseStart_1005083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005100 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 3]
def baseStart_1005100 : Nat := 118140960795 + 1005100 * 2 ^ 59
def prefixEnd_1005100 : Nat := 4983230072969 + 3 ^ 40 * 1005100 * 2
def baseEnd_1005100 : Nat := 516099405834122775327635

theorem tailTrace_1005100 : CollatzResearch.WordTrace tailWord_1005100 prefixEnd_1005100 516099405834122775327635 := by
  unfold tailWord_1005100
  simp only [CollatzResearch.WordTrace]
  refine ⟨18329504329350916129382377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24439339105801221505843169 18329504329350916129382377)
  ·
    refine ⟨13747128247013187097036783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18329504329350916129382377 13747128247013187097036783)
    ·
      refine ⟨20620692370519780645555175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13747128247013187097036783 20620692370519780645555175)
      ·
        refine ⟨30931038555779670968332763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20620692370519780645555175 30931038555779670968332763)
        ·
          refine ⟨46396557833669506452499145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30931038555779670968332763 46396557833669506452499145)
          ·
            refine ⟨34797418375252129839374359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46396557833669506452499145 34797418375252129839374359)
            ·
              refine ⟨52196127562878194759061539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34797418375252129839374359 52196127562878194759061539)
              ·
                refine ⟨78294191344317292138592309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52196127562878194759061539 78294191344317292138592309)
                ·
                  refine ⟨7340080438529746137993029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78294191344317292138592309 7340080438529746137993029)
                  ·
                    refine ⟨1376265082224327400873693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7340080438529746137993029 1376265082224327400873693)
                    ·
                      refine ⟨516099405834122775327635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376265082224327400873693 516099405834122775327635)
                      ·
                        rfl

theorem cell23_1005100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_1005100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005100 prefixEnd_1005100 := by exact prefixLift 1005100
  have htrace : WordTrace (prefixWord ++ tailWord_1005100) baseStart_1005100 baseEnd_1005100 := by
    simpa [prefixWord, tailWord_1005100, baseEnd_1005100] using wordTrace_append hprefix tailTrace_1005100
  have hstable : (prefixWord ++ tailWord_1005100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005100).length < 2 ^ (prefixWord ++ tailWord_1005100).sum := by decide
  have hdescent : baseEnd_1005100 < baseStart_1005100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005187 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 8, 2]
def baseStart_1005187 : Nat := 118140960795 + 1005187 * 2 ^ 59
def prefixEnd_1005187 : Nat := 4983230072969 + 3 ^ 40 * 1005187 * 2
def baseEnd_1005187 : Nat := 516144078651063934939735

theorem tailTrace_1005187 : CollatzResearch.WordTrace tailWord_1005187 prefixEnd_1005187 516144078651063934939735 := by
  unfold tailWord_1005187
  simp only [CollatzResearch.WordTrace]
  refine ⟨36662181809386646117181815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24441454539591097411454543 36662181809386646117181815)
  ·
    refine ⟨54993272714079969175772723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36662181809386646117181815 54993272714079969175772723)
    ·
      refine ⟨82489909071119953763659085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54993272714079969175772723 82489909071119953763659085)
      ·
        refine ⟨30933715901669982661372157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82489909071119953763659085 30933715901669982661372157)
        ·
          refine ⟨11600143463126243498014559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30933715901669982661372157 11600143463126243498014559)
          ·
            refine ⟨17400215194689365247021839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11600143463126243498014559 17400215194689365247021839)
            ·
              refine ⟨26100322792034047870532759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17400215194689365247021839 26100322792034047870532759)
              ·
                refine ⟨39150484188051071805799139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26100322792034047870532759 39150484188051071805799139)
                ·
                  refine ⟨58725726282076607708698709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39150484188051071805799139 58725726282076607708698709)
                  ·
                    refine ⟨688192104868085246586313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 58725726282076607708698709 688192104868085246586313)
                    ·
                      refine ⟨516144078651063934939735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688192104868085246586313 516144078651063934939735)
                      ·
                        rfl

theorem cell23_1005187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_1005187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005187 prefixEnd_1005187 := by exact prefixLift 1005187
  have htrace : WordTrace (prefixWord ++ tailWord_1005187) baseStart_1005187 baseEnd_1005187 := by
    simpa [prefixWord, tailWord_1005187, baseEnd_1005187] using wordTrace_append hprefix tailTrace_1005187
  have hstable : (prefixWord ++ tailWord_1005187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005187).length < 2 ^ (prefixWord ++ tailWord_1005187).sum := by decide
  have hdescent : baseEnd_1005187 < baseStart_1005187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005198 : List Nat := [4, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3]
def baseStart_1005198 : Nat := 118140960795 + 1005198 * 2 ^ 59
def prefixEnd_1005198 : Nat := 4983230072969 + 3 ^ 40 * 1005198 * 2
def baseEnd_1005198 : Nat := 516149726938263391902185

theorem tailTrace_1005198 : CollatzResearch.WordTrace tailWord_1005198 prefixEnd_1005198 516149726938263391902185 := by
  unfold tailWord_1005198
  simp only [CollatzResearch.WordTrace]
  refine ⟨4582822876543349374479031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 24441722008231196663888165 4582822876543349374479031)
  ·
    refine ⟨6874234314815024061718547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4582822876543349374479031 6874234314815024061718547)
    ·
      refine ⟨10311351472222536092577821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6874234314815024061718547 10311351472222536092577821)
      ·
        refine ⟨3866756802083451034716683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10311351472222536092577821 3866756802083451034716683)
        ·
          refine ⟨5800135203125176552075025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866756802083451034716683 5800135203125176552075025)
          ·
            refine ⟨4350101402343882414056269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800135203125176552075025 4350101402343882414056269)
            ·
              refine ⟨1631288025878955905271101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350101402343882414056269 1631288025878955905271101)
              ·
                refine ⟨611733009704608464476663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1631288025878955905271101 611733009704608464476663)
                ·
                  refine ⟨917599514556912696714995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 611733009704608464476663 917599514556912696714995)
                  ·
                    refine ⟨1376399271835369045072493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917599514556912696714995 1376399271835369045072493)
                    ·
                      refine ⟨516149726938263391902185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376399271835369045072493 516149726938263391902185)
                      ·
                        rfl

theorem cell23_1005198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_1005198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005198 prefixEnd_1005198 := by exact prefixLift 1005198
  have htrace : WordTrace (prefixWord ++ tailWord_1005198) baseStart_1005198 baseEnd_1005198 := by
    simpa [prefixWord, tailWord_1005198, baseEnd_1005198] using wordTrace_append hprefix tailTrace_1005198
  have hstable : (prefixWord ++ tailWord_1005198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005198).length < 2 ^ (prefixWord ++ tailWord_1005198).sum := by decide
  have hdescent : baseEnd_1005198 < baseStart_1005198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005207 : List Nat := [1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1005207 : Nat := 118140960795 + 1005207 * 2 ^ 59
def prefixEnd_1005207 : Nat := 4983230072969 + 3 ^ 40 * 1005207 * 2
def baseEnd_1005207 : Nat := 516154348264153856689643

theorem tailTrace_1005207 : CollatzResearch.WordTrace tailWord_1005207 prefixEnd_1005207 516154348264153856689643 := by
  unfold tailWord_1005207
  simp only [CollatzResearch.WordTrace]
  refine ⟨36662911269314189532909875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24441940846209459688606583 36662911269314189532909875)
  ·
    refine ⟨54994366903971284299364813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36662911269314189532909875 54994366903971284299364813)
    ·
      refine ⟨20622887588989231612261805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54994366903971284299364813 20622887588989231612261805)
      ·
        refine ⟨7733582845870961854598177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20622887588989231612261805 7733582845870961854598177)
        ·
          refine ⟨5800187134403221390948633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7733582845870961854598177 5800187134403221390948633)
          ·
            refine ⟨4350140350802416043211475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5800187134403221390948633 4350140350802416043211475)
            ·
              refine ⟨6525210526203624064817213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350140350802416043211475 6525210526203624064817213)
              ·
                refine ⟨2446953947326359024306455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6525210526203624064817213 2446953947326359024306455)
                ·
                  refine ⟨3670430920989538536459683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2446953947326359024306455 3670430920989538536459683)
                  ·
                    refine ⟨5505646381484307804689525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3670430920989538536459683 5505646381484307804689525)
                    ·
                      refine ⟨516154348264153856689643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5505646381484307804689525 516154348264153856689643)
                      ·
                        rfl

theorem cell23_1005207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1005207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005207 prefixEnd_1005207 := by exact prefixLift 1005207
  have htrace : WordTrace (prefixWord ++ tailWord_1005207) baseStart_1005207 baseEnd_1005207 := by
    simpa [prefixWord, tailWord_1005207, baseEnd_1005207] using wordTrace_append hprefix tailTrace_1005207
  have hstable : (prefixWord ++ tailWord_1005207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005207).length < 2 ^ (prefixWord ++ tailWord_1005207).sum := by decide
  have hdescent : baseEnd_1005207 < baseStart_1005207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005215 : List Nat := [1, 1, 2, 7, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1005215 : Nat := 118140960795 + 1005215 * 2 ^ 59
def prefixEnd_1005215 : Nat := 4983230072969 + 3 ^ 40 * 1005215 * 2
def baseEnd_1005215 : Nat := 516158456109389825389607

theorem tailTrace_1005215 : CollatzResearch.WordTrace tailWord_1005215 prefixEnd_1005215 516158456109389825389607 := by
  unfold tailWord_1005215
  simp only [CollatzResearch.WordTrace]
  refine ⟨36663203053285206899201099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24442135368856804599467399 36663203053285206899201099)
  ·
    refine ⟨54994804579927810348801649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36663203053285206899201099 54994804579927810348801649)
    ·
      refine ⟨41246103434945857761601237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54994804579927810348801649 41246103434945857761601237)
      ·
        refine ⟨966705549256543541287529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 41246103434945857761601237 966705549256543541287529)
        ·
          refine ⟨725029161942407655965647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966705549256543541287529 725029161942407655965647)
          ·
            refine ⟨1087543742913611483948471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725029161942407655965647 1087543742913611483948471)
            ·
              refine ⟨1631315614370417225922707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087543742913611483948471 1631315614370417225922707)
              ·
                refine ⟨2446973421555625838884061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631315614370417225922707 2446973421555625838884061)
                ·
                  refine ⟨917615033083359689581523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2446973421555625838884061 917615033083359689581523)
                  ·
                    refine ⟨1376422549625039534372285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917615033083359689581523 1376422549625039534372285)
                    ·
                      refine ⟨516158456109389825389607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376422549625039534372285 516158456109389825389607)
                      ·
                        rfl

theorem cell23_1005215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1005215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005215 prefixEnd_1005215 := by exact prefixLift 1005215
  have htrace : WordTrace (prefixWord ++ tailWord_1005215) baseStart_1005215 baseEnd_1005215 := by
    simpa [prefixWord, tailWord_1005215, baseEnd_1005215] using wordTrace_append hprefix tailTrace_1005215
  have hstable : (prefixWord ++ tailWord_1005215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005215).length < 2 ^ (prefixWord ++ tailWord_1005215).sum := by decide
  have hdescent : baseEnd_1005215 < baseStart_1005215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005217 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1005217 : Nat := 118140960795 + 1005217 * 2 ^ 59
def prefixEnd_1005217 : Nat := 4983230072969 + 3 ^ 40 * 1005217 * 2
def baseEnd_1005217 : Nat := 516159483070698817564597

theorem tailTrace_1005217 : CollatzResearch.WordTrace tailWord_1005217 prefixEnd_1005217 516159483070698817564597 := by
  unfold tailWord_1005217
  simp only [CollatzResearch.WordTrace]
  refine ⟨36663275999277961240773905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24442183999518640827182603 36663275999277961240773905)
  ·
    refine ⟨27497456999458470930580429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36663275999277961240773905 27497456999458470930580429)
    ·
      refine ⟨10311546374796926598967661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27497456999458470930580429 10311546374796926598967661)
      ·
        refine ⟨3866829890548847474612873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10311546374796926598967661 3866829890548847474612873)
        ·
          refine ⟨2900122417911635605959655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3866829890548847474612873 2900122417911635605959655)
          ·
            refine ⟨4350183626867453408939483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900122417911635605959655 4350183626867453408939483)
            ·
              refine ⟨6525275440301180113409225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350183626867453408939483 6525275440301180113409225)
              ·
                refine ⟨4893956580225885085056919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6525275440301180113409225 4893956580225885085056919)
                ·
                  refine ⟨7340934870338827627585379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4893956580225885085056919 7340934870338827627585379)
                  ·
                    refine ⟨11011402305508241441378069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7340934870338827627585379 11011402305508241441378069)
                    ·
                      refine ⟨516159483070698817564597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11011402305508241441378069 516159483070698817564597)
                      ·
                        rfl

theorem cell23_1005217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1005217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005217 prefixEnd_1005217 := by exact prefixLift 1005217
  have htrace : WordTrace (prefixWord ++ tailWord_1005217) baseStart_1005217 baseEnd_1005217 := by
    simpa [prefixWord, tailWord_1005217, baseEnd_1005217] using wordTrace_append hprefix tailTrace_1005217
  have hstable : (prefixWord ++ tailWord_1005217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005217).length < 2 ^ (prefixWord ++ tailWord_1005217).sum := by decide
  have hdescent : baseEnd_1005217 < baseStart_1005217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005221 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 3, 2, 2]
def baseStart_1005221 : Nat := 118140960795 + 1005221 * 2 ^ 59
def prefixEnd_1005221 : Nat := 4983230072969 + 3 ^ 40 * 1005221 * 2
def baseEnd_1005221 : Nat := 516161536993316801914579

theorem tailTrace_1005221 : CollatzResearch.WordTrace tailWord_1005221 prefixEnd_1005221 516161536993316801914579 := by
  unfold tailWord_1005221
  simp only [CollatzResearch.WordTrace]
  refine ⟨36663421891263469923919517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24442281260842313282613011 36663421891263469923919517)
  ·
    refine ⟨13748783209223801221469819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36663421891263469923919517 13748783209223801221469819)
    ·
      refine ⟨20623174813835701832204729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13748783209223801221469819 20623174813835701832204729)
      ·
        refine ⟨15467381110376776374153547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20623174813835701832204729 15467381110376776374153547)
        ·
          refine ⟨23201071665565164561230321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15467381110376776374153547 23201071665565164561230321)
          ·
            refine ⟨17400803749173873420922741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23201071665565164561230321 17400803749173873420922741)
            ·
              refine ⟨1631325351485050633211507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17400803749173873420922741 1631325351485050633211507)
              ·
                refine ⟨2446988027227575949817261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1631325351485050633211507 2446988027227575949817261)
                ·
                  refine ⟨917620510210340981181473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2446988027227575949817261 917620510210340981181473)
                  ·
                    refine ⟨688215382657755735886105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 917620510210340981181473 688215382657755735886105)
                    ·
                      refine ⟨516161536993316801914579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688215382657755735886105 516161536993316801914579)
                      ·
                        rfl

theorem cell23_1005221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_1005221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005221 prefixEnd_1005221 := by exact prefixLift 1005221
  have htrace : WordTrace (prefixWord ++ tailWord_1005221) baseStart_1005221 baseEnd_1005221 := by
    simpa [prefixWord, tailWord_1005221, baseEnd_1005221] using wordTrace_append hprefix tailTrace_1005221
  have hstable : (prefixWord ++ tailWord_1005221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005221).length < 2 ^ (prefixWord ++ tailWord_1005221).sum := by decide
  have hdescent : baseEnd_1005221 < baseStart_1005221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005238 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1005238 : Nat := 118140960795 + 1005238 * 2 ^ 59
def prefixEnd_1005238 : Nat := 4983230072969 + 3 ^ 40 * 1005238 * 2
def baseEnd_1005238 : Nat := 516170266164443235402001

theorem tailTrace_1005238 : CollatzResearch.WordTrace tailWord_1005238 prefixEnd_1005238 516170266164443235402001 := by
  unfold tailWord_1005238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2291502620762617614205523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24442694621467921218192245 2291502620762617614205523)
  ·
    refine ⟨3437253931143926421308285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2291502620762617614205523 3437253931143926421308285)
    ·
      refine ⟨1288970224178972407990607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3437253931143926421308285 1288970224178972407990607)
      ·
        refine ⟨1933455336268458611985911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288970224178972407990607 1933455336268458611985911)
        ·
          refine ⟨2900183004402687917978867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933455336268458611985911 2900183004402687917978867)
          ·
            refine ⟨4350274506604031876968301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900183004402687917978867 4350274506604031876968301)
            ·
              refine ⟨1631352939976511953863113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4350274506604031876968301 1631352939976511953863113)
              ·
                refine ⟨1223514704982383965397335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631352939976511953863113 1223514704982383965397335)
                ·
                  refine ⟨1835272057473575948096003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223514704982383965397335 1835272057473575948096003)
                  ·
                    refine ⟨2752908086210363922144005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835272057473575948096003 2752908086210363922144005)
                    ·
                      refine ⟨516170266164443235402001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2752908086210363922144005 516170266164443235402001)
                      ·
                        rfl

theorem cell23_1005238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1005238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005238 prefixEnd_1005238 := by exact prefixLift 1005238
  have htrace : WordTrace (prefixWord ++ tailWord_1005238) baseStart_1005238 baseEnd_1005238 := by
    simpa [prefixWord, tailWord_1005238, baseEnd_1005238] using wordTrace_append hprefix tailTrace_1005238
  have hstable : (prefixWord ++ tailWord_1005238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005238).length < 2 ^ (prefixWord ++ tailWord_1005238).sum := by decide
  have hdescent : baseEnd_1005238 < baseStart_1005238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005258 : List Nat := [3, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3]
def baseStart_1005258 : Nat := 118140960795 + 1005258 * 2 ^ 59
def prefixEnd_1005258 : Nat := 4983230072969 + 3 ^ 40 * 1005258 * 2
def baseEnd_1005258 : Nat := 516180535777533157151909

theorem tailTrace_1005258 : CollatzResearch.WordTrace tailWord_1005258 prefixEnd_1005258 516180535777533157151909 := by
  unfold tailWord_1005258
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166192848032356310754107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24443180928086283495344285 9166192848032356310754107)
  ·
    refine ⟨13749289272048534466131161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9166192848032356310754107 13749289272048534466131161)
    ·
      refine ⟨10311966954036400849598371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13749289272048534466131161 10311966954036400849598371)
      ·
        refine ⟨15467950431054601274397557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10311966954036400849598371 15467950431054601274397557)
        ·
          refine ⟨1450120352911368869474771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15467950431054601274397557 1450120352911368869474771)
          ·
            refine ⟨2175180529367053304212157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450120352911368869474771 2175180529367053304212157)
            ·
              refine ⟨815692698512644989079559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2175180529367053304212157 815692698512644989079559)
              ·
                refine ⟨1223539047768967483619339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815692698512644989079559 1223539047768967483619339)
                ·
                  refine ⟨1835308571653451225429009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223539047768967483619339 1835308571653451225429009)
                  ·
                    refine ⟨1376481428740088419071757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1835308571653451225429009 1376481428740088419071757)
                    ·
                      refine ⟨516180535777533157151909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376481428740088419071757 516180535777533157151909)
                      ·
                        rfl

theorem cell23_1005258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_1005258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005258 prefixEnd_1005258 := by exact prefixLift 1005258
  have htrace : WordTrace (prefixWord ++ tailWord_1005258) baseStart_1005258 baseEnd_1005258 := by
    simpa [prefixWord, tailWord_1005258, baseEnd_1005258] using wordTrace_append hprefix tailTrace_1005258
  have hstable : (prefixWord ++ tailWord_1005258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005258).length < 2 ^ (prefixWord ++ tailWord_1005258).sum := by decide
  have hdescent : baseEnd_1005258 < baseStart_1005258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005271 : List Nat := [1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 3]
def baseStart_1005271 : Nat := 118140960795 + 1005271 * 2 ^ 59
def prefixEnd_1005271 : Nat := 4983230072969 + 3 ^ 40 * 1005271 * 2
def baseEnd_1005271 : Nat := 516187211026041606289349

theorem tailTrace_1005271 : CollatzResearch.WordTrace tailWord_1005271 prefixEnd_1005271 516187211026041606289349 := by
  unfold tailWord_1005271
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665245541082328463239667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24443497027388218975493111 36665245541082328463239667)
  ·
    refine ⟨54997868311623492694859501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36665245541082328463239667 54997868311623492694859501)
    ·
      refine ⟨20624200616858809760572313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54997868311623492694859501 20624200616858809760572313)
      ·
        refine ⟨15468150462644107320429235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20624200616858809760572313 15468150462644107320429235)
        ·
          refine ⟨23202225693966160980643853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15468150462644107320429235 23202225693966160980643853)
          ·
            refine ⟨8700834635237310367741445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23202225693966160980643853 8700834635237310367741445)
            ·
              refine ⟨1631406494106995693951521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8700834635237310367741445 1631406494106995693951521)
              ·
                refine ⟨1223554870580246770463641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631406494106995693951521 1223554870580246770463641)
                ·
                  refine ⟨917666152935185077847731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223554870580246770463641 917666152935185077847731)
                  ·
                    refine ⟨1376499229402777616771597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917666152935185077847731 1376499229402777616771597)
                    ·
                      refine ⟨516187211026041606289349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376499229402777616771597 516187211026041606289349)
                      ·
                        rfl

theorem cell23_1005271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_1005271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005271 prefixEnd_1005271 := by exact prefixLift 1005271
  have htrace : WordTrace (prefixWord ++ tailWord_1005271) baseStart_1005271 baseEnd_1005271 := by
    simpa [prefixWord, tailWord_1005271, baseEnd_1005271] using wordTrace_append hprefix tailTrace_1005271
  have hstable : (prefixWord ++ tailWord_1005271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005271).length < 2 ^ (prefixWord ++ tailWord_1005271).sum := by decide
  have hdescent : baseEnd_1005271 < baseStart_1005271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005314 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_1005314 : Nat := 118140960795 + 1005314 * 2 ^ 59
def prefixEnd_1005314 : Nat := 4983230072969 + 3 ^ 40 * 1005314 * 2
def baseEnd_1005314 : Nat := 516209290694184938051651

theorem tailTrace_1005314 : CollatzResearch.WordTrace tailWord_1005314 prefixEnd_1005314 516209290694184938051651 := by
  unfold tailWord_1005314
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166703469981636701763749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24444542586617697871369997 9166703469981636701763749)
  ·
    refine ⟨1718756900621556881580703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9166703469981636701763749 1718756900621556881580703)
    ·
      refine ⟨2578135350932335322371055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1718756900621556881580703 2578135350932335322371055)
      ·
        refine ⟨3867203026398502983556583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2578135350932335322371055 3867203026398502983556583)
        ·
          refine ⟨5800804539597754475334875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867203026398502983556583 5800804539597754475334875)
          ·
            refine ⟨8701206809396631713002313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800804539597754475334875 8701206809396631713002313)
            ·
              refine ⟨6525905107047473784751735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8701206809396631713002313 6525905107047473784751735)
              ·
                refine ⟨9788857660571210677127603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6525905107047473784751735 9788857660571210677127603)
                ·
                  refine ⟨14683286490856816015691405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9788857660571210677127603 14683286490856816015691405)
                  ·
                    refine ⟨5506232434071306005884277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14683286490856816015691405 5506232434071306005884277)
                    ·
                      refine ⟨516209290694184938051651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5506232434071306005884277 516209290694184938051651)
                      ·
                        rfl

theorem cell23_1005314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_1005314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005314 prefixEnd_1005314 := by exact prefixLift 1005314
  have htrace : WordTrace (prefixWord ++ tailWord_1005314) baseStart_1005314 baseEnd_1005314 := by
    simpa [prefixWord, tailWord_1005314, baseEnd_1005314] using wordTrace_append hprefix tailTrace_1005314
  have hstable : (prefixWord ++ tailWord_1005314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005314).length < 2 ^ (prefixWord ++ tailWord_1005314).sum := by decide
  have hdescent : baseEnd_1005314 < baseStart_1005314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005344 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1005344 : Nat := 118140960795 + 1005344 * 2 ^ 59
def prefixEnd_1005344 : Nat := 4983230072969 + 3 ^ 40 * 1005344 * 2
def baseEnd_1005344 : Nat := 516224695113819820676513

theorem tailTrace_1005344 : CollatzResearch.WordTrace tailWord_1005344 prefixEnd_1005344 516224695113819820676513 := by
  unfold tailWord_1005344
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333954034908930965323543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24445272046545241287098057 18333954034908930965323543)
  ·
    refine ⟨27500931052363396447985315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333954034908930965323543 27500931052363396447985315)
    ·
      refine ⟨41251396578545094671977973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500931052363396447985315 41251396578545094671977973)
      ·
        refine ⟨3867318429238602625497935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41251396578545094671977973 3867318429238602625497935)
        ·
          refine ⟨5800977643857903938246903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3867318429238602625497935 5800977643857903938246903)
          ·
            refine ⟨8701466465786855907370355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800977643857903938246903 8701466465786855907370355)
            ·
              refine ⟨13052199698680283861055533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701466465786855907370355 13052199698680283861055533)
              ·
                refine ⟨4894574887005106447895825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13052199698680283861055533 4894574887005106447895825)
                ·
                  refine ⟨3670931165253829835921869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4894574887005106447895825 3670931165253829835921869)
                  ·
                    refine ⟨1376599186970186188470701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3670931165253829835921869 1376599186970186188470701)
                    ·
                      refine ⟨516224695113819820676513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376599186970186188470701 516224695113819820676513)
                      ·
                        rfl

theorem cell23_1005344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1005344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005344 prefixEnd_1005344 := by exact prefixLift 1005344
  have htrace : WordTrace (prefixWord ++ tailWord_1005344) baseStart_1005344 baseEnd_1005344 := by
    simpa [prefixWord, tailWord_1005344, baseEnd_1005344] using wordTrace_append hprefix tailTrace_1005344
  have hstable : (prefixWord ++ tailWord_1005344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005344).length < 2 ^ (prefixWord ++ tailWord_1005344).sum := by decide
  have hdescent : baseEnd_1005344 < baseStart_1005344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005345 : List Nat := [1, 2, 3, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_1005345 : Nat := 118140960795 + 1005345 * 2 ^ 59
def prefixEnd_1005345 : Nat := 4983230072969 + 3 ^ 40 * 1005345 * 2
def baseEnd_1005345 : Nat := 516225208594474316764009

theorem tailTrace_1005345 : CollatzResearch.WordTrace tailWord_1005345 prefixEnd_1005345 516225208594474316764009 := by
  unfold tailWord_1005345
  simp only [CollatzResearch.WordTrace]
  refine ⟨36667944542814239101433489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24445296361876159400955659 36667944542814239101433489)
  ·
    refine ⟨27500958407110679326075117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36667944542814239101433489 27500958407110679326075117)
    ·
      refine ⟨10312859402666504747278169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27500958407110679326075117 10312859402666504747278169)
      ·
        refine ⟨7734644551999878560458627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10312859402666504747278169 7734644551999878560458627)
        ·
          refine ⟨11601966827999817840687941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734644551999878560458627 11601966827999817840687941)
          ·
            refine ⟨2175368780249965845128989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11601966827999817840687941 2175368780249965845128989)
            ·
              refine ⟨815763292593737191923371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2175368780249965845128989 815763292593737191923371)
              ·
                refine ⟨1223644938890605787885057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815763292593737191923371 1223644938890605787885057)
                ·
                  refine ⟨917733704167954340913793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223644938890605787885057 917733704167954340913793)
                  ·
                    refine ⟨688300278125965755685345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 917733704167954340913793 688300278125965755685345)
                    ·
                      refine ⟨516225208594474316764009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688300278125965755685345 516225208594474316764009)
                      ·
                        rfl

theorem cell23_1005345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_1005345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005345 prefixEnd_1005345 := by exact prefixLift 1005345
  have htrace : WordTrace (prefixWord ++ tailWord_1005345) baseStart_1005345 baseEnd_1005345 := by
    simpa [prefixWord, tailWord_1005345, baseEnd_1005345] using wordTrace_append hprefix tailTrace_1005345
  have hstable : (prefixWord ++ tailWord_1005345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005345).length < 2 ^ (prefixWord ++ tailWord_1005345).sum := by decide
  have hdescent : baseEnd_1005345 < baseStart_1005345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005347 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 1, 7]
def baseStart_1005347 : Nat := 118140960795 + 1005347 * 2 ^ 59
def prefixEnd_1005347 : Nat := 4983230072969 + 3 ^ 40 * 1005347 * 2
def baseEnd_1005347 : Nat := 172075411851927769646333

theorem tailTrace_1005347 : CollatzResearch.WordTrace tailWord_1005347 prefixEnd_1005347 172075411851927769646333 := by
  unfold tailWord_1005347
  simp only [CollatzResearch.WordTrace]
  refine ⟨36668017488806993443006295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24445344992537995628670863 36668017488806993443006295)
  ·
    refine ⟨55002026233210490164509443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36668017488806993443006295 55002026233210490164509443)
    ·
      refine ⟨82503039349815735246764165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55002026233210490164509443 82503039349815735246764165)
      ·
        refine ⟨15469319878090450358768281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82503039349815735246764165 15469319878090450358768281)
        ·
          refine ⟨11601989908567837769076211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15469319878090450358768281 11601989908567837769076211)
          ·
            refine ⟨17402984862851756653614317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601989908567837769076211 17402984862851756653614317)
            ·
              refine ⟨6526119323569408745105369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17402984862851756653614317 6526119323569408745105369)
              ·
                refine ⟨4894589492677056558829027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6526119323569408745105369 4894589492677056558829027)
                ·
                  refine ⟨7341884239015584838243541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894589492677056558829027 7341884239015584838243541)
                  ·
                    refine ⟨172075411851927769646333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 7341884239015584838243541 172075411851927769646333)
                    ·
                      rfl

theorem cell23_1005347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 7].length) (baseStart_1005347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005347 prefixEnd_1005347 := by exact prefixLift 1005347
  have htrace : WordTrace (prefixWord ++ tailWord_1005347) baseStart_1005347 baseEnd_1005347 := by
    simpa [prefixWord, tailWord_1005347, baseEnd_1005347] using wordTrace_append hprefix tailTrace_1005347
  have hstable : (prefixWord ++ tailWord_1005347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005347).length < 2 ^ (prefixWord ++ tailWord_1005347).sum := by decide
  have hdescent : baseEnd_1005347 < baseStart_1005347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005384 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_1005384 : Nat := 118140960795 + 1005384 * 2 ^ 59
def prefixEnd_1005384 : Nat := 4983230072969 + 3 ^ 40 * 1005384 * 2
def baseEnd_1005384 : Nat := 516245234339999664176329

theorem tailTrace_1005384 : CollatzResearch.WordTrace tailWord_1005384 prefixEnd_1005384 516245234339999664176329 := by
  unfold tailWord_1005384
  simp only [CollatzResearch.WordTrace]
  refine ⟨18334683494836474381051603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24446244659781965841402137 18334683494836474381051603)
  ·
    refine ⟨27502025242254711571577405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18334683494836474381051603 27502025242254711571577405)
    ·
      refine ⟨10313259465845516839341527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27502025242254711571577405 10313259465845516839341527)
      ·
        refine ⟨15469889198768275259012291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10313259465845516839341527 15469889198768275259012291)
        ·
          refine ⟨23204833798152412888518437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15469889198768275259012291 23204833798152412888518437)
          ·
            refine ⟨4350906337153577416597207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23204833798152412888518437 4350906337153577416597207)
            ·
              refine ⟨6526359505730366124895811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4350906337153577416597207 6526359505730366124895811)
              ·
                refine ⟨9789539258595549187343717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526359505730366124895811 9789539258595549187343717)
                ·
                  refine ⟨1835538610986665472626947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 9789539258595549187343717 1835538610986665472626947)
                  ·
                    refine ⟨2753307916479998208940421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835538610986665472626947 2753307916479998208940421)
                    ·
                      refine ⟨516245234339999664176329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2753307916479998208940421 516245234339999664176329)
                      ·
                        rfl

theorem cell23_1005384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_1005384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005384 prefixEnd_1005384 := by exact prefixLift 1005384
  have htrace : WordTrace (prefixWord ++ tailWord_1005384) baseStart_1005384 baseEnd_1005384 := by
    simpa [prefixWord, tailWord_1005384, baseEnd_1005384] using wordTrace_append hprefix tailTrace_1005384
  have hstable : (prefixWord ++ tailWord_1005384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005384).length < 2 ^ (prefixWord ++ tailWord_1005384).sum := by decide
  have hdescent : baseEnd_1005384 < baseStart_1005384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005421 : List Nat := [1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1005421 : Nat := 118140960795 + 1005421 * 2 ^ 59
def prefixEnd_1005421 : Nat := 4983230072969 + 3 ^ 40 * 1005421 * 2
def baseEnd_1005421 : Nat := 516264233124216019413659

theorem tailTrace_1005421 : CollatzResearch.WordTrace tailWord_1005421 prefixEnd_1005421 516264233124216019413659 := by
  unfold tailWord_1005421
  simp only [CollatzResearch.WordTrace]
  refine ⟨36670716490538904081200117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24447144327025936054133411 36670716490538904081200117)
  ·
    refine ⟨3437879670988022257612511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 36670716490538904081200117 3437879670988022257612511)
    ·
      refine ⟨5156819506482033386418767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437879670988022257612511 5156819506482033386418767)
      ·
        refine ⟨7735229259723050079628151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5156819506482033386418767 7735229259723050079628151)
        ·
          refine ⟨11602843889584575119442227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735229259723050079628151 11602843889584575119442227)
          ·
            refine ⟨17404265834376862679163341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602843889584575119442227 17404265834376862679163341)
            ·
              refine ⟨6526599687891323504686253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17404265834376862679163341 6526599687891323504686253)
              ·
                refine ⟨2447474882959246314257345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6526599687891323504686253 2447474882959246314257345)
                ·
                  refine ⟨1835606162219434735693009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2447474882959246314257345 1835606162219434735693009)
                  ·
                    refine ⟨1376704621664576051769757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1835606162219434735693009 1376704621664576051769757)
                    ·
                      refine ⟨516264233124216019413659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376704621664576051769757 516264233124216019413659)
                      ·
                        rfl

theorem cell23_1005421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1005421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005421 prefixEnd_1005421 := by exact prefixLift 1005421
  have htrace : WordTrace (prefixWord ++ tailWord_1005421) baseStart_1005421 baseEnd_1005421 := by
    simpa [prefixWord, tailWord_1005421, baseEnd_1005421] using wordTrace_append hprefix tailTrace_1005421
  have hstable : (prefixWord ++ tailWord_1005421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005421).length < 2 ^ (prefixWord ++ tailWord_1005421).sum := by decide
  have hdescent : baseEnd_1005421 < baseStart_1005421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005427 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8]
def baseStart_1005427 : Nat := 118140960795 + 1005427 * 2 ^ 59
def prefixEnd_1005427 : Nat := 4983230072969 + 3 ^ 40 * 1005427 * 2
def baseEnd_1005427 : Nat := 516267314008142995938631

theorem tailTrace_1005427 : CollatzResearch.WordTrace tailWord_1005427 prefixEnd_1005427 516267314008142995938631 := by
  unfold tailWord_1005427
  simp only [CollatzResearch.WordTrace]
  refine ⟨36670935328517167105918535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24447290219011444737279023 36670935328517167105918535)
  ·
    refine ⟨55006402992775750658877803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36670935328517167105918535 55006402992775750658877803)
    ·
      refine ⟨82509604489163625988316705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55006402992775750658877803 82509604489163625988316705)
      ·
        refine ⟨61882203366872719491237529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82509604489163625988316705 61882203366872719491237529)
        ·
          refine ⟨46411652525154539618428147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61882203366872719491237529 46411652525154539618428147)
          ·
            refine ⟨69617478787731809427642221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46411652525154539618428147 69617478787731809427642221)
            ·
              refine ⟨26106554545399428535365833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69617478787731809427642221 26106554545399428535365833)
              ·
                refine ⟨19579915909049571401524375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26106554545399428535365833 19579915909049571401524375)
                ·
                  refine ⟨29369873863574357102286563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19579915909049571401524375 29369873863574357102286563)
                  ·
                    refine ⟨44054810795361535653429845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29369873863574357102286563 44054810795361535653429845)
                    ·
                      refine ⟨516267314008142995938631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 44054810795361535653429845 516267314008142995938631)
                      ·
                        rfl

theorem cell23_1005427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_1005427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005427 prefixEnd_1005427 := by exact prefixLift 1005427
  have htrace : WordTrace (prefixWord ++ tailWord_1005427) baseStart_1005427 baseEnd_1005427 := by
    simpa [prefixWord, tailWord_1005427, baseEnd_1005427] using wordTrace_append hprefix tailTrace_1005427
  have hstable : (prefixWord ++ tailWord_1005427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005427).length < 2 ^ (prefixWord ++ tailWord_1005427).sum := by decide
  have hdescent : baseEnd_1005427 < baseStart_1005427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005451 : List Nat := [1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 3]
def baseStart_1005451 : Nat := 118140960795 + 1005451 * 2 ^ 59
def prefixEnd_1005451 : Nat := 4983230072969 + 3 ^ 40 * 1005451 * 2
def baseEnd_1005451 : Nat := 516279637543850902038521

theorem tailTrace_1005451 : CollatzResearch.WordTrace tailWord_1005451 prefixEnd_1005451 516279637543850902038521 := by
  unfold tailWord_1005451
  simp only [CollatzResearch.WordTrace]
  refine ⟨36671810680430219204792207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24447873786953479469861471 36671810680430219204792207)
  ·
    refine ⟨55007716020645328807188311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36671810680430219204792207 55007716020645328807188311)
    ·
      refine ⟨82511574030967993210782467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55007716020645328807188311 82511574030967993210782467)
      ·
        refine ⟨123767361046451989816173701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82511574030967993210782467 123767361046451989816173701)
        ·
          refine ⟨23206380196209748090532569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123767361046451989816173701 23206380196209748090532569)
          ·
            refine ⟨17404785147157311067899427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23206380196209748090532569 17404785147157311067899427)
            ·
              refine ⟨26107177720735966601849141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17404785147157311067899427 26107177720735966601849141)
              ·
                refine ⟨2447547911318996868923357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26107177720735966601849141 2447547911318996868923357)
                ·
                  refine ⟨917830466744623825846259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2447547911318996868923357 917830466744623825846259)
                  ·
                    refine ⟨1376745700116935738769389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917830466744623825846259 1376745700116935738769389)
                    ·
                      refine ⟨516279637543850902038521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376745700116935738769389 516279637543850902038521)
                      ·
                        rfl

theorem cell23_1005451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 3, 1, 3].length) (baseStart_1005451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005451 prefixEnd_1005451 := by exact prefixLift 1005451
  have htrace : WordTrace (prefixWord ++ tailWord_1005451) baseStart_1005451 baseEnd_1005451 := by
    simpa [prefixWord, tailWord_1005451, baseEnd_1005451] using wordTrace_append hprefix tailTrace_1005451
  have hstable : (prefixWord ++ tailWord_1005451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005451).length < 2 ^ (prefixWord ++ tailWord_1005451).sum := by decide
  have hdescent : baseEnd_1005451 < baseStart_1005451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005461 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 1, 5, 2]
def baseStart_1005461 : Nat := 118140960795 + 1005461 * 2 ^ 59
def prefixEnd_1005461 : Nat := 4983230072969 + 3 ^ 40 * 1005461 * 2
def baseEnd_1005461 : Nat := 516284772350395862913475

theorem tailTrace_1005461 : CollatzResearch.WordTrace tailWord_1005461 prefixEnd_1005461 516284772350395862913475 := by
  unfold tailWord_1005461
  simp only [CollatzResearch.WordTrace]
  refine ⟨36672175410393990912656237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24448116940262660608437491 36672175410393990912656237)
  ·
    refine ⟨13752065778897746592246089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36672175410393990912656237 13752065778897746592246089)
    ·
      refine ⟨10314049334173309944184567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13752065778897746592246089 10314049334173309944184567)
      ·
        refine ⟨15471074001259964916276851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10314049334173309944184567 15471074001259964916276851)
        ·
          refine ⟨23206611001889947374415277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15471074001259964916276851 23206611001889947374415277)
          ·
            refine ⟨8702479125708730265405729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23206611001889947374415277 8702479125708730265405729)
            ·
              refine ⟨6526859344281547699054297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8702479125708730265405729 6526859344281547699054297)
              ·
                refine ⟨4895144508211160774290723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6526859344281547699054297 4895144508211160774290723)
                ·
                  refine ⟨7342716762316741161436085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895144508211160774290723 7342716762316741161436085)
                  ·
                    refine ⟨688379696467194483884633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7342716762316741161436085 688379696467194483884633)
                    ·
                      refine ⟨516284772350395862913475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688379696467194483884633 516284772350395862913475)
                      ·
                        rfl

theorem cell23_1005461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_1005461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005461 prefixEnd_1005461 := by exact prefixLift 1005461
  have htrace : WordTrace (prefixWord ++ tailWord_1005461) baseStart_1005461 baseEnd_1005461 := by
    simpa [prefixWord, tailWord_1005461, baseEnd_1005461] using wordTrace_append hprefix tailTrace_1005461
  have hstable : (prefixWord ++ tailWord_1005461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005461).length < 2 ^ (prefixWord ++ tailWord_1005461).sum := by decide
  have hdescent : baseEnd_1005461 < baseStart_1005461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005462 : List Nat := [5, 3, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1005462 : Nat := 118140960795 + 1005462 * 2 ^ 59
def prefixEnd_1005462 : Nat := 4983230072969 + 3 ^ 40 * 1005462 * 2
def baseEnd_1005462 : Nat := 172095095277016786333657

theorem tailTrace_1005462 : CollatzResearch.WordTrace tailWord_1005462 prefixEnd_1005462 172095095277016786333657 := by
  unfold tailWord_1005462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2292013242711898005215165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 24448141255593578722295093 2292013242711898005215165)
  ·
    refine ⟨859504966016961751955687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2292013242711898005215165 859504966016961751955687)
    ·
      refine ⟨1289257449025442627933531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859504966016961751955687 1289257449025442627933531)
      ·
        refine ⟨1933886173538163941900297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289257449025442627933531 1933886173538163941900297)
        ·
          refine ⟨1450414630153622956425223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1933886173538163941900297 1450414630153622956425223)
          ·
            refine ⟨2175621945230434434637835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1450414630153622956425223 2175621945230434434637835)
            ·
              refine ⟨3263432917845651651956753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175621945230434434637835 3263432917845651651956753)
              ·
                refine ⟨2447574688384238738967565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263432917845651651956753 2447574688384238738967565)
                ·
                  refine ⟨917840508144089527112837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2447574688384238738967565 917840508144089527112837)
                  ·
                    refine ⟨172095095277016786333657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 917840508144089527112837 172095095277016786333657)
                    ·
                      rfl

theorem cell23_1005462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1005462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005462 prefixEnd_1005462 := by exact prefixLift 1005462
  have htrace : WordTrace (prefixWord ++ tailWord_1005462) baseStart_1005462 baseEnd_1005462 := by
    simpa [prefixWord, tailWord_1005462, baseEnd_1005462] using wordTrace_append hprefix tailTrace_1005462
  have hstable : (prefixWord ++ tailWord_1005462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005462).length < 2 ^ (prefixWord ++ tailWord_1005462).sum := by decide
  have hdescent : baseEnd_1005462 < baseStart_1005462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005468 : List Nat := [2, 2, 3, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1005468 : Nat := 118140960795 + 1005468 * 2 ^ 59
def prefixEnd_1005468 : Nat := 4983230072969 + 3 ^ 40 * 1005468 * 2
def baseEnd_1005468 : Nat := 516288366714977335525943

theorem tailTrace_1005468 : CollatzResearch.WordTrace tailWord_1005468 prefixEnd_1005468 516288366714977335525943 := by
  unfold tailWord_1005468
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336215360684315554080529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24448287147579087405440705 18336215360684315554080529)
  ·
    refine ⟨13752161520513236665560397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18336215360684315554080529 13752161520513236665560397)
    ·
      refine ⟨5157060570192463749585149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13752161520513236665560397 5157060570192463749585149)
      ·
        refine ⟨1933897713822173906094431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5157060570192463749585149 1933897713822173906094431)
        ·
          refine ⟨2900846570733260859141647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1933897713822173906094431 2900846570733260859141647)
          ·
            refine ⟨4351269856099891288712471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2900846570733260859141647 4351269856099891288712471)
            ·
              refine ⟨6526904784149836933068707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4351269856099891288712471 6526904784149836933068707)
              ·
                refine ⟨9790357176224755399603061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526904784149836933068707 9790357176224755399603061)
                ·
                  refine ⟨917845985271070818712787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9790357176224755399603061 917845985271070818712787)
                  ·
                    refine ⟨1376768977906606228069181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917845985271070818712787 1376768977906606228069181)
                    ·
                      refine ⟨516288366714977335525943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376768977906606228069181 516288366714977335525943)
                      ·
                        rfl

theorem cell23_1005468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1005468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005468 prefixEnd_1005468 := by exact prefixLift 1005468
  have htrace : WordTrace (prefixWord ++ tailWord_1005468) baseStart_1005468 baseEnd_1005468 := by
    simpa [prefixWord, tailWord_1005468, baseEnd_1005468] using wordTrace_append hprefix tailTrace_1005468
  have hstable : (prefixWord ++ tailWord_1005468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005468).length < 2 ^ (prefixWord ++ tailWord_1005468).sum := by decide
  have hdescent : baseEnd_1005468 < baseStart_1005468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005491 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 4]
def baseStart_1005491 : Nat := 118140960795 + 1005491 * 2 ^ 59
def prefixEnd_1005491 : Nat := 4983230072969 + 3 ^ 40 * 1005491 * 2
def baseEnd_1005491 : Nat := 516300176770030745538337

theorem tailTrace_1005491 : CollatzResearch.WordTrace tailWord_1005491 prefixEnd_1005491 516300176770030745538337 := by
  unfold tailWord_1005491
  simp only [CollatzResearch.WordTrace]
  refine ⟨36673269600285306036248327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24448846400190204024165551 36673269600285306036248327)
  ·
    refine ⟨55009904400427959054372491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36673269600285306036248327 55009904400427959054372491)
    ·
      refine ⟨82514856600641938581558737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55009904400427959054372491 82514856600641938581558737)
      ·
        refine ⟨61886142450481453936169053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82514856600641938581558737 61886142450481453936169053)
        ·
          refine ⟨23207303418930545226063395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61886142450481453936169053 23207303418930545226063395)
          ·
            refine ⟨34810955128395817839095093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23207303418930545226063395 34810955128395817839095093)
            ·
              refine ⟨3263527043287107922415165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34810955128395817839095093 3263527043287107922415165)
              ·
                refine ⟨1223822641232665470905687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263527043287107922415165 1223822641232665470905687)
                ·
                  refine ⟨1835733961848998206358531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223822641232665470905687 1835733961848998206358531)
                  ·
                    refine ⟨2753600942773497309537797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1835733961848998206358531 2753600942773497309537797)
                    ·
                      refine ⟨516300176770030745538337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 2753600942773497309537797 516300176770030745538337)
                      ·
                        rfl

theorem cell23_1005491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_1005491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005491 prefixEnd_1005491 := by exact prefixLift 1005491
  have htrace : WordTrace (prefixWord ++ tailWord_1005491) baseStart_1005491 baseEnd_1005491 := by
    simpa [prefixWord, tailWord_1005491, baseEnd_1005491] using wordTrace_append hprefix tailTrace_1005491
  have hstable : (prefixWord ++ tailWord_1005491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005491).length < 2 ^ (prefixWord ++ tailWord_1005491).sum := by decide
  have hdescent : baseEnd_1005491 < baseStart_1005491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005492 : List Nat := [2, 5, 2, 1, 3, 1, 1, 2, 6]
def baseStart_1005492 : Nat := 118140960795 + 1005492 * 2 ^ 59
def prefixEnd_1005492 : Nat := 4983230072969 + 3 ^ 40 * 1005492 * 2
def baseEnd_1005492 : Nat := 57366743361187249069537

theorem tailTrace_1005492 : CollatzResearch.WordTrace tailWord_1005492 prefixEnd_1005492 57366743361187249069537 := by
  unfold tailWord_1005492
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336653036640841603517365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24448870715521122138023153 18336653036640841603517365)
  ·
    refine ⟨1719061222185078900329753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18336653036640841603517365 1719061222185078900329753)
    ·
      refine ⟨1289295916638809175247315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1719061222185078900329753 1289295916638809175247315)
      ·
        refine ⟨1933943874958213762870973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289295916638809175247315 1933943874958213762870973)
        ·
          refine ⟨725228953109330161076615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1933943874958213762870973 725228953109330161076615)
          ·
            refine ⟨1087843429663995241614923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725228953109330161076615 1087843429663995241614923)
            ·
              refine ⟨1631765144495992862422385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1087843429663995241614923 1631765144495992862422385)
              ·
                refine ⟨1223823858371994646816789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631765144495992862422385 1223823858371994646816789)
                ·
                  refine ⟨57366743361187249069537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1223823858371994646816789 57366743361187249069537)
                  ·
                    rfl

theorem cell23_1005492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_1005492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005492 prefixEnd_1005492 := by exact prefixLift 1005492
  have htrace : WordTrace (prefixWord ++ tailWord_1005492) baseStart_1005492 baseEnd_1005492 := by
    simpa [prefixWord, tailWord_1005492, baseEnd_1005492] using wordTrace_append hprefix tailTrace_1005492
  have hstable : (prefixWord ++ tailWord_1005492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005492).length < 2 ^ (prefixWord ++ tailWord_1005492).sum := by decide
  have hdescent : baseEnd_1005492 < baseStart_1005492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005504 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_1005504 : Nat := 118140960795 + 1005504 * 2 ^ 59
def prefixEnd_1005504 : Nat := 4983230072969 + 3 ^ 40 * 1005504 * 2
def baseEnd_1005504 : Nat := 516306852018539194675777

theorem tailTrace_1005504 : CollatzResearch.WordTrace tailWord_1005504 prefixEnd_1005504 516306852018539194675777 := by
  unfold tailWord_1005504
  simp only [CollatzResearch.WordTrace]
  refine ⟨18336871874619104628235783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24449162499492139504314377 18336871874619104628235783)
  ·
    refine ⟨27505307811928656942353675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18336871874619104628235783 27505307811928656942353675)
    ·
      refine ⟨41257961717892985413530513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27505307811928656942353675 41257961717892985413530513)
      ·
        refine ⟨30943471288419739060147885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41257961717892985413530513 30943471288419739060147885)
        ·
          refine ⟨11603801733157402147555457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30943471288419739060147885 11603801733157402147555457)
          ·
            refine ⟨8702851299868051610666593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11603801733157402147555457 8702851299868051610666593)
            ·
              refine ⟨6527138474901038707999945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8702851299868051610666593 6527138474901038707999945)
              ·
                refine ⟨4895353856175779030999959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527138474901038707999945 4895353856175779030999959)
                ·
                  refine ⟨7343030784263668546499939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895353856175779030999959 7343030784263668546499939)
                  ·
                    refine ⟨11014546176395502819749909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7343030784263668546499939 11014546176395502819749909)
                    ·
                      refine ⟨516306852018539194675777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 11014546176395502819749909 516306852018539194675777)
                      ·
                        rfl

theorem cell23_1005504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_1005504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005504 prefixEnd_1005504 := by exact prefixLift 1005504
  have htrace : WordTrace (prefixWord ++ tailWord_1005504) baseStart_1005504 baseEnd_1005504 := by
    simpa [prefixWord, tailWord_1005504, baseEnd_1005504] using wordTrace_append hprefix tailTrace_1005504
  have hstable : (prefixWord ++ tailWord_1005504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005504).length < 2 ^ (prefixWord ++ tailWord_1005504).sum := by decide
  have hdescent : baseEnd_1005504 < baseStart_1005504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005525 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1005525 : Nat := 118140960795 + 1005525 * 2 ^ 59
def prefixEnd_1005525 : Nat := 4983230072969 + 3 ^ 40 * 1005525 * 2
def baseEnd_1005525 : Nat := 516317635112283612513181

theorem tailTrace_1005525 : CollatzResearch.WordTrace tailWord_1005525 prefixEnd_1005525 516317635112283612513181 := by
  unfold tailWord_1005525
  simp only [CollatzResearch.WordTrace]
  refine ⟨36674509682162129842986029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24449673121441419895324019 36674509682162129842986029)
  ·
    refine ⟨13752941130810798691119761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36674509682162129842986029 13752941130810798691119761)
    ·
      refine ⟨10314705848108099018339821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13752941130810798691119761 10314705848108099018339821)
      ·
        refine ⟨3868014693040537131877433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10314705848108099018339821 3868014693040537131877433)
        ·
          refine ⟨2901011019780402848908075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3868014693040537131877433 2901011019780402848908075)
          ·
            refine ⟨4351516529670604273362113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2901011019780402848908075 4351516529670604273362113)
            ·
              refine ⟨3263637397252953205021585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4351516529670604273362113 3263637397252953205021585)
              ·
                refine ⟨2447728047939714903766189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3263637397252953205021585 2447728047939714903766189)
                ·
                  refine ⟨917898017977393088912321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2447728047939714903766189 917898017977393088912321)
                  ·
                    refine ⟨688423513483044816684241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 917898017977393088912321 688423513483044816684241)
                    ·
                      refine ⟨516317635112283612513181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688423513483044816684241 516317635112283612513181)
                      ·
                        rfl

theorem cell23_1005525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1005525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005525 prefixEnd_1005525 := by exact prefixLift 1005525
  have htrace : WordTrace (prefixWord ++ tailWord_1005525) baseStart_1005525 baseEnd_1005525 := by
    simpa [prefixWord, tailWord_1005525, baseEnd_1005525] using wordTrace_append hprefix tailTrace_1005525
  have hstable : (prefixWord ++ tailWord_1005525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005525).length < 2 ^ (prefixWord ++ tailWord_1005525).sum := by decide
  have hdescent : baseEnd_1005525 < baseStart_1005525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005528 : List Nat := [2, 1, 2, 2, 2, 2, 4, 2, 1, 2, 3]
def baseStart_1005528 : Nat := 118140960795 + 1005528 * 2 ^ 59
def prefixEnd_1005528 : Nat := 4983230072969 + 3 ^ 40 * 1005528 * 2
def baseEnd_1005528 : Nat := 516319175554247100775667

theorem tailTrace_1005528 : CollatzResearch.WordTrace tailWord_1005528 prefixEnd_1005528 516319175554247100775667 := by
  unfold tailWord_1005528
  simp only [CollatzResearch.WordTrace]
  refine ⟨18337309550575630677672619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24449746067434174236896825 18337309550575630677672619)
  ·
    refine ⟨27505964325863446016508929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18337309550575630677672619 27505964325863446016508929)
    ·
      refine ⟨20629473244397584512381697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27505964325863446016508929 20629473244397584512381697)
      ·
        refine ⟨15472104933298188384286273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20629473244397584512381697 15472104933298188384286273)
        ·
          refine ⟨11604078699973641288214705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15472104933298188384286273 11604078699973641288214705)
          ·
            refine ⟨8703059024980230966161029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11604078699973641288214705 8703059024980230966161029)
            ·
              refine ⟨1631823567183793306155193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8703059024980230966161029 1631823567183793306155193)
              ·
                refine ⟨1223867675387844979616395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1631823567183793306155193 1223867675387844979616395)
                ·
                  refine ⟨1835801513081767469424593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223867675387844979616395 1835801513081767469424593)
                  ·
                    refine ⟨1376851134811325602068445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1835801513081767469424593 1376851134811325602068445)
                    ·
                      refine ⟨516319175554247100775667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376851134811325602068445 516319175554247100775667)
                      ·
                        rfl

theorem cell23_1005528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 2, 1, 2, 3].length) (baseStart_1005528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005528 prefixEnd_1005528 := by exact prefixLift 1005528
  have htrace : WordTrace (prefixWord ++ tailWord_1005528) baseStart_1005528 baseEnd_1005528 := by
    simpa [prefixWord, tailWord_1005528, baseEnd_1005528] using wordTrace_append hprefix tailTrace_1005528
  have hstable : (prefixWord ++ tailWord_1005528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005528).length < 2 ^ (prefixWord ++ tailWord_1005528).sum := by decide
  have hdescent : baseEnd_1005528 < baseStart_1005528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005544 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1005544 : Nat := 118140960795 + 1005544 * 2 ^ 59
def prefixEnd_1005544 : Nat := 4983230072969 + 3 ^ 40 * 1005544 * 2
def baseEnd_1005544 : Nat := 172109130414906346058531

theorem tailTrace_1005544 : CollatzResearch.WordTrace tailWord_1005544 prefixEnd_1005544 172109130414906346058531 := by
  unfold tailWord_1005544
  simp only [CollatzResearch.WordTrace]
  refine ⟨18337601334546648043963843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24450135112728864058618457 18337601334546648043963843)
  ·
    refine ⟨27506402001819972065945765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18337601334546648043963843 27506402001819972065945765)
    ·
      refine ⟨5157450375341244762364831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27506402001819972065945765 5157450375341244762364831)
      ·
        refine ⟨7736175563011867143547247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157450375341244762364831 7736175563011867143547247)
        ·
          refine ⟨11604263344517800715320871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736175563011867143547247 11604263344517800715320871)
          ·
            refine ⟨17406395016776701072981307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604263344517800715320871 17406395016776701072981307)
            ·
              refine ⟨26109592525165051609471961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406395016776701072981307 26109592525165051609471961)
              ·
                refine ⟨19582194393873788707103971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26109592525165051609471961 19582194393873788707103971)
                ·
                  refine ⟨29373291590810683060655957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19582194393873788707103971 29373291590810683060655957)
                  ·
                    refine ⟨172109130414906346058531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 29373291590810683060655957 172109130414906346058531)
                    ·
                      rfl

theorem cell23_1005544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1005544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005544 prefixEnd_1005544 := by exact prefixLift 1005544
  have htrace : WordTrace (prefixWord ++ tailWord_1005544) baseStart_1005544 baseEnd_1005544 := by
    simpa [prefixWord, tailWord_1005544, baseEnd_1005544] using wordTrace_append hprefix tailTrace_1005544
  have hstable : (prefixWord ++ tailWord_1005544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005544).length < 2 ^ (prefixWord ++ tailWord_1005544).sum := by decide
  have hdescent : baseEnd_1005544 < baseStart_1005544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005575 : List Nat := [1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1005575 : Nat := 118140960795 + 1005575 * 2 ^ 59
def prefixEnd_1005575 : Nat := 4983230072969 + 3 ^ 40 * 1005575 * 2
def baseEnd_1005575 : Nat := 516343309145008416887951

theorem tailTrace_1005575 : CollatzResearch.WordTrace tailWord_1005575 prefixEnd_1005575 516343309145008416887951 := by
  unfold tailWord_1005575
  simp only [CollatzResearch.WordTrace]
  refine ⟨36676333331980988382306179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24450888887987325588204119 36676333331980988382306179)
  ·
    refine ⟨55014499997971482573459269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36676333331980988382306179 55014499997971482573459269)
    ·
      refine ⟨10315218749619652982523613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55014499997971482573459269 10315218749619652982523613)
      ·
        refine ⟨3868207031107369868446355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10315218749619652982523613 3868207031107369868446355)
        ·
          refine ⟨5802310546661054802669533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3868207031107369868446355 5802310546661054802669533)
          ·
            refine ⟨2175866454997895551001075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5802310546661054802669533 2175866454997895551001075)
            ·
              refine ⟨3263799682496843326501613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2175866454997895551001075 3263799682496843326501613)
              ·
                refine ⟨1223924880936316247438105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3263799682496843326501613 1223924880936316247438105)
                ·
                  refine ⟨917943660702237185578579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1223924880936316247438105 917943660702237185578579)
                  ·
                    refine ⟨1376915491053355778367869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 917943660702237185578579 1376915491053355778367869)
                    ·
                      refine ⟨516343309145008416887951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376915491053355778367869 516343309145008416887951)
                      ·
                        rfl

theorem cell23_1005575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1005575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005575 prefixEnd_1005575 := by exact prefixLift 1005575
  have htrace : WordTrace (prefixWord ++ tailWord_1005575) baseStart_1005575 baseEnd_1005575 := by
    simpa [prefixWord, tailWord_1005575, baseEnd_1005575] using wordTrace_append hprefix tailTrace_1005575
  have hstable : (prefixWord ++ tailWord_1005575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005575).length < 2 ^ (prefixWord ++ tailWord_1005575).sum := by decide
  have hdescent : baseEnd_1005575 < baseStart_1005575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005584 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_1005584 : Nat := 118140960795 + 1005584 * 2 ^ 59
def prefixEnd_1005584 : Nat := 4983230072969 + 3 ^ 40 * 1005584 * 2
def baseEnd_1005584 : Nat := 516347930470898881675409

theorem tailTrace_1005584 : CollatzResearch.WordTrace tailWord_1005584 prefixEnd_1005584 516347930470898881675409 := by
  unfold tailWord_1005584
  simp only [CollatzResearch.WordTrace]
  refine ⟨18338330794474191459691903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 24451107725965588612922537 18338330794474191459691903)
  ·
    refine ⟨27507496191711287189537855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18338330794474191459691903 27507496191711287189537855)
    ·
      refine ⟨41261244287566930784306783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27507496191711287189537855 41261244287566930784306783)
      ·
        refine ⟨61891866431350396176460175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41261244287566930784306783 61891866431350396176460175)
        ·
          refine ⟨92837799647025594264690263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61891866431350396176460175 92837799647025594264690263)
          ·
            refine ⟨139256699470538391397035395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92837799647025594264690263 139256699470538391397035395)
            ·
              refine ⟨208885049205807587095553093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139256699470538391397035395 208885049205807587095553093)
              ·
                refine ⟨39165946726088922580416205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208885049205807587095553093 39165946726088922580416205)
                ·
                  refine ⟨14687230022283345967656077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39165946726088922580416205 14687230022283345967656077)
                  ·
                    refine ⟨5507711258356254737871029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14687230022283345967656077 5507711258356254737871029)
                    ·
                      refine ⟨516347930470898881675409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 5507711258356254737871029 516347930470898881675409)
                      ·
                        rfl

theorem cell23_1005584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_1005584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005584 prefixEnd_1005584 := by exact prefixLift 1005584
  have htrace : WordTrace (prefixWord ++ tailWord_1005584) baseStart_1005584 baseEnd_1005584 := by
    simpa [prefixWord, tailWord_1005584, baseEnd_1005584] using wordTrace_append hprefix tailTrace_1005584
  have hstable : (prefixWord ++ tailWord_1005584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005584).length < 2 ^ (prefixWord ++ tailWord_1005584).sum := by decide
  have hdescent : baseEnd_1005584 < baseStart_1005584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005602 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_1005602 : Nat := 118140960795 + 1005602 * 2 ^ 59
def prefixEnd_1005602 : Nat := 4983230072969 + 3 ^ 40 * 1005602 * 2
def baseEnd_1005602 : Nat := 516357173122679811250327

theorem tailTrace_1005602 : CollatzResearch.WordTrace tailWord_1005602 prefixEnd_1005602 516357173122679811250327 := by
  unfold tailWord_1005602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9169329525720792998384765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 24451545401922114662359373 9169329525720792998384765)
  ·
    refine ⟨3438498572145297374394287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9169329525720792998384765 3438498572145297374394287)
    ·
      refine ⟨5157747858217946061591431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438498572145297374394287 5157747858217946061591431)
      ·
        refine ⟨7736621787326919092387147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157747858217946061591431 7736621787326919092387147)
        ·
          refine ⟨11604932680990378638580721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7736621787326919092387147 11604932680990378638580721)
          ·
            refine ⟨8703699510742783978935541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11604932680990378638580721 8703699510742783978935541)
            ·
              refine ⟨815971829132135998025207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8703699510742783978935541 815971829132135998025207)
              ·
                refine ⟨1223957743698203997037811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 815971829132135998025207 1223957743698203997037811)
                ·
                  refine ⟨1835936615547305995556717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1223957743698203997037811 1835936615547305995556717)
                  ·
                    refine ⟨688476230830239748333769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1835936615547305995556717 688476230830239748333769)
                    ·
                      refine ⟨516357173122679811250327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 688476230830239748333769 516357173122679811250327)
                      ·
                        rfl

theorem cell23_1005602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_1005602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005602 prefixEnd_1005602 := by exact prefixLift 1005602
  have htrace : WordTrace (prefixWord ++ tailWord_1005602) baseStart_1005602 baseEnd_1005602 := by
    simpa [prefixWord, tailWord_1005602, baseEnd_1005602] using wordTrace_append hprefix tailTrace_1005602
  have hstable : (prefixWord ++ tailWord_1005602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005602).length < 2 ^ (prefixWord ++ tailWord_1005602).sum := by decide
  have hdescent : baseEnd_1005602 < baseStart_1005602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1005631 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 3]
def baseStart_1005631 : Nat := 118140960795 + 1005631 * 2 ^ 59
def prefixEnd_1005631 : Nat := 4983230072969 + 3 ^ 40 * 1005631 * 2
def baseEnd_1005631 : Nat := 516372064061660197787693

theorem tailTrace_1005631 : CollatzResearch.WordTrace tailWord_1005631 prefixEnd_1005631 516372064061660197787693 := by
  unfold tailWord_1005631
  simp only [CollatzResearch.WordTrace]
  refine ⟨36678375819778109946344747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 24452250546518739964229831 36678375819778109946344747)
  ·
    refine ⟨55017563729667164919517121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36678375819778109946344747 55017563729667164919517121)
    ·
      refine ⟨41263172797250373689637841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55017563729667164919517121 41263172797250373689637841)
      ·
        refine ⟨30947379597937780267228381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41263172797250373689637841 30947379597937780267228381)
        ·
          refine ⟨11605267349226667600210643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30947379597937780267228381 11605267349226667600210643)
          ·
            refine ⟨17407901023840001400315965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11605267349226667600210643 17407901023840001400315965)
            ·
              refine ⟨6527962883940000525118487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17407901023840001400315965 6527962883940000525118487)
              ·
                refine ⟨9791944325910000787677731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527962883940000525118487 9791944325910000787677731)
                ·
                  refine ⟨14687916488865001181516597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9791944325910000787677731 14687916488865001181516597)
                  ·
                    refine ⟨1376992170831093860767181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14687916488865001181516597 1376992170831093860767181)
                    ·
                      refine ⟨516372064061660197787693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1376992170831093860767181 516372064061660197787693)
                      ·
                        rfl

theorem cell23_1005631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 1, 5, 3].length) (baseStart_1005631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1005631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1005631 prefixEnd_1005631 := by exact prefixLift 1005631
  have htrace : WordTrace (prefixWord ++ tailWord_1005631) baseStart_1005631 baseEnd_1005631 := by
    simpa [prefixWord, tailWord_1005631, baseEnd_1005631] using wordTrace_append hprefix tailTrace_1005631
  have hstable : (prefixWord ++ tailWord_1005631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1005631).length < 2 ^ (prefixWord ++ tailWord_1005631).sum := by decide
  have hdescent : baseEnd_1005631 < baseStart_1005631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1005631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
