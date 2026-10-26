import V185TrunkScan23Chunk1107

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6561754 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2]
def baseStart_6561754 : Nat := 118140960795 + 6561754 * 2 ^ 59
def prefixEnd_6561754 : Nat := 4983230072969 + 3 ^ 40 * 6561754 * 2
def baseEnd_6561754 : Nat := 3369333738562425340998049

theorem tailTrace_6561754 : CollatzResearch.WordTrace tailWord_6561754 prefixEnd_6561754 3369333738562425340998049 := by
  unfold tailWord_6561754
  simp only [CollatzResearch.WordTrace]
  refine ⟨59831707467473347802035079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159551219913262260805426877 59831707467473347802035079)
  ·
    refine ⟨89747561201210021703052619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59831707467473347802035079 89747561201210021703052619)
    ·
      refine ⟨134621341801815032554578929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89747561201210021703052619 134621341801815032554578929)
      ·
        refine ⟨100966006351361274415934197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134621341801815032554578929 100966006351361274415934197)
        ·
          refine ⟨9465563095440119476493831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100966006351361274415934197 9465563095440119476493831)
          ·
            refine ⟨14198344643160179214740747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9465563095440119476493831 14198344643160179214740747)
            ·
              refine ⟨21297516964740268822111121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14198344643160179214740747 21297516964740268822111121)
              ·
                refine ⟨15973137723555201616583341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21297516964740268822111121 15973137723555201616583341)
                ·
                  refine ⟨5989926646333200606218753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15973137723555201616583341 5989926646333200606218753)
                  ·
                    refine ⟨4492444984749900454664065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989926646333200606218753 4492444984749900454664065)
                    ·
                      refine ⟨3369333738562425340998049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492444984749900454664065 3369333738562425340998049)
                      ·
                        rfl

theorem cell23_6561754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_6561754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561754 prefixEnd_6561754 := by exact prefixLift 6561754
  have htrace : WordTrace (prefixWord ++ tailWord_6561754) baseStart_6561754 baseEnd_6561754 := by
    simpa [prefixWord, tailWord_6561754, baseEnd_6561754] using wordTrace_append hprefix tailTrace_6561754
  have hstable : (prefixWord ++ tailWord_6561754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561754).length < 2 ^ (prefixWord ++ tailWord_6561754).sum := by decide
  have hdescent : baseEnd_6561754 < baseStart_6561754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561770 : List Nat := [3, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_6561770 : Nat := 118140960795 + 6561770 * 2 ^ 59
def prefixEnd_6561770 : Nat := 4983230072969 + 3 ^ 40 * 6561770 * 2
def baseEnd_6561770 : Nat := 3369341954252897278397975

theorem tailTrace_6561770 : CollatzResearch.WordTrace tailWord_6561770 prefixEnd_6561770 3369341954252897278397975 := by
  unfold tailWord_6561770
  simp only [CollatzResearch.WordTrace]
  refine ⟨59831853359458856485180691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159551608958556950627148509 59831853359458856485180691)
  ·
    refine ⟨89747780039188284727771037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59831853359458856485180691 89747780039188284727771037)
    ·
      refine ⟨33655417514695606772914139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89747780039188284727771037 33655417514695606772914139)
      ·
        refine ⟨50483126272043410159371209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33655417514695606772914139 50483126272043410159371209)
        ·
          refine ⟨37862344704032557619528407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50483126272043410159371209 37862344704032557619528407)
          ·
            refine ⟨56793517056048836429292611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37862344704032557619528407 56793517056048836429292611)
            ·
              refine ⟨85190275584073254643938917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56793517056048836429292611 85190275584073254643938917)
              ·
                refine ⟨15973176672013735245738547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85190275584073254643938917 15973176672013735245738547)
                ·
                  refine ⟨23959765008020602868607821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15973176672013735245738547 23959765008020602868607821)
                  ·
                    refine ⟨8984911878007726075727933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23959765008020602868607821 8984911878007726075727933)
                    ·
                      refine ⟨3369341954252897278397975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984911878007726075727933 3369341954252897278397975)
                      ·
                        rfl

theorem cell23_6561770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_6561770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561770 prefixEnd_6561770 := by exact prefixLift 6561770
  have htrace : WordTrace (prefixWord ++ tailWord_6561770) baseStart_6561770 baseEnd_6561770 := by
    simpa [prefixWord, tailWord_6561770, baseEnd_6561770] using wordTrace_append hprefix tailTrace_6561770
  have hstable : (prefixWord ++ tailWord_6561770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561770).length < 2 ^ (prefixWord ++ tailWord_6561770).sum := by decide
  have hdescent : baseEnd_6561770 < baseStart_6561770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561774 : List Nat := [4, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_6561774 : Nat := 118140960795 + 6561774 * 2 ^ 59
def prefixEnd_6561774 : Nat := 4983230072969 + 3 ^ 40 * 6561774 * 2
def baseEnd_6561774 : Nat := 3369344008175515262747957

theorem tailTrace_6561774 : CollatzResearch.WordTrace tailWord_6561774 prefixEnd_6561774 3369344008175515262747957 := by
  unfold tailWord_6561774
  simp only [CollatzResearch.WordTrace]
  refine ⟨29915944916227616827983547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159551706219880623082578917 29915944916227616827983547)
  ·
    refine ⟨44873917374341425241975321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29915944916227616827983547 44873917374341425241975321)
    ·
      refine ⟨33655438030756068931481491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44873917374341425241975321 33655438030756068931481491)
      ·
        refine ⟨50483157046134103397222237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33655438030756068931481491 50483157046134103397222237)
        ·
          refine ⟨18931183892300288773958339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50483157046134103397222237 18931183892300288773958339)
          ·
            refine ⟨28396775838450433160937509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18931183892300288773958339 28396775838450433160937509)
            ·
              refine ⟨5324395469709456217675783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28396775838450433160937509 5324395469709456217675783)
              ·
                refine ⟨7986593204564184326513675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324395469709456217675783 7986593204564184326513675)
                ·
                  refine ⟨11979889806846276489770513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7986593204564184326513675 11979889806846276489770513)
                  ·
                    refine ⟨8984917355134707367327885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11979889806846276489770513 8984917355134707367327885)
                    ·
                      refine ⟨3369344008175515262747957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984917355134707367327885 3369344008175515262747957)
                      ·
                        rfl

theorem cell23_6561774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_6561774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561774 prefixEnd_6561774 := by exact prefixLift 6561774
  have htrace : WordTrace (prefixWord ++ tailWord_6561774) baseStart_6561774 baseEnd_6561774 := by
    simpa [prefixWord, tailWord_6561774, baseEnd_6561774] using wordTrace_append hprefix tailTrace_6561774
  have hstable : (prefixWord ++ tailWord_6561774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561774).length < 2 ^ (prefixWord ++ tailWord_6561774).sum := by decide
  have hdescent : baseEnd_6561774 < baseStart_6561774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561787 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 3]
def baseStart_6561787 : Nat := 118140960795 + 6561787 * 2 ^ 59
def prefixEnd_6561787 : Nat := 4983230072969 + 3 ^ 40 * 6561787 * 2
def baseEnd_6561787 : Nat := 3369350683424023711885397

theorem tailTrace_6561787 : CollatzResearch.WordTrace tailWord_6561787 prefixEnd_6561787 3369350683424023711885397 := by
  unfold tailWord_6561787
  simp only [CollatzResearch.WordTrace]
  refine ⟨239328033478773837844091615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159552022319182558562727743 239328033478773837844091615)
  ·
    refine ⟨358992050218160756766137423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239328033478773837844091615 358992050218160756766137423)
    ·
      refine ⟨538488075327241135149206135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358992050218160756766137423 538488075327241135149206135)
      ·
        refine ⟨807732112990861702723809203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538488075327241135149206135 807732112990861702723809203)
        ·
          refine ⟨1211598169486292554085713805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807732112990861702723809203 1211598169486292554085713805)
          ·
            refine ⟨454349313557359707782142677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1211598169486292554085713805 454349313557359707782142677)
            ·
              refine ⟨10648812036500618151143969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 454349313557359707782142677 10648812036500618151143969)
              ·
                refine ⟨7986609027375463613357977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10648812036500618151143969 7986609027375463613357977)
                ·
                  refine ⟨5989956770531597710018483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7986609027375463613357977 5989956770531597710018483)
                  ·
                    refine ⟨8984935155797396565027725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5989956770531597710018483 8984935155797396565027725)
                    ·
                      refine ⟨3369350683424023711885397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984935155797396565027725 3369350683424023711885397)
                      ·
                        rfl

theorem cell23_6561787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 2, 1, 3].length) (baseStart_6561787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561787 prefixEnd_6561787 := by exact prefixLift 6561787
  have htrace : WordTrace (prefixWord ++ tailWord_6561787) baseStart_6561787 baseEnd_6561787 := by
    simpa [prefixWord, tailWord_6561787, baseEnd_6561787] using wordTrace_append hprefix tailTrace_6561787
  have hstable : (prefixWord ++ tailWord_6561787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561787).length < 2 ^ (prefixWord ++ tailWord_6561787).sum := by decide
  have hdescent : baseEnd_6561787 < baseStart_6561787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561798 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6561798 : Nat := 118140960795 + 6561798 * 2 ^ 59
def prefixEnd_6561798 : Nat := 4983230072969 + 3 ^ 40 * 6561798 * 2
def baseEnd_6561798 : Nat := 1123118777237074389615949

theorem tailTrace_6561798 : CollatzResearch.WordTrace tailWord_6561798 prefixEnd_6561798 1123118777237074389615949 := by
  unfold tailWord_6561798
  simp only [CollatzResearch.WordTrace]
  refine ⟨7479013583804187085085689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159552289787822657815161365 7479013583804187085085689)
  ·
    refine ⟨5609260187853140313814267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7479013583804187085085689 5609260187853140313814267)
    ·
      refine ⟨8413890281779710470721401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5609260187853140313814267 8413890281779710470721401)
      ·
        refine ⟨6310417711334782853041051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8413890281779710470721401 6310417711334782853041051)
        ·
          refine ⟨9465626567002174279561577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310417711334782853041051 9465626567002174279561577)
          ·
            refine ⟨7099219925251630709671183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9465626567002174279561577 7099219925251630709671183)
            ·
              refine ⟨10648829887877446064506775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099219925251630709671183 10648829887877446064506775)
              ·
                refine ⟨15973244831816169096760163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10648829887877446064506775 15973244831816169096760163)
                ·
                  refine ⟨23959867247724253645140245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15973244831816169096760163 23959867247724253645140245)
                  ·
                    refine ⟨1123118777237074389615949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23959867247724253645140245 1123118777237074389615949)
                    ·
                      rfl

theorem cell23_6561798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6561798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561798 prefixEnd_6561798 := by exact prefixLift 6561798
  have htrace : WordTrace (prefixWord ++ tailWord_6561798) baseStart_6561798 baseEnd_6561798 := by
    simpa [prefixWord, tailWord_6561798, baseEnd_6561798] using wordTrace_append hprefix tailTrace_6561798
  have hstable : (prefixWord ++ tailWord_6561798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561798).length < 2 ^ (prefixWord ++ tailWord_6561798).sum := by decide
  have hdescent : baseEnd_6561798 < baseStart_6561798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561803 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 2, 6]
def baseStart_6561803 : Nat := 118140960795 + 6561803 * 2 ^ 59
def prefixEnd_6561803 : Nat := 4983230072969 + 3 ^ 40 * 6561803 * 2
def baseEnd_6561803 : Nat := 1123119633038165216428441

theorem tailTrace_6561803 : CollatzResearch.WordTrace tailWord_6561803 prefixEnd_6561803 1123119633038165216428441 := by
  unfold tailWord_6561803
  simp only [CollatzResearch.WordTrace]
  refine ⟨239328617046715872576674063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159552411364477248384449375 239328617046715872576674063)
  ·
    refine ⟨358992925570073808865011095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239328617046715872576674063 358992925570073808865011095)
    ·
      refine ⟨538489388355110713297516643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358992925570073808865011095 538489388355110713297516643)
      ·
        refine ⟨807734082532666069946274965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538489388355110713297516643 807734082532666069946274965)
        ·
          refine ⟨37862535118718722028731639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 807734082532666069946274965 37862535118718722028731639)
          ·
            refine ⟨56793802678078083043097459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37862535118718722028731639 56793802678078083043097459)
            ·
              refine ⟨85190704017117124564646189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56793802678078083043097459 85190704017117124564646189)
              ·
                refine ⟨31946514006418921711742321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85190704017117124564646189 31946514006418921711742321)
                ·
                  refine ⟨23959885504814191283806741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31946514006418921711742321 23959885504814191283806741)
                  ·
                    refine ⟨1123119633038165216428441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23959885504814191283806741 1123119633038165216428441)
                    ·
                      rfl

theorem cell23_6561803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 6].length) (baseStart_6561803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561803 prefixEnd_6561803 := by exact prefixLift 6561803
  have htrace : WordTrace (prefixWord ++ tailWord_6561803) baseStart_6561803 baseEnd_6561803 := by
    simpa [prefixWord, tailWord_6561803, baseEnd_6561803] using wordTrace_append hprefix tailTrace_6561803
  have hstable : (prefixWord ++ tailWord_6561803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561803).length < 2 ^ (prefixWord ++ tailWord_6561803).sum := by decide
  have hdescent : baseEnd_6561803 < baseStart_6561803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561804 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 2, 1, 3]
def baseStart_6561804 : Nat := 118140960795 + 6561804 * 2 ^ 59
def prefixEnd_6561804 : Nat := 4983230072969 + 3 ^ 40 * 6561804 * 2
def baseEnd_6561804 : Nat := 3369359412595150145372819

theorem tailTrace_6561804 : CollatzResearch.WordTrace tailWord_6561804 prefixEnd_6561804 3369359412595150145372819 := by
  unfold tailWord_6561804
  simp only [CollatzResearch.WordTrace]
  refine ⟨119664326759856124873730233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159552435679808166498306977 119664326759856124873730233)
  ·
    refine ⟨89748245069892093655297675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119664326759856124873730233 89748245069892093655297675)
    ·
      refine ⟨134622367604838140482946513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89748245069892093655297675 134622367604838140482946513)
      ·
        refine ⟨100966775703628605362209885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134622367604838140482946513 100966775703628605362209885)
        ·
          refine ⟨37862540888860727010828707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100966775703628605362209885 37862540888860727010828707)
          ·
            refine ⟨56793811333291090516243061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37862540888860727010828707 56793811333291090516243061)
            ·
              refine ⟨5324419812496039735897787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56793811333291090516243061 5324419812496039735897787)
              ·
                refine ⟨7986629718744059603846681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5324419812496039735897787 7986629718744059603846681)
                ·
                  refine ⟨5989972289058044702885011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7986629718744059603846681 5989972289058044702885011)
                  ·
                    refine ⟨8984958433587067054327517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5989972289058044702885011 8984958433587067054327517)
                    ·
                      refine ⟨3369359412595150145372819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8984958433587067054327517 3369359412595150145372819)
                      ·
                        rfl

theorem cell23_6561804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_6561804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561804 prefixEnd_6561804 := by exact prefixLift 6561804
  have htrace : WordTrace (prefixWord ++ tailWord_6561804) baseStart_6561804 baseEnd_6561804 := by
    simpa [prefixWord, tailWord_6561804, baseEnd_6561804] using wordTrace_append hprefix tailTrace_6561804
  have hstable : (prefixWord ++ tailWord_6561804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561804).length < 2 ^ (prefixWord ++ tailWord_6561804).sum := by decide
  have hdescent : baseEnd_6561804 < baseStart_6561804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561827 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 6, 2, 2]
def baseStart_6561827 : Nat := 118140960795 + 6561827 * 2 ^ 59
def prefixEnd_6561827 : Nat := 4983230072969 + 3 ^ 40 * 6561827 * 2
def baseEnd_6561827 : Nat := 3369371222650203555385213

theorem tailTrace_6561827 : CollatzResearch.WordTrace tailWord_6561827 prefixEnd_6561827 3369371222650203555385213 := by
  unfold tailWord_6561827
  simp only [CollatzResearch.WordTrace]
  refine ⟨239329492398628924675547735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159552994932419283117031823 239329492398628924675547735)
  ·
    refine ⟨358994238597943387013321603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239329492398628924675547735 358994238597943387013321603)
    ·
      refine ⟨538491357896915080519982405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358994238597943387013321603 538491357896915080519982405)
      ·
        refine ⟨100967129605671577597496701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 538491357896915080519982405 100967129605671577597496701)
        ·
          refine ⟨37862673602126841599061263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100967129605671577597496701 37862673602126841599061263)
          ·
            refine ⟨56794010403190262398591895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37862673602126841599061263 56794010403190262398591895)
            ·
              refine ⟨85191015604785393597887843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56794010403190262398591895 85191015604785393597887843)
              ·
                refine ⟨127786523407178090396831765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85191015604785393597887843 127786523407178090396831765)
                ·
                  refine ⟨5989993284711472987351489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127786523407178090396831765 5989993284711472987351489)
                  ·
                    refine ⟨4492494963533604740513617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5989993284711472987351489 4492494963533604740513617)
                    ·
                      refine ⟨3369371222650203555385213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492494963533604740513617 3369371222650203555385213)
                      ·
                        rfl

theorem cell23_6561827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_6561827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561827 prefixEnd_6561827 := by exact prefixLift 6561827
  have htrace : WordTrace (prefixWord ++ tailWord_6561827) baseStart_6561827 baseEnd_6561827 := by
    simpa [prefixWord, tailWord_6561827, baseEnd_6561827] using wordTrace_append hprefix tailTrace_6561827
  have hstable : (prefixWord ++ tailWord_6561827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561827).length < 2 ^ (prefixWord ++ tailWord_6561827).sum := by decide
  have hdescent : baseEnd_6561827 < baseStart_6561827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561873 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_6561873 : Nat := 118140960795 + 6561873 * 2 ^ 59
def prefixEnd_6561873 : Nat := 4983230072969 + 3 ^ 40 * 6561873 * 2
def baseEnd_6561873 : Nat := 3369394842760310375410001

theorem tailTrace_6561873 : CollatzResearch.WordTrace tailWord_6561873 prefixEnd_6561873 3369394842760310375410001 := by
  unfold tailWord_6561873
  simp only [CollatzResearch.WordTrace]
  refine ⟨239331170156462274531722273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159554113437641516354481515 239331170156462274531722273)
  ·
    refine ⟨179498377617346705898791705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239331170156462274531722273 179498377617346705898791705)
    ·
      refine ⟨134623783213010029424093779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179498377617346705898791705 134623783213010029424093779)
      ·
        refine ⟨201935674819515044136140669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134623783213010029424093779 201935674819515044136140669)
        ·
          refine ⟨75725878057318141551052751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201935674819515044136140669 75725878057318141551052751)
          ·
            refine ⟨113588817085977212326579127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75725878057318141551052751 113588817085977212326579127)
            ·
              refine ⟨170383225628965818489868691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113588817085977212326579127 170383225628965818489868691)
              ·
                refine ⟨255574838443448727734803037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170383225628965818489868691 255574838443448727734803037)
                ·
                  refine ⟨95840564416293272900551139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255574838443448727734803037 95840564416293272900551139)
                  ·
                    refine ⟨143760846624439909350826709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95840564416293272900551139 143760846624439909350826709)
                    ·
                      refine ⟨3369394842760310375410001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143760846624439909350826709 3369394842760310375410001)
                      ·
                        rfl

theorem cell23_6561873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_6561873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561873 prefixEnd_6561873 := by exact prefixLift 6561873
  have htrace : WordTrace (prefixWord ++ tailWord_6561873) baseStart_6561873 baseEnd_6561873 := by
    simpa [prefixWord, tailWord_6561873, baseEnd_6561873] using wordTrace_append hprefix tailTrace_6561873
  have hstable : (prefixWord ++ tailWord_6561873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561873).length < 2 ^ (prefixWord ++ tailWord_6561873).sum := by decide
  have hdescent : baseEnd_6561873 < baseStart_6561873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561880 : List Nat := [2, 1, 2, 2, 1, 4, 1, 3, 2, 5]
def baseStart_6561880 : Nat := 118140960795 + 6561880 * 2 ^ 59
def prefixEnd_6561880 : Nat := 4983230072969 + 3 ^ 40 * 6561880 * 2
def baseEnd_6561880 : Nat := 1123132812374963949340823

theorem tailTrace_6561880 : CollatzResearch.WordTrace tailWord_6561880 prefixEnd_6561880 1123132812374963949340823 := by
  unfold tailWord_6561880
  simp only [CollatzResearch.WordTrace]
  refine ⟨119665712733718457363613547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159554283644957943151484729 119665712733718457363613547)
  ·
    refine ⟨179498569100577686045420321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119665712733718457363613547 179498569100577686045420321)
    ·
      refine ⟨134623926825433264534065241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179498569100577686045420321 134623926825433264534065241)
      ·
        refine ⟨100967945119074948400548931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134623926825433264534065241 100967945119074948400548931)
        ·
          refine ⟨151451917678612422600823397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100967945119074948400548931 151451917678612422600823397)
          ·
            refine ⟨28397234564739829237654387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151451917678612422600823397 28397234564739829237654387)
            ·
              refine ⟨42595851847109743856481581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28397234564739829237654387 42595851847109743856481581)
              ·
                refine ⟨15973444442666153946180593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42595851847109743856481581 15973444442666153946180593)
                ·
                  refine ⟨11980083331999615459635445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15973444442666153946180593 11980083331999615459635445)
                  ·
                    refine ⟨1123132812374963949340823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11980083331999615459635445 1123132812374963949340823)
                    ·
                      rfl

theorem cell23_6561880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_6561880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561880 prefixEnd_6561880 := by exact prefixLift 6561880
  have htrace : WordTrace (prefixWord ++ tailWord_6561880) baseStart_6561880 baseEnd_6561880 := by
    simpa [prefixWord, tailWord_6561880, baseEnd_6561880] using wordTrace_append hprefix tailTrace_6561880
  have hstable : (prefixWord ++ tailWord_6561880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561880).length < 2 ^ (prefixWord ++ tailWord_6561880).sum := by decide
  have hdescent : baseEnd_6561880 < baseStart_6561880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561917 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 1, 6, 2]
def baseStart_6561917 : Nat := 118140960795 + 6561917 * 2 ^ 59
def prefixEnd_6561917 : Nat := 4983230072969 + 3 ^ 40 * 6561917 * 2
def baseEnd_6561917 : Nat := 3369417435909108203259799

theorem tailTrace_6561917 : CollatzResearch.WordTrace tailWord_6561917 prefixEnd_6561917 3369417435909108203259799 := by
  unfold tailWord_6561917
  simp only [CollatzResearch.WordTrace]
  refine ⟨239332774968302870046324005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159555183312201913364216003 239332774968302870046324005)
  ·
    refine ⟨44874895306556788133685751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239332774968302870046324005 44874895306556788133685751)
    ·
      refine ⟨67312342959835182200528627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44874895306556788133685751 67312342959835182200528627)
      ·
        refine ⟨100968514439752773300792941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67312342959835182200528627 100968514439752773300792941)
        ·
          refine ⟨37863192914907289987797353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100968514439752773300792941 37863192914907289987797353)
          ·
            refine ⟨28397394686180467490848015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37863192914907289987797353 28397394686180467490848015)
            ·
              refine ⟨42596092029270701236272023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28397394686180467490848015 42596092029270701236272023)
              ·
                refine ⟨63894138043906051854408035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42596092029270701236272023 63894138043906051854408035)
                ·
                  refine ⟨95841207065859077781612053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63894138043906051854408035 95841207065859077781612053)
                  ·
                    refine ⟨4492556581212144271013065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95841207065859077781612053 4492556581212144271013065)
                    ·
                      refine ⟨3369417435909108203259799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492556581212144271013065 3369417435909108203259799)
                      ·
                        rfl

theorem cell23_6561917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_6561917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561917 prefixEnd_6561917 := by exact prefixLift 6561917
  have htrace : WordTrace (prefixWord ++ tailWord_6561917) baseStart_6561917 baseEnd_6561917 := by
    simpa [prefixWord, tailWord_6561917, baseEnd_6561917] using wordTrace_append hprefix tailTrace_6561917
  have hstable : (prefixWord ++ tailWord_6561917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561917).length < 2 ^ (prefixWord ++ tailWord_6561917).sum := by decide
  have hdescent : baseEnd_6561917 < baseStart_6561917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561920 : List Nat := [2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3]
def baseStart_6561920 : Nat := 118140960795 + 6561920 * 2 ^ 59
def prefixEnd_6561920 : Nat := 4983230072969 + 3 ^ 40 * 6561920 * 2
def baseEnd_6561920 : Nat := 3369418976351071691522285

theorem tailTrace_6561920 : CollatzResearch.WordTrace tailWord_6561920 prefixEnd_6561920 3369418976351071691522285 := by
  unfold tailWord_6561920
  simp only [CollatzResearch.WordTrace]
  refine ⟨119666442193646000779341607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159555256258194667705788809 119666442193646000779341607)
  ·
    refine ⟨179499663290469001169012411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119666442193646000779341607 179499663290469001169012411)
    ·
      refine ⟨269249494935703501753518617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179499663290469001169012411 269249494935703501753518617)
      ·
        refine ⟨201937121201777626315138963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269249494935703501753518617 201937121201777626315138963)
        ·
          refine ⟨302905681802666439472708445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201937121201777626315138963 302905681802666439472708445)
          ·
            refine ⟨113589630675999914802265667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 302905681802666439472708445 113589630675999914802265667)
            ·
              refine ⟨170384446013999872203398501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113589630675999914802265667 170384446013999872203398501)
              ·
                refine ⟨31947083627624976038137219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170384446013999872203398501 31947083627624976038137219)
                ·
                  refine ⟨47920625441437464057205829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31947083627624976038137219 47920625441437464057205829)
                  ·
                    refine ⟨8985117270269524510726093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47920625441437464057205829 8985117270269524510726093)
                    ·
                      refine ⟨3369418976351071691522285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985117270269524510726093 3369418976351071691522285)
                      ·
                        rfl

theorem cell23_6561920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_6561920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561920 prefixEnd_6561920 := by exact prefixLift 6561920
  have htrace : WordTrace (prefixWord ++ tailWord_6561920) baseStart_6561920 baseEnd_6561920 := by
    simpa [prefixWord, tailWord_6561920, baseEnd_6561920] using wordTrace_append hprefix tailTrace_6561920
  have hstable : (prefixWord ++ tailWord_6561920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561920).length < 2 ^ (prefixWord ++ tailWord_6561920).sum := by decide
  have hdescent : baseEnd_6561920 < baseStart_6561920 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561977 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6561977 : Nat := 118140960795 + 6561977 * 2 ^ 59
def prefixEnd_6561977 : Nat := 4983230072969 + 3 ^ 40 * 6561977 * 2
def baseEnd_6561977 : Nat := 3369448244748377968509523

theorem tailTrace_6561977 : CollatzResearch.WordTrace tailWord_6561977 prefixEnd_6561977 3369448244748377968509523 := by
  unfold tailWord_6561977
  simp only [CollatzResearch.WordTrace]
  refine ⟨239334963348085500293508185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159556642232057000195672123 239334963348085500293508185)
  ·
    refine ⟨179501222511064125220131139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239334963348085500293508185 179501222511064125220131139)
    ·
      refine ⟨269251833766596187830196709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179501222511064125220131139 269251833766596187830196709)
      ·
        refine ⟨50484718831236785218161883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269251833766596187830196709 50484718831236785218161883)
        ·
          refine ⟨75727078246855177827242825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50484718831236785218161883 75727078246855177827242825)
          ·
            refine ⟨56795308685141383370432119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75727078246855177827242825 56795308685141383370432119)
            ·
              refine ⟨85192963027712075055648179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56795308685141383370432119 85192963027712075055648179)
              ·
                refine ⟨127789444541568112583472269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85192963027712075055648179 127789444541568112583472269)
                ·
                  refine ⟨47921041703088042218802101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127789444541568112583472269 47921041703088042218802101)
                  ·
                    refine ⟨4492597659664503958012697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47921041703088042218802101 4492597659664503958012697)
                    ·
                      refine ⟨3369448244748377968509523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492597659664503958012697 3369448244748377968509523)
                      ·
                        rfl

theorem cell23_6561977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6561977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561977 prefixEnd_6561977 := by exact prefixLift 6561977
  have htrace : WordTrace (prefixWord ++ tailWord_6561977) baseStart_6561977 baseEnd_6561977 := by
    simpa [prefixWord, tailWord_6561977, baseEnd_6561977] using wordTrace_append hprefix tailTrace_6561977
  have hstable : (prefixWord ++ tailWord_6561977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561977).length < 2 ^ (prefixWord ++ tailWord_6561977).sum := by decide
  have hdescent : baseEnd_6561977 < baseStart_6561977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561984 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 3, 1, 3]
def baseStart_6561984 : Nat := 118140960795 + 6561984 * 2 ^ 59
def prefixEnd_6561984 : Nat := 4983230072969 + 3 ^ 40 * 6561984 * 2
def baseEnd_6561984 : Nat := 3369451839112959441121991

theorem tailTrace_6561984 : CollatzResearch.WordTrace tailWord_6561984 prefixEnd_6561984 3369451839112959441121991 := by
  unfold tailWord_6561984
  simp only [CollatzResearch.WordTrace]
  refine ⟨119667609329530070244506503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159556812439373426992675337 119667609329530070244506503)
  ·
    refine ⟨179501413994295105366759755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119667609329530070244506503 179501413994295105366759755)
    ·
      refine ⟨269252120991442658050139633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179501413994295105366759755 269252120991442658050139633)
      ·
        refine ⟨201939090743581993537604725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269252120991442658050139633 201939090743581993537604725)
        ·
          refine ⟨18931789757210811894150443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201939090743581993537604725 18931789757210811894150443)
          ·
            refine ⟨28397684635816217841225665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18931789757210811894150443 28397684635816217841225665)
            ·
              refine ⟨21298263476862163380919249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28397684635816217841225665 21298263476862163380919249)
              ·
                refine ⟨15973697607646622535689437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21298263476862163380919249 15973697607646622535689437)
                ·
                  refine ⟨5990136602867483450883539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15973697607646622535689437 5990136602867483450883539)
                  ·
                    refine ⟨8985204904301225176325309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5990136602867483450883539 8985204904301225176325309)
                    ·
                      refine ⟨3369451839112959441121991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985204904301225176325309 3369451839112959441121991)
                      ·
                        rfl

theorem cell23_6561984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_6561984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561984 prefixEnd_6561984 := by exact prefixLift 6561984
  have htrace : WordTrace (prefixWord ++ tailWord_6561984) baseStart_6561984 baseEnd_6561984 := by
    simpa [prefixWord, tailWord_6561984, baseEnd_6561984] using wordTrace_append hprefix tailTrace_6561984
  have hstable : (prefixWord ++ tailWord_6561984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561984).length < 2 ^ (prefixWord ++ tailWord_6561984).sum := by decide
  have hdescent : baseEnd_6561984 < baseStart_6561984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6561994 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_6561994 : Nat := 118140960795 + 6561994 * 2 ^ 59
def prefixEnd_6561994 : Nat := 4983230072969 + 3 ^ 40 * 6561994 * 2
def baseEnd_6561994 : Nat := 3369456973919504401996945

theorem tailTrace_6561994 : CollatzResearch.WordTrace tailWord_6561994 prefixEnd_6561994 3369456973919504401996945 := by
  unfold tailWord_6561994
  simp only [CollatzResearch.WordTrace]
  refine ⟨59833895847255978049219259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159557055592682608131251357 59833895847255978049219259)
  ·
    refine ⟨89750843770883967073828889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59833895847255978049219259 89750843770883967073828889)
    ·
      refine ⟨67313132828162975305371667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89750843770883967073828889 67313132828162975305371667)
      ·
        refine ⟨100969699242244462958057501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67313132828162975305371667 100969699242244462958057501)
        ·
          refine ⟨37863637215841673609271563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100969699242244462958057501 37863637215841673609271563)
          ·
            refine ⟨56795455823762510413907345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37863637215841673609271563 56795455823762510413907345)
            ·
              refine ⟨42596591867821882810430509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56795455823762510413907345 42596591867821882810430509)
              ·
                refine ⟨15973721950433206053911441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42596591867821882810430509 15973721950433206053911441)
                ·
                  refine ⟨11980291462824904540433581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15973721950433206053911441 11980291462824904540433581)
                  ·
                    refine ⟨4492609298559339202662593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11980291462824904540433581 4492609298559339202662593)
                    ·
                      refine ⟨3369456973919504401996945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492609298559339202662593 3369456973919504401996945)
                      ·
                        rfl

theorem cell23_6561994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_6561994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6561994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6561994 prefixEnd_6561994 := by exact prefixLift 6561994
  have htrace : WordTrace (prefixWord ++ tailWord_6561994) baseStart_6561994 baseEnd_6561994 := by
    simpa [prefixWord, tailWord_6561994, baseEnd_6561994] using wordTrace_append hprefix tailTrace_6561994
  have hstable : (prefixWord ++ tailWord_6561994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6561994).length < 2 ^ (prefixWord ++ tailWord_6561994).sum := by decide
  have hdescent : baseEnd_6561994 < baseStart_6561994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6561994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562001 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 1, 1, 3]
def baseStart_6562001 : Nat := 118140960795 + 6562001 * 2 ^ 59
def prefixEnd_6562001 : Nat := 4983230072969 + 3 ^ 40 * 6562001 * 2
def baseEnd_6562001 : Nat := 3369460568284085874609413

theorem tailTrace_6562001 : CollatzResearch.WordTrace tailWord_6562001 prefixEnd_6562001 3369460568284085874609413 := by
  unfold tailWord_6562001
  simp only [CollatzResearch.WordTrace]
  refine ⟨239335838699998552392381857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159557225799999034928254571 239335838699998552392381857)
  ·
    refine ⟨179501879024998914294286393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239335838699998552392381857 179501879024998914294286393)
    ·
      refine ⟨134626409268749185720714795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179501879024998914294286393 134626409268749185720714795)
      ·
        refine ⟨201939613903123778581072193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134626409268749185720714795 201939613903123778581072193)
        ·
          refine ⟨151454710427342833935804145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201939613903123778581072193 151454710427342833935804145)
          ·
            refine ⟨113591032820507125451853109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151454710427342833935804145 113591032820507125451853109)
            ·
              refine ⟨10649159326922543011111229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113591032820507125451853109 10649159326922543011111229)
              ·
                refine ⟨3993434747595953629166711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10649159326922543011111229 3993434747595953629166711)
                ·
                  refine ⟨5990152121393930443750067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993434747595953629166711 5990152121393930443750067)
                  ·
                    refine ⟨8985228182090895665625101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5990152121393930443750067 8985228182090895665625101)
                    ·
                      refine ⟨3369460568284085874609413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985228182090895665625101 3369460568284085874609413)
                      ·
                        rfl

theorem cell23_6562001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_6562001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562001 prefixEnd_6562001 := by exact prefixLift 6562001
  have htrace : WordTrace (prefixWord ++ tailWord_6562001) baseStart_6562001 baseEnd_6562001 := by
    simpa [prefixWord, tailWord_6562001, baseEnd_6562001] using wordTrace_append hprefix tailTrace_6562001
  have hstable : (prefixWord ++ tailWord_6562001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562001).length < 2 ^ (prefixWord ++ tailWord_6562001).sum := by decide
  have hdescent : baseEnd_6562001 < baseStart_6562001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562017 : List Nat := [1, 2, 3, 1, 3, 1, 1, 3, 4, 4]
def baseStart_6562017 : Nat := 118140960795 + 6562017 * 2 ^ 59
def prefixEnd_6562017 : Nat := 4983230072969 + 3 ^ 40 * 6562017 * 2
def baseEnd_6562017 : Nat := 1123156261324852604003113

theorem tailTrace_6562017 : CollatzResearch.WordTrace tailWord_6562017 prefixEnd_6562017 1123156261324852604003113 := by
  unfold tailWord_6562017
  simp only [CollatzResearch.WordTrace]
  refine ⟨239336422267940587124964305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159557614845293724749976203 239336422267940587124964305)
  ·
    refine ⟨179502316700955440343723229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239336422267940587124964305 179502316700955440343723229)
    ·
      refine ⟨67313368762858290128896211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179502316700955440343723229 67313368762858290128896211)
      ·
        refine ⟨100970053144287435193344317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67313368762858290128896211 100970053144287435193344317)
        ·
          refine ⟨37863769929107788197504119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100970053144287435193344317 37863769929107788197504119)
          ·
            refine ⟨56795654893661682296256179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37863769929107788197504119 56795654893661682296256179)
            ·
              refine ⟨85193482340492523444384269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56795654893661682296256179 85193482340492523444384269)
              ·
                refine ⟨31947555877684696291644101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85193482340492523444384269 31947555877684696291644101)
                ·
                  refine ⟨5990166727065880554683269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31947555877684696291644101 5990166727065880554683269)
                  ·
                    refine ⟨1123156261324852604003113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5990166727065880554683269 1123156261324852604003113)
                    ·
                      rfl

theorem cell23_6562017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 4].length) (baseStart_6562017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562017 prefixEnd_6562017 := by exact prefixLift 6562017
  have htrace : WordTrace (prefixWord ++ tailWord_6562017) baseStart_6562017 baseEnd_6562017 := by
    simpa [prefixWord, tailWord_6562017, baseEnd_6562017] using wordTrace_append hprefix tailTrace_6562017
  have hstable : (prefixWord ++ tailWord_6562017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562017).length < 2 ^ (prefixWord ++ tailWord_6562017).sum := by decide
  have hdescent : baseEnd_6562017 < baseStart_6562017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562027 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 3]
def baseStart_6562027 : Nat := 118140960795 + 6562027 * 2 ^ 59
def prefixEnd_6562027 : Nat := 4983230072969 + 3 ^ 40 * 6562027 * 2
def baseEnd_6562027 : Nat := 3369473918781102772884293

theorem tailTrace_6562027 : CollatzResearch.WordTrace tailWord_6562027 prefixEnd_6562027 3369473918781102772884293 := by
  unfold tailWord_6562027
  simp only [CollatzResearch.WordTrace]
  refine ⟨239336786997904358832828335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159557857998602905888552223 239336786997904358832828335)
  ·
    refine ⟨359005180496856538249242503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239336786997904358832828335 359005180496856538249242503)
    ·
      refine ⟨538507770745284807373863755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359005180496856538249242503 538507770745284807373863755)
      ·
        refine ⟨807761656117927211060795633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538507770745284807373863755 807761656117927211060795633)
        ·
          refine ⟨605821242088445408295596725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807761656117927211060795633 605821242088445408295596725)
          ·
            refine ⟨56795741445791757027712193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 605821242088445408295596725 56795741445791757027712193)
            ·
              refine ⟨42596806084343817770784145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56795741445791757027712193 42596806084343817770784145)
              ·
                refine ⟨31947604563257863328088109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42596806084343817770784145 31947604563257863328088109)
                ·
                  refine ⟨11980351711221698748033041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31947604563257863328088109 11980351711221698748033041)
                  ·
                    refine ⟨8985263783416274061024781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11980351711221698748033041 8985263783416274061024781)
                    ·
                      refine ⟨3369473918781102772884293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985263783416274061024781 3369473918781102772884293)
                      ·
                        rfl

theorem cell23_6562027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 3, 2, 3].length) (baseStart_6562027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562027 prefixEnd_6562027 := by exact prefixLift 6562027
  have htrace : WordTrace (prefixWord ++ tailWord_6562027) baseStart_6562027 baseEnd_6562027 := by
    simpa [prefixWord, tailWord_6562027, baseEnd_6562027] using wordTrace_append hprefix tailTrace_6562027
  have hstable : (prefixWord ++ tailWord_6562027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562027).length < 2 ^ (prefixWord ++ tailWord_6562027).sum := by decide
  have hdescent : baseEnd_6562027 < baseStart_6562027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562044 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 3, 2, 3]
def baseStart_6562044 : Nat := 118140960795 + 6562044 * 2 ^ 59
def prefixEnd_6562044 : Nat := 4983230072969 + 3 ^ 40 * 6562044 * 2
def baseEnd_6562044 : Nat := 3369482647952229206371715

theorem tailTrace_6562044 : CollatzResearch.WordTrace tailWord_6562044 prefixEnd_6562044 3369482647952229206371715 := by
  unfold tailWord_6562044
  simp only [CollatzResearch.WordTrace]
  refine ⟨119668703519421385368098593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159558271359228513824131457 119668703519421385368098593)
  ·
    refine ⟨89751527639566039026073945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119668703519421385368098593 89751527639566039026073945)
    ·
      refine ⟨67313645729674529269555459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89751527639566039026073945 67313645729674529269555459)
      ·
        refine ⟨100970468594511793904333189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67313645729674529269555459 100970468594511793904333189)
        ·
          refine ⟨18931962861470961357062473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100970468594511793904333189 18931962861470961357062473)
          ·
            refine ⟨14198972146103221017796855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18931962861470961357062473 14198972146103221017796855)
            ·
              refine ⟨21298458219154831526695283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14198972146103221017796855 21298458219154831526695283)
              ·
                refine ⟨31947687328732247290042925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21298458219154831526695283 31947687328732247290042925)
                ·
                  refine ⟨11980382748274592733766097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31947687328732247290042925 11980382748274592733766097)
                  ·
                    refine ⟨8985287061205944550324573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11980382748274592733766097 8985287061205944550324573)
                    ·
                      refine ⟨3369482647952229206371715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985287061205944550324573 3369482647952229206371715)
                      ·
                        rfl

theorem cell23_6562044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_6562044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562044 prefixEnd_6562044 := by exact prefixLift 6562044
  have htrace : WordTrace (prefixWord ++ tailWord_6562044) baseStart_6562044 baseEnd_6562044 := by
    simpa [prefixWord, tailWord_6562044, baseEnd_6562044] using wordTrace_append hprefix tailTrace_6562044
  have hstable : (prefixWord ++ tailWord_6562044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562044).length < 2 ^ (prefixWord ++ tailWord_6562044).sum := by decide
  have hdescent : baseEnd_6562044 < baseStart_6562044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562057 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 3]
def baseStart_6562057 : Nat := 118140960795 + 6562057 * 2 ^ 59
def prefixEnd_6562057 : Nat := 4983230072969 + 3 ^ 40 * 6562057 * 2
def baseEnd_6562057 : Nat := 3369489323200737655509155

theorem tailTrace_6562057 : CollatzResearch.WordTrace tailWord_6562057 prefixEnd_6562057 3369489323200737655509155 := by
  unfold tailWord_6562057
  simp only [CollatzResearch.WordTrace]
  refine ⟨239337881187795673956420425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159558587458530449304280283 239337881187795673956420425)
  ·
    refine ⟨179503410890846755467315319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239337881187795673956420425 179503410890846755467315319)
    ·
      refine ⟨269255116336270133200972979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179503410890846755467315319 269255116336270133200972979)
      ·
        refine ⟨403882674504405199801459469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269255116336270133200972979 403882674504405199801459469)
        ·
          refine ⟨151456002939151949925547301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 403882674504405199801459469 151456002939151949925547301)
          ·
            refine ⟨28398000551090990611040119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151456002939151949925547301 28398000551090990611040119)
            ·
              refine ⟨42597000826636485916560179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28398000551090990611040119 42597000826636485916560179)
              ·
                refine ⟨63895501239954728874840269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42597000826636485916560179 63895501239954728874840269)
                ·
                  refine ⟨23960812964983023328065101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63895501239954728874840269 23960812964983023328065101)
                  ·
                    refine ⟨8985304861868633748024413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23960812964983023328065101 8985304861868633748024413)
                    ·
                      refine ⟨3369489323200737655509155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985304861868633748024413 3369489323200737655509155)
                      ·
                        rfl

theorem cell23_6562057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 3, 3].length) (baseStart_6562057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562057 prefixEnd_6562057 := by exact prefixLift 6562057
  have htrace : WordTrace (prefixWord ++ tailWord_6562057) baseStart_6562057 baseEnd_6562057 := by
    simpa [prefixWord, tailWord_6562057, baseEnd_6562057] using wordTrace_append hprefix tailTrace_6562057
  have hstable : (prefixWord ++ tailWord_6562057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562057).length < 2 ^ (prefixWord ++ tailWord_6562057).sum := by decide
  have hdescent : baseEnd_6562057 < baseStart_6562057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562101 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_6562101 : Nat := 118140960795 + 6562101 * 2 ^ 59
def prefixEnd_6562101 : Nat := 4983230072969 + 3 ^ 40 * 6562101 * 2
def baseEnd_6562101 : Nat := 3369511916349535483358953

theorem tailTrace_6562101 : CollatzResearch.WordTrace tailWord_6562101 prefixEnd_6562101 3369511916349535483358953 := by
  unfold tailWord_6562101
  simp only [CollatzResearch.WordTrace]
  refine ⟨239339485999636269471022157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159559657333090846314014771 239339485999636269471022157)
  ·
    refine ⟨89752307249863601051633309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239339485999636269471022157 89752307249863601051633309)
    ·
      refine ⟨33657115218698850394362491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89752307249863601051633309 33657115218698850394362491)
      ·
        refine ⟨50485672828048275591543737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33657115218698850394362491 50485672828048275591543737)
        ·
          refine ⟨37864254621036206693657803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50485672828048275591543737 37864254621036206693657803)
          ·
            refine ⟨56796381931554310040486705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37864254621036206693657803 56796381931554310040486705)
            ·
              refine ⟨42597286448665732530365029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56796381931554310040486705 42597286448665732530365029)
              ·
                refine ⟨7986991209124824849443443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42597286448665732530365029 7986991209124824849443443)
                ·
                  refine ⟨11980486813687237274165165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7986991209124824849443443 11980486813687237274165165)
                  ·
                    refine ⟨4492682555132713977811937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11980486813687237274165165 4492682555132713977811937)
                    ·
                      refine ⟨3369511916349535483358953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492682555132713977811937 3369511916349535483358953)
                      ·
                        rfl

theorem cell23_6562101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_6562101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562101 prefixEnd_6562101 := by exact prefixLift 6562101
  have htrace : WordTrace (prefixWord ++ tailWord_6562101) baseStart_6562101 baseEnd_6562101 := by
    simpa [prefixWord, tailWord_6562101, baseEnd_6562101] using wordTrace_append hprefix tailTrace_6562101
  have hstable : (prefixWord ++ tailWord_6562101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562101).length < 2 ^ (prefixWord ++ tailWord_6562101).sum := by decide
  have hdescent : baseEnd_6562101 < baseStart_6562101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562131 : List Nat := [1, 1, 1, 2, 1, 1, 4, 6, 2, 2, 2]
def baseStart_6562131 : Nat := 118140960795 + 6562131 * 2 ^ 59
def prefixEnd_6562131 : Nat := 4983230072969 + 3 ^ 40 * 6562131 * 2
def baseEnd_6562131 : Nat := 3369527320769170365983815

theorem tailTrace_6562131 : CollatzResearch.WordTrace tailWord_6562131 prefixEnd_6562131 3369527320769170365983815 := by
  unfold tailWord_6562131
  simp only [CollatzResearch.WordTrace]
  refine ⟨239340580189527584594614247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159560386793018389729742831 239340580189527584594614247)
  ·
    refine ⟨359010870284291376891921371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239340580189527584594614247 359010870284291376891921371)
    ·
      refine ⟨538516305426437065337882057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359010870284291376891921371 538516305426437065337882057)
      ·
        refine ⟨403887229069827799003411543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538516305426437065337882057 403887229069827799003411543)
        ·
          refine ⟨605830843604741698505117315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403887229069827799003411543 605830843604741698505117315)
          ·
            refine ⟨908746265407112547757675973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605830843604741698505117315 908746265407112547757675973)
            ·
              refine ⟨170389924763833602704564245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 908746265407112547757675973 170389924763833602704564245)
              ·
                refine ⟨7987027723304700126776449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 170389924763833602704564245 7987027723304700126776449)
                ·
                  refine ⟨5990270792478525095082337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7987027723304700126776449 5990270792478525095082337)
                  ·
                    refine ⟨4492703094358893821311753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5990270792478525095082337 4492703094358893821311753)
                    ·
                      refine ⟨3369527320769170365983815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492703094358893821311753 3369527320769170365983815)
                      ·
                        rfl

theorem cell23_6562131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 6, 2, 2, 2].length) (baseStart_6562131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562131 prefixEnd_6562131 := by exact prefixLift 6562131
  have htrace : WordTrace (prefixWord ++ tailWord_6562131) baseStart_6562131 baseEnd_6562131 := by
    simpa [prefixWord, tailWord_6562131, baseEnd_6562131] using wordTrace_append hprefix tailTrace_6562131
  have hstable : (prefixWord ++ tailWord_6562131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562131).length < 2 ^ (prefixWord ++ tailWord_6562131).sum := by decide
  have hdescent : baseEnd_6562131 < baseStart_6562131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562154 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 7]
def baseStart_6562154 : Nat := 118140960795 + 6562154 * 2 ^ 59
def prefixEnd_6562154 : Nat := 4983230072969 + 3 ^ 40 * 6562154 * 2
def baseEnd_6562154 : Nat := 374393236758247086221801

theorem tailTrace_6562154 : CollatzResearch.WordTrace tailWord_6562154 prefixEnd_6562154 374393236758247086221801 := by
  unfold tailWord_6562154
  simp only [CollatzResearch.WordTrace]
  refine ⟨59835354767111064880675379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159560946045629506348467677 59835354767111064880675379)
  ·
    refine ⟨89753032150666597321013069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59835354767111064880675379 89753032150666597321013069)
    ·
      refine ⟨33657387056499973995379901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89753032150666597321013069 33657387056499973995379901)
      ·
        refine ⟨12621520146187490248267463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33657387056499973995379901 12621520146187490248267463)
        ·
          refine ⟨18932280219281235372401195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12621520146187490248267463 18932280219281235372401195)
          ·
            refine ⟨28398420328921853058601793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18932280219281235372401195 28398420328921853058601793)
            ·
              refine ⟨21298815246691389793951345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28398420328921853058601793 21298815246691389793951345)
              ·
                refine ⟨15974111435018542345463509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21298815246691389793951345 15974111435018542345463509)
                ·
                  refine ⟨374393236758247086221801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15974111435018542345463509 374393236758247086221801)
                  ·
                    rfl

theorem cell23_6562154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_6562154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562154 prefixEnd_6562154 := by exact prefixLift 6562154
  have htrace : WordTrace (prefixWord ++ tailWord_6562154) baseStart_6562154 baseEnd_6562154 := by
    simpa [prefixWord, tailWord_6562154, baseEnd_6562154] using wordTrace_append hprefix tailTrace_6562154
  have hstable : (prefixWord ++ tailWord_6562154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562154).length < 2 ^ (prefixWord ++ tailWord_6562154).sum := by decide
  have hdescent : baseEnd_6562154 < baseStart_6562154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562171 : List Nat := [1, 1, 1, 1, 1, 9, 1, 3, 5]
def baseStart_6562171 : Nat := 118140960795 + 6562171 * 2 ^ 59
def prefixEnd_6562171 : Nat := 4983230072969 + 3 ^ 40 * 6562171 * 2
def baseEnd_6562171 : Nat := 374394206666150023275959

theorem tailTrace_6562171 : CollatzResearch.WordTrace tailWord_6562171 prefixEnd_6562171 374394206666150023275959 := by
  unfold tailWord_6562171
  simp only [CollatzResearch.WordTrace]
  refine ⟨239342039109382671426070367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159561359406255114284046911 239342039109382671426070367)
  ·
    refine ⟨359013058664074007139105551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239342039109382671426070367 359013058664074007139105551)
    ·
      refine ⟨538519587996111010708658327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359013058664074007139105551 538519587996111010708658327)
      ·
        refine ⟨807779381994166516062987491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538519587996111010708658327 807779381994166516062987491)
        ·
          refine ⟨1211669072991249774094481237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807779381994166516062987491 1211669072991249774094481237)
          ·
            refine ⟨7099623474558104145084851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1211669072991249774094481237 7099623474558104145084851)
            ·
              refine ⟨10649435211837156217627277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099623474558104145084851 10649435211837156217627277)
              ·
                refine ⟨3993538204438933581610229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10649435211837156217627277 3993538204438933581610229)
                ·
                  refine ⟨374394206666150023275959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3993538204438933581610229 374394206666150023275959)
                  ·
                    rfl

theorem cell23_6562171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 3, 5].length) (baseStart_6562171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562171 prefixEnd_6562171 := by exact prefixLift 6562171
  have htrace : WordTrace (prefixWord ++ tailWord_6562171) baseStart_6562171 baseEnd_6562171 := by
    simpa [prefixWord, tailWord_6562171, baseEnd_6562171] using wordTrace_append hprefix tailTrace_6562171
  have hstable : (prefixWord ++ tailWord_6562171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562171).length < 2 ^ (prefixWord ++ tailWord_6562171).sum := by decide
  have hdescent : baseEnd_6562171 < baseStart_6562171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562184 : List Nat := [2, 1, 3, 3, 1, 1, 3, 2, 2, 5]
def baseStart_6562184 : Nat := 118140960795 + 6562184 * 2 ^ 59
def prefixEnd_6562184 : Nat := 4983230072969 + 3 ^ 40 * 6562184 * 2
def baseEnd_6562184 : Nat := 1123184845081286219540357

theorem tailTrace_6562184 : CollatzResearch.WordTrace tailWord_6562184 prefixEnd_6562184 1123184845081286219540357 := by
  unfold tailWord_6562184
  simp only [CollatzResearch.WordTrace]
  refine ⟨119671256629167787323146803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159561675505557049764195737 119671256629167787323146803)
  ·
    refine ⟨179506884943751680984720205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119671256629167787323146803 179506884943751680984720205)
    ·
      refine ⟨67315081853906880369270077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179506884943751680984720205 67315081853906880369270077)
      ·
        refine ⟨25243155695215080138476279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67315081853906880369270077 25243155695215080138476279)
        ·
          refine ⟨37864733542822620207714419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25243155695215080138476279 37864733542822620207714419)
          ·
            refine ⟨56797100314233930311571629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37864733542822620207714419 56797100314233930311571629)
            ·
              refine ⟨21298912617837723866839361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56797100314233930311571629 21298912617837723866839361)
              ·
                refine ⟨15974184463378292900129521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21298912617837723866839361 15974184463378292900129521)
                ·
                  refine ⟨11980638347533719675097141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15974184463378292900129521 11980638347533719675097141)
                  ·
                    refine ⟨1123184845081286219540357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11980638347533719675097141 1123184845081286219540357)
                    ·
                      rfl

theorem cell23_6562184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_6562184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562184 prefixEnd_6562184 := by exact prefixLift 6562184
  have htrace : WordTrace (prefixWord ++ tailWord_6562184) baseStart_6562184 baseEnd_6562184 := by
    simpa [prefixWord, tailWord_6562184, baseEnd_6562184] using wordTrace_append hprefix tailTrace_6562184
  have hstable : (prefixWord ++ tailWord_6562184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562184).length < 2 ^ (prefixWord ++ tailWord_6562184).sum := by decide
  have hdescent : baseEnd_6562184 < baseStart_6562184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562217 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 4]
def baseStart_6562217 : Nat := 118140960795 + 6562217 * 2 ^ 59
def prefixEnd_6562217 : Nat := 4983230072969 + 3 ^ 40 * 6562217 * 2
def baseEnd_6562217 : Nat := 3369571480105457029508419

theorem tailTrace_6562217 : CollatzResearch.WordTrace tailWord_6562217 prefixEnd_6562217 3369571480105457029508419 := by
  unfold tailWord_6562217
  simp only [CollatzResearch.WordTrace]
  refine ⟨239343716867216021282244905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159562477911477347521496603 239343716867216021282244905)
  ·
    refine ⟨179507787650412015961683679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239343716867216021282244905 179507787650412015961683679)
    ·
      refine ⟨269261681475618023942525519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179507787650412015961683679 269261681475618023942525519)
      ·
        refine ⟨403892522213427035913788279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269261681475618023942525519 403892522213427035913788279)
        ·
          refine ⟨605838783320140553870682419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403892522213427035913788279 605838783320140553870682419)
          ·
            refine ⟨908758174980210830806023629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605838783320140553870682419 908758174980210830806023629)
            ·
              refine ⟨340784315617579061552258861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908758174980210830806023629 340784315617579061552258861)
              ·
                refine ⟨127794118356592148082097073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340784315617579061552258861 127794118356592148082097073)
                ·
                  refine ⟨95845588767444111061572805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127794118356592148082097073 95845588767444111061572805)
                  ·
                    refine ⟨17971047893895770824044901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95845588767444111061572805 17971047893895770824044901)
                    ·
                      refine ⟨3369571480105457029508419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17971047893895770824044901 3369571480105457029508419)
                      ·
                        rfl

theorem cell23_6562217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4, 4].length) (baseStart_6562217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562217 prefixEnd_6562217 := by exact prefixLift 6562217
  have htrace : WordTrace (prefixWord ++ tailWord_6562217) baseStart_6562217 baseEnd_6562217 := by
    simpa [prefixWord, tailWord_6562217, baseEnd_6562217] using wordTrace_append hprefix tailTrace_6562217
  have hstable : (prefixWord ++ tailWord_6562217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562217).length < 2 ^ (prefixWord ++ tailWord_6562217).sum := by decide
  have hdescent : baseEnd_6562217 < baseStart_6562217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562248 : List Nat := [2, 1, 3, 1, 3, 3, 1, 4, 1, 4]
def baseStart_6562248 : Nat := 118140960795 + 6562248 * 2 ^ 59
def prefixEnd_6562248 : Nat := 4983230072969 + 3 ^ 40 * 6562248 * 2
def baseEnd_6562248 : Nat := 1123195799335248802740259

theorem tailTrace_6562248 : CollatzResearch.WordTrace tailWord_6562248 prefixEnd_6562248 1123195799335248802740259 := by
  unfold tailWord_6562248
  simp only [CollatzResearch.WordTrace]
  refine ⟨119672423765051856788311699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159563231686735809051082265 119672423765051856788311699)
  ·
    refine ⟨179508635647577785182467549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119672423765051856788311699 179508635647577785182467549)
    ·
      refine ⟨67315738367841669443425331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179508635647577785182467549 67315738367841669443425331)
      ·
        refine ⟨100973607551762504165137997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67315738367841669443425331 100973607551762504165137997)
        ·
          refine ⟨37865102831910939061926749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100973607551762504165137997 37865102831910939061926749)
          ·
            refine ⟨14199413561966602148222531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37865102831910939061926749 14199413561966602148222531)
            ·
              refine ⟨21299120342949903222333797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14199413561966602148222531 21299120342949903222333797)
              ·
                refine ⟨3993585064303106854187587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21299120342949903222333797 3993585064303106854187587)
                ·
                  refine ⟨5990377596454660281281381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993585064303106854187587 5990377596454660281281381)
                  ·
                    refine ⟨1123195799335248802740259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5990377596454660281281381 1123195799335248802740259)
                    ·
                      rfl

theorem cell23_6562248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_6562248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562248 prefixEnd_6562248 := by exact prefixLift 6562248
  have htrace : WordTrace (prefixWord ++ tailWord_6562248) baseStart_6562248 baseEnd_6562248 := by
    simpa [prefixWord, tailWord_6562248, baseEnd_6562248] using wordTrace_append hprefix tailTrace_6562248
  have hstable : (prefixWord ++ tailWord_6562248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562248).length < 2 ^ (prefixWord ++ tailWord_6562248).sum := by decide
  have hdescent : baseEnd_6562248 < baseStart_6562248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562254 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_6562254 : Nat := 118140960795 + 6562254 * 2 ^ 59
def prefixEnd_6562254 : Nat := 4983230072969 + 3 ^ 40 * 6562254 * 2
def baseEnd_6562254 : Nat := 3369590478889673384745749

theorem tailTrace_6562254 : CollatzResearch.WordTrace tailWord_6562254 prefixEnd_6562254 3369590478889673384745749 := by
  unfold tailWord_6562254
  simp only [CollatzResearch.WordTrace]
  refine ⟨29918133296010247075167727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159563377578721317734227877 29918133296010247075167727)
  ·
    refine ⟨44877199944015370612751591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29918133296010247075167727 44877199944015370612751591)
    ·
      refine ⟨67315799916023055919127387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44877199944015370612751591 67315799916023055919127387)
      ·
        refine ⟨100973699874034583878691081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67315799916023055919127387 100973699874034583878691081)
        ·
          refine ⟨75730274905525937909018311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100973699874034583878691081 75730274905525937909018311)
          ·
            refine ⟨113595412358288906863527467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75730274905525937909018311 113595412358288906863527467)
            ·
              refine ⟨170393118537433360295291201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113595412358288906863527467 170393118537433360295291201)
              ·
                refine ⟨127794838903075020221468401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170393118537433360295291201 127794838903075020221468401)
                ·
                  refine ⟨95846129177306265166101301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127794838903075020221468401 95846129177306265166101301)
                  ·
                    refine ⟨8985574610372462359321997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95846129177306265166101301 8985574610372462359321997)
                    ·
                      refine ⟨3369590478889673384745749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985574610372462359321997 3369590478889673384745749)
                      ·
                        rfl

theorem cell23_6562254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_6562254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562254 prefixEnd_6562254 := by exact prefixLift 6562254
  have htrace : WordTrace (prefixWord ++ tailWord_6562254) baseStart_6562254 baseEnd_6562254 := by
    simpa [prefixWord, tailWord_6562254, baseEnd_6562254] using wordTrace_append hprefix tailTrace_6562254
  have hstable : (prefixWord ++ tailWord_6562254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562254).length < 2 ^ (prefixWord ++ tailWord_6562254).sum := by decide
  have hdescent : baseEnd_6562254 < baseStart_6562254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562271 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 3]
def baseStart_6562271 : Nat := 118140960795 + 6562271 * 2 ^ 59
def prefixEnd_6562271 : Nat := 4983230072969 + 3 ^ 40 * 6562271 * 2
def baseEnd_6562271 : Nat := 3369599208060799818233171

theorem tailTrace_6562271 : CollatzResearch.WordTrace tailWord_6562271 prefixEnd_6562271 3369599208060799818233171 := by
  unfold tailWord_6562271
  simp only [CollatzResearch.WordTrace]
  refine ⟨239345686409020388504710667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159563790939346925669807111 239345686409020388504710667)
  ·
    refine ⟨359018529613530582757066001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239345686409020388504710667 359018529613530582757066001)
    ·
      refine ⟨269263897210147937067799501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359018529613530582757066001 269263897210147937067799501)
      ·
        refine ⟨100973961453805476400424813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269263897210147937067799501 100973961453805476400424813)
        ·
          refine ⟨37865235545177053650159305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100973961453805476400424813 37865235545177053650159305)
          ·
            refine ⟨28398926658882790237619479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37865235545177053650159305 28398926658882790237619479)
            ·
              refine ⟨42598389988324185356429219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28398926658882790237619479 42598389988324185356429219)
              ·
                refine ⟨63897584982486278034643829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42598389988324185356429219 63897584982486278034643829)
                ·
                  refine ⟨5990398592108088565747859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63897584982486278034643829 5990398592108088565747859)
                  ·
                    refine ⟨8985597888162132848621789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5990398592108088565747859 8985597888162132848621789)
                    ·
                      refine ⟨3369599208060799818233171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985597888162132848621789 3369599208060799818233171)
                      ·
                        rfl

theorem cell23_6562271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_6562271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562271 prefixEnd_6562271 := by exact prefixLift 6562271
  have htrace : WordTrace (prefixWord ++ tailWord_6562271) baseStart_6562271 baseEnd_6562271 := by
    simpa [prefixWord, tailWord_6562271, baseEnd_6562271] using wordTrace_append hprefix tailTrace_6562271
  have hstable : (prefixWord ++ tailWord_6562271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562271).length < 2 ^ (prefixWord ++ tailWord_6562271).sum := by decide
  have hdescent : baseEnd_6562271 < baseStart_6562271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562275 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 2, 2, 3]
def baseStart_6562275 : Nat := 118140960795 + 6562275 * 2 ^ 59
def prefixEnd_6562275 : Nat := 4983230072969 + 3 ^ 40 * 6562275 * 2
def baseEnd_6562275 : Nat := 3369601261983417802583153

theorem tailTrace_6562275 : CollatzResearch.WordTrace tailWord_6562275 prefixEnd_6562275 3369601261983417802583153 := by
  unfold tailWord_6562275
  simp only [CollatzResearch.WordTrace]
  refine ⟨239345832301005897187856279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159563888200670598125237519 239345832301005897187856279)
  ·
    refine ⟨359018748451508845781784419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239345832301005897187856279 359018748451508845781784419)
    ·
      refine ⟨538528122677263268672676629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359018748451508845781784419 538528122677263268672676629)
      ·
        refine ⟨25243505750496715719031717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 538528122677263268672676629 25243505750496715719031717)
        ·
          refine ⟨4733157328218134197318447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25243505750496715719031717 4733157328218134197318447)
          ·
            refine ⟨7099735992327201295977671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733157328218134197318447 7099735992327201295977671)
            ·
              refine ⟨10649603988490801943966507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099735992327201295977671 10649603988490801943966507)
              ·
                refine ⟨15974405982736202915949761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10649603988490801943966507 15974405982736202915949761)
                ·
                  refine ⟨11980804487052152186962321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15974405982736202915949761 11980804487052152186962321)
                  ·
                    refine ⟨8985603365289114140221741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11980804487052152186962321 8985603365289114140221741)
                    ·
                      refine ⟨3369601261983417802583153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985603365289114140221741 3369601261983417802583153)
                      ·
                        rfl

theorem cell23_6562275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_6562275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562275 prefixEnd_6562275 := by exact prefixLift 6562275
  have htrace : WordTrace (prefixWord ++ tailWord_6562275) baseStart_6562275 baseEnd_6562275 := by
    simpa [prefixWord, tailWord_6562275, baseEnd_6562275] using wordTrace_append hprefix tailTrace_6562275
  have hstable : (prefixWord ++ tailWord_6562275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562275).length < 2 ^ (prefixWord ++ tailWord_6562275).sum := by decide
  have hdescent : baseEnd_6562275 < baseStart_6562275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562281 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 2, 3, 2]
def baseStart_6562281 : Nat := 118140960795 + 6562281 * 2 ^ 59
def prefixEnd_6562281 : Nat := 4983230072969 + 3 ^ 40 * 6562281 * 2
def baseEnd_6562281 : Nat := 3369604342867344779108125

theorem tailTrace_6562281 : CollatzResearch.WordTrace tailWord_6562281 prefixEnd_6562281 3369604342867344779108125 := by
  unfold tailWord_6562281
  simp only [CollatzResearch.WordTrace]
  refine ⟨239346051138984160212574697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159564034092656106808383131 239346051138984160212574697)
  ·
    refine ⟨179509538354238120159431023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239346051138984160212574697 179509538354238120159431023)
    ·
      refine ⟨269264307531357180239146535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179509538354238120159431023 269264307531357180239146535)
      ·
        refine ⟨403896461297035770358719803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269264307531357180239146535 403896461297035770358719803)
        ·
          refine ⟨605844691945553655538079705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403896461297035770358719803 605844691945553655538079705)
          ·
            refine ⟨454383518959165241653559779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605844691945553655538079705 454383518959165241653559779)
            ·
              refine ⟨681575278438747862480339669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454383518959165241653559779 681575278438747862480339669)
              ·
                refine ⟨15974420588408153026882961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 681575278438747862480339669 15974420588408153026882961)
                ·
                  refine ⟨11980815441306114770162221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15974420588408153026882961 11980815441306114770162221)
                  ·
                    refine ⟨4492805790489793038810833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11980815441306114770162221 4492805790489793038810833)
                    ·
                      refine ⟨3369604342867344779108125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492805790489793038810833 3369604342867344779108125)
                      ·
                        rfl

theorem cell23_6562281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 2, 3, 2].length) (baseStart_6562281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562281 prefixEnd_6562281 := by exact prefixLift 6562281
  have htrace : WordTrace (prefixWord ++ tailWord_6562281) baseStart_6562281 baseEnd_6562281 := by
    simpa [prefixWord, tailWord_6562281, baseEnd_6562281] using wordTrace_append hprefix tailTrace_6562281
  have hstable : (prefixWord ++ tailWord_6562281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562281).length < 2 ^ (prefixWord ++ tailWord_6562281).sum := by decide
  have hdescent : baseEnd_6562281 < baseStart_6562281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562305 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 1, 1, 3]
def baseStart_6562305 : Nat := 118140960795 + 6562305 * 2 ^ 59
def prefixEnd_6562305 : Nat := 4983230072969 + 3 ^ 40 * 6562305 * 2
def baseEnd_6562305 : Nat := 3369616666403052685208015

theorem tailTrace_6562305 : CollatzResearch.WordTrace tailWord_6562305 prefixEnd_6562305 3369616666403052685208015 := by
  unfold tailWord_6562305
  simp only [CollatzResearch.WordTrace]
  refine ⟨239346926490897212311448369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159564617660598141540965579 239346926490897212311448369)
  ·
    refine ⟨179510194868172909233586277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239346926490897212311448369 179510194868172909233586277)
    ·
      refine ⟨33658161537782420481297427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179510194868172909233586277 33658161537782420481297427)
      ·
        refine ⟨50487242306673630721946141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33658161537782420481297427 50487242306673630721946141)
        ·
          refine ⟨18932715865002611520729803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50487242306673630721946141 18932715865002611520729803)
          ·
            refine ⟨28399073797503917281094705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18932715865002611520729803 28399073797503917281094705)
            ·
              refine ⟨21299305348127937960821029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28399073797503917281094705 21299305348127937960821029)
              ·
                refine ⟨3993619752773988367653943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21299305348127937960821029 3993619752773988367653943)
                ·
                  refine ⟨5990429629160982551480915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993619752773988367653943 5990429629160982551480915)
                  ·
                    refine ⟨8985644443741473827221373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5990429629160982551480915 8985644443741473827221373)
                    ·
                      refine ⟨3369616666403052685208015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985644443741473827221373 3369616666403052685208015)
                      ·
                        rfl

theorem cell23_6562305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 1, 1, 3].length) (baseStart_6562305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562305 prefixEnd_6562305 := by exact prefixLift 6562305
  have htrace : WordTrace (prefixWord ++ tailWord_6562305) baseStart_6562305 baseEnd_6562305 := by
    simpa [prefixWord, tailWord_6562305, baseEnd_6562305] using wordTrace_append hprefix tailTrace_6562305
  have hstable : (prefixWord ++ tailWord_6562305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562305).length < 2 ^ (prefixWord ++ tailWord_6562305).sum := by decide
  have hdescent : baseEnd_6562305 < baseStart_6562305 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562328 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 1, 1, 4]
def baseStart_6562328 : Nat := 118140960795 + 6562328 * 2 ^ 59
def prefixEnd_6562328 : Nat := 4983230072969 + 3 ^ 40 * 6562328 * 2
def baseEnd_6562328 : Nat := 3369628476458106095220409

theorem tailTrace_6562328 : CollatzResearch.WordTrace tailWord_6562328 prefixEnd_6562328 3369628476458106095220409 := by
  unfold tailWord_6562328
  simp only [CollatzResearch.WordTrace]
  refine ⟨119673882684906943619767819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159565176913209258159690425 119673882684906943619767819)
  ·
    refine ⟨179510824027360415429651729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119673882684906943619767819 179510824027360415429651729)
    ·
      refine ⟨134633118020520311572238797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179510824027360415429651729 134633118020520311572238797)
      ·
        refine ⟨50487419257695116839589549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134633118020520311572238797 50487419257695116839589549)
        ·
          refine ⟨18932782221635668814846081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50487419257695116839589549 18932782221635668814846081)
          ·
            refine ⟨14199586666226751611134561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18932782221635668814846081 14199586666226751611134561)
            ·
              refine ⟨10649689999670063708350921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14199586666226751611134561 10649689999670063708350921)
              ·
                refine ⟨7987267499752547781263191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10649689999670063708350921 7987267499752547781263191)
                ·
                  refine ⟨11980901249628821671894787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7987267499752547781263191 11980901249628821671894787)
                  ·
                    refine ⟨17971351874443232507842181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11980901249628821671894787 17971351874443232507842181)
                    ·
                      refine ⟨3369628476458106095220409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17971351874443232507842181 3369628476458106095220409)
                      ·
                        rfl

theorem cell23_6562328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_6562328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562328 prefixEnd_6562328 := by exact prefixLift 6562328
  have htrace : WordTrace (prefixWord ++ tailWord_6562328) baseStart_6562328 baseEnd_6562328 := by
    simpa [prefixWord, tailWord_6562328, baseEnd_6562328] using wordTrace_append hprefix tailTrace_6562328
  have hstable : (prefixWord ++ tailWord_6562328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562328).length < 2 ^ (prefixWord ++ tailWord_6562328).sum := by decide
  have hdescent : baseEnd_6562328 < baseStart_6562328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562349 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6562349 : Nat := 118140960795 + 6562349 * 2 ^ 59
def prefixEnd_6562349 : Nat := 4983230072969 + 3 ^ 40 * 6562349 * 2
def baseEnd_6562349 : Nat := 3369639259551850513057813

theorem tailTrace_6562349 : CollatzResearch.WordTrace tailWord_6562349 prefixEnd_6562349 3369639259551850513057813 := by
  unfold tailWord_6562349
  simp only [CollatzResearch.WordTrace]
  refine ⟨239348531302737807826050101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159565687535158538550700067 239348531302737807826050101)
  ·
    refine ⟨22438924809631669483692197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239348531302737807826050101 22438924809631669483692197)
    ·
      refine ⟨4207298401805938028192287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22438924809631669483692197 4207298401805938028192287)
      ·
        refine ⟨6310947602708907042288431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207298401805938028192287 6310947602708907042288431)
        ·
          refine ⟨9466421404063360563432647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310947602708907042288431 9466421404063360563432647)
          ·
            refine ⟨14199632106095040845148971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9466421404063360563432647 14199632106095040845148971)
            ·
              refine ⟨21299448159142561267723457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14199632106095040845148971 21299448159142561267723457)
              ·
                refine ⟨15974586119356920950792593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21299448159142561267723457 15974586119356920950792593)
                ·
                  refine ⟨11980939589517690713094445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15974586119356920950792593 11980939589517690713094445)
                  ·
                    refine ⟨4492852346069134017410417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11980939589517690713094445 4492852346069134017410417)
                    ·
                      refine ⟨3369639259551850513057813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492852346069134017410417 3369639259551850513057813)
                      ·
                        rfl

theorem cell23_6562349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6562349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562349 prefixEnd_6562349 := by exact prefixLift 6562349
  have htrace : WordTrace (prefixWord ++ tailWord_6562349) baseStart_6562349 baseEnd_6562349 := by
    simpa [prefixWord, tailWord_6562349, baseEnd_6562349] using wordTrace_append hprefix tailTrace_6562349
  have hstable : (prefixWord ++ tailWord_6562349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562349).length < 2 ^ (prefixWord ++ tailWord_6562349).sum := by decide
  have hdescent : baseEnd_6562349 < baseStart_6562349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562356 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6562356 : Nat := 118140960795 + 6562356 * 2 ^ 59
def prefixEnd_6562356 : Nat := 4983230072969 + 3 ^ 40 * 6562356 * 2
def baseEnd_6562356 : Nat := 3369642853916431985670281

theorem tailTrace_6562356 : CollatzResearch.WordTrace tailWord_6562356 prefixEnd_6562356 3369642853916431985670281 := by
  unfold tailWord_6562356
  simp only [CollatzResearch.WordTrace]
  refine ⟨119674393306856224010777461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159565857742474965347703281 119674393306856224010777461)
  ·
    refine ⟨11219474372517771001010387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119674393306856224010777461 11219474372517771001010387)
    ·
      refine ⟨16829211558776656501515581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11219474372517771001010387 16829211558776656501515581)
      ·
        refine ⟨6310954334541246188068343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16829211558776656501515581 6310954334541246188068343)
        ·
          refine ⟨9466431501811869282102515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6310954334541246188068343 9466431501811869282102515)
          ·
            refine ⟨14199647252717803923153773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9466431501811869282102515 14199647252717803923153773)
            ·
              refine ⟨5324867719769176471182665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14199647252717803923153773 5324867719769176471182665)
              ·
                refine ⟨3993650789826882353386999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5324867719769176471182665 3993650789826882353386999)
                ·
                  refine ⟨5990476184740323530080499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993650789826882353386999 5990476184740323530080499)
                  ·
                    refine ⟨8985714277110485295120749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5990476184740323530080499 8985714277110485295120749)
                    ·
                      refine ⟨3369642853916431985670281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985714277110485295120749 3369642853916431985670281)
                      ·
                        rfl

theorem cell23_6562356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6562356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562356 prefixEnd_6562356 := by exact prefixLift 6562356
  have htrace : WordTrace (prefixWord ++ tailWord_6562356) baseStart_6562356 baseEnd_6562356 := by
    simpa [prefixWord, tailWord_6562356, baseEnd_6562356] using wordTrace_append hprefix tailTrace_6562356
  have hstable : (prefixWord ++ tailWord_6562356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562356).length < 2 ^ (prefixWord ++ tailWord_6562356).sum := by decide
  have hdescent : baseEnd_6562356 < baseStart_6562356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562384 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4]
def baseStart_6562384 : Nat := 118140960795 + 6562384 * 2 ^ 59
def prefixEnd_6562384 : Nat := 4983230072969 + 3 ^ 40 * 6562384 * 2
def baseEnd_6562384 : Nat := 3369657231374757876120151

theorem tailTrace_6562384 : CollatzResearch.WordTrace tailWord_6562384 prefixEnd_6562384 3369657231374757876120151 := by
  unfold tailWord_6562384
  simp only [CollatzResearch.WordTrace]
  refine ⟨119674903928805504401787103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159566538571740672535716137 119674903928805504401787103)
  ·
    refine ⟨179512355893208256602680655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119674903928805504401787103 179512355893208256602680655)
    ·
      refine ⟨269268533839812384904020983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179512355893208256602680655 269268533839812384904020983)
      ·
        refine ⟨403902800759718577356031475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269268533839812384904020983 403902800759718577356031475)
        ·
          refine ⟨605854201139577866034047213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403902800759718577356031475 605854201139577866034047213)
          ·
            refine ⟨227195325427341699762767705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 605854201139577866034047213 227195325427341699762767705)
            ·
              refine ⟨170396494070506274822075779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227195325427341699762767705 170396494070506274822075779)
              ·
                refine ⟨255594741105759412233113669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170396494070506274822075779 255594741105759412233113669)
                ·
                  refine ⟨47924013957329889793708813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255594741105759412233113669 47924013957329889793708813)
                  ·
                    refine ⟨17971505233998708672640805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47924013957329889793708813 17971505233998708672640805)
                    ·
                      refine ⟨3369657231374757876120151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17971505233998708672640805 3369657231374757876120151)
                      ·
                        rfl

theorem cell23_6562384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 4].length) (baseStart_6562384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562384 prefixEnd_6562384 := by exact prefixLift 6562384
  have htrace : WordTrace (prefixWord ++ tailWord_6562384) baseStart_6562384 baseEnd_6562384 := by
    simpa [prefixWord, tailWord_6562384, baseEnd_6562384] using wordTrace_append hprefix tailTrace_6562384
  have hstable : (prefixWord ++ tailWord_6562384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562384).length < 2 ^ (prefixWord ++ tailWord_6562384).sum := by decide
  have hdescent : baseEnd_6562384 < baseStart_6562384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562394 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_6562394 : Nat := 118140960795 + 6562394 * 2 ^ 59
def prefixEnd_6562394 : Nat := 4983230072969 + 3 ^ 40 * 6562394 * 2
def baseEnd_6562394 : Nat := 1123220788727100945665035

theorem tailTrace_6562394 : CollatzResearch.WordTrace tailWord_6562394 prefixEnd_6562394 1123220788727100945665035 := by
  unfold tailWord_6562394
  simp only [CollatzResearch.WordTrace]
  refine ⟨59837543146893695127859559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159566781725049853674292157 59837543146893695127859559)
  ·
    refine ⟨89756314720340542691789339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59837543146893695127859559 89756314720340542691789339)
    ·
      refine ⟨134634472080510814037684009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89756314720340542691789339 134634472080510814037684009)
      ·
        refine ⟨100975854060383110528263007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134634472080510814037684009 100975854060383110528263007)
        ·
          refine ⟨151463781090574665792394511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100975854060383110528263007 151463781090574665792394511)
          ·
            refine ⟨227195671635861998688591767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151463781090574665792394511 227195671635861998688591767)
            ·
              refine ⟨340793507453792998032887651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227195671635861998688591767 340793507453792998032887651)
              ·
                refine ⟨511190261180689497049331477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340793507453792998032887651 511190261180689497049331477)
                ·
                  refine ⟨23962043492844820174187413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 511190261180689497049331477 23962043492844820174187413)
                  ·
                    refine ⟨1123220788727100945665035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23962043492844820174187413 1123220788727100945665035)
                    ·
                      rfl

theorem cell23_6562394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_6562394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562394 prefixEnd_6562394 := by exact prefixLift 6562394
  have htrace : WordTrace (prefixWord ++ tailWord_6562394) baseStart_6562394 baseEnd_6562394 := by
    simpa [prefixWord, tailWord_6562394, baseEnd_6562394] using wordTrace_append hprefix tailTrace_6562394
  have hstable : (prefixWord ++ tailWord_6562394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562394).length < 2 ^ (prefixWord ++ tailWord_6562394).sum := by decide
  have hdescent : baseEnd_6562394 < baseStart_6562394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562435 : List Nat := [1, 1, 1, 3, 3, 1, 4, 3, 2, 2, 2]
def baseStart_6562435 : Nat := 118140960795 + 6562435 * 2 ^ 59
def prefixEnd_6562435 : Nat := 4983230072969 + 3 ^ 40 * 6562435 * 2
def baseEnd_6562435 : Nat := 3369683418888137176582417

theorem tailTrace_6562435 : CollatzResearch.WordTrace tailWord_6562435 prefixEnd_6562435 3369683418888137176582417 := by
  unfold tailWord_6562435
  simp only [CollatzResearch.WordTrace]
  refine ⟨239351667980426244513680759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159567778653617496342453839 239351667980426244513680759)
  ·
    refine ⟨359027501970639366770521139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239351667980426244513680759 359027501970639366770521139)
    ·
      refine ⟨538541252955959050155781709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359027501970639366770521139 538541252955959050155781709)
      ·
        refine ⟨201952969858484643808418141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538541252955959050155781709 201952969858484643808418141)
        ·
          refine ⟨75732363696931741428156803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201952969858484643808418141 75732363696931741428156803)
          ·
            refine ⟨113598545545397612142235205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75732363696931741428156803 113598545545397612142235205)
            ·
              refine ⟨21299727289762052276669101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113598545545397612142235205 21299727289762052276669101)
              ·
                refine ⟨7987397733660769603750913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21299727289762052276669101 7987397733660769603750913)
                ·
                  refine ⟨5990548300245577202813185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7987397733660769603750913 5990548300245577202813185)
                  ·
                    refine ⟨4492911225184182902109889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5990548300245577202813185 4492911225184182902109889)
                    ·
                      refine ⟨3369683418888137176582417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492911225184182902109889 3369683418888137176582417)
                      ·
                        rfl

theorem cell23_6562435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_6562435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562435 prefixEnd_6562435 := by exact prefixLift 6562435
  have htrace : WordTrace (prefixWord ++ tailWord_6562435) baseStart_6562435 baseEnd_6562435 := by
    simpa [prefixWord, tailWord_6562435, baseEnd_6562435] using wordTrace_append hprefix tailTrace_6562435
  have hstable : (prefixWord ++ tailWord_6562435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562435).length < 2 ^ (prefixWord ++ tailWord_6562435).sum := by decide
  have hdescent : baseEnd_6562435 < baseStart_6562435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562486 : List Nat := [5, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_6562486 : Nat := 118140960795 + 6562486 * 2 ^ 59
def prefixEnd_6562486 : Nat := 4983230072969 + 3 ^ 40 * 6562486 * 2
def baseEnd_6562486 : Nat := 3369709606401516477044683

theorem tailTrace_6562486 : CollatzResearch.WordTrace tailWord_6562486 prefixEnd_6562486 3369709606401516477044683 := by
  unfold tailWord_6562486
  simp only [CollatzResearch.WordTrace]
  refine ⟨14959595506452592513986707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159569018735494320149191541 14959595506452592513986707)
  ·
    refine ⟨22439393259678888770980061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14959595506452592513986707 22439393259678888770980061)
    ·
      refine ⟨8414772472379583289117523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22439393259678888770980061 8414772472379583289117523)
      ·
        refine ⟨12622158708569374933676285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8414772472379583289117523 12622158708569374933676285)
        ·
          refine ⟨4733309515713515600128607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12622158708569374933676285 4733309515713515600128607)
          ·
            refine ⟨7099964273570273400192911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733309515713515600128607 7099964273570273400192911)
            ·
              refine ⟨10649946410355410100289367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099964273570273400192911 10649946410355410100289367)
              ·
                refine ⟨15974919615533115150434051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10649946410355410100289367 15974919615533115150434051)
                ·
                  refine ⟨23962379423299672725651077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15974919615533115150434051 23962379423299672725651077)
                  ·
                    refine ⟨4492946141868688636059577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23962379423299672725651077 4492946141868688636059577)
                    ·
                      refine ⟨3369709606401516477044683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4492946141868688636059577 3369709606401516477044683)
                      ·
                        rfl

theorem cell23_6562486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_6562486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562486 prefixEnd_6562486 := by exact prefixLift 6562486
  have htrace : WordTrace (prefixWord ++ tailWord_6562486) baseStart_6562486 baseEnd_6562486 := by
    simpa [prefixWord, tailWord_6562486, baseEnd_6562486] using wordTrace_append hprefix tailTrace_6562486
  have hstable : (prefixWord ++ tailWord_6562486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562486).length < 2 ^ (prefixWord ++ tailWord_6562486).sum := by decide
  have hdescent : baseEnd_6562486 < baseStart_6562486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562508 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6562508 : Nat := 118140960795 + 6562508 * 2 ^ 59
def prefixEnd_6562508 : Nat := 4983230072969 + 3 ^ 40 * 6562508 * 2
def baseEnd_6562508 : Nat := 3369720902975915390969581

theorem tailTrace_6562508 : CollatzResearch.WordTrace tailWord_6562508 prefixEnd_6562508 3369720902975915390969581 := by
  unfold tailWord_6562508
  simp only [CollatzResearch.WordTrace]
  refine ⟨119677165254580888990544089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159569553672774518654058785 119677165254580888990544089)
  ·
    refine ⟨89757873940935666742908067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119677165254580888990544089 89757873940935666742908067)
    ·
      refine ⟨134636810911403500114362101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89757873940935666742908067 134636810911403500114362101)
      ·
        refine ⟨12622201022944078135721447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134636810911403500114362101 12622201022944078135721447)
        ·
          refine ⟨18933301534416117203582171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12622201022944078135721447 18933301534416117203582171)
          ·
            refine ⟨28399952301624175805373257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18933301534416117203582171 28399952301624175805373257)
            ·
              refine ⟨21299964226218131854029943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28399952301624175805373257 21299964226218131854029943)
              ·
                refine ⟨31949946339327197781044915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21299964226218131854029943 31949946339327197781044915)
                ·
                  refine ⟨47924919508990796671567373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31949946339327197781044915 47924919508990796671567373)
                  ·
                    refine ⟨17971844815871548751837765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47924919508990796671567373 17971844815871548751837765)
                    ·
                      refine ⟨3369720902975915390969581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17971844815871548751837765 3369720902975915390969581)
                      ·
                        rfl

theorem cell23_6562508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6562508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562508 prefixEnd_6562508 := by exact prefixLift 6562508
  have htrace : WordTrace (prefixWord ++ tailWord_6562508) baseStart_6562508 baseEnd_6562508 := by
    simpa [prefixWord, tailWord_6562508, baseEnd_6562508] using wordTrace_append hprefix tailTrace_6562508
  have hstable : (prefixWord ++ tailWord_6562508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562508).length < 2 ^ (prefixWord ++ tailWord_6562508).sum := by decide
  have hdescent : baseEnd_6562508 < baseStart_6562508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562509 : List Nat := [1, 6, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6562509 : Nat := 118140960795 + 6562509 * 2 ^ 59
def prefixEnd_6562509 : Nat := 4983230072969 + 3 ^ 40 * 6562509 * 2
def baseEnd_6562509 : Nat := 374413490717396654117453

theorem tailTrace_6562509 : CollatzResearch.WordTrace tailWord_6562509 prefixEnd_6562509 374413490717396654117453 := by
  unfold tailWord_6562509
  simp only [CollatzResearch.WordTrace]
  refine ⟨239354366982158155151874581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159569577988105436767916387 239354366982158155151874581)
  ·
    refine ⟨11219735952288663522744121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239354366982158155151874581 11219735952288663522744121)
    ·
      refine ⟨8414801964216497642058091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11219735952288663522744121 8414801964216497642058091)
      ·
        refine ⟨12622202946324746463087137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8414801964216497642058091 12622202946324746463087137)
        ·
          refine ⟨9466652209743559847315353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12622202946324746463087137 9466652209743559847315353)
          ·
            refine ⟨7099989157307669885486515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9466652209743559847315353 7099989157307669885486515)
            ·
              refine ⟨10649983735961504828229773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7099989157307669885486515 10649983735961504828229773)
              ·
                refine ⟨3993743900985564310586165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10649983735961504828229773 3993743900985564310586165)
                ·
                  refine ⟨374413490717396654117453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3993743900985564310586165 374413490717396654117453)
                  ·
                    rfl

theorem cell23_6562509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6562509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562509 prefixEnd_6562509 := by exact prefixLift 6562509
  have htrace : WordTrace (prefixWord ++ tailWord_6562509) baseStart_6562509 baseEnd_6562509 := by
    simpa [prefixWord, tailWord_6562509, baseEnd_6562509] using wordTrace_append hprefix tailTrace_6562509
  have hstable : (prefixWord ++ tailWord_6562509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562509).length < 2 ^ (prefixWord ++ tailWord_6562509).sum := by decide
  have hdescent : baseEnd_6562509 < baseStart_6562509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562562 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_6562562 : Nat := 118140960795 + 6562562 * 2 ^ 59
def prefixEnd_6562562 : Nat := 4983230072969 + 3 ^ 40 * 6562562 * 2
def baseEnd_6562562 : Nat := 3369748630931258179694333

theorem tailTrace_6562562 : CollatzResearch.WordTrace tailWord_6562562 prefixEnd_6562562 3369748630931258179694333 := by
  unfold tailWord_6562562
  simp only [CollatzResearch.WordTrace]
  refine ⟨59839075012741536300888485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159570866700644096802369293 59839075012741536300888485)
  ·
    refine ⟨11219826564889038056416591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59839075012741536300888485 11219826564889038056416591)
    ·
      refine ⟨16829739847333557084624887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11219826564889038056416591 16829739847333557084624887)
      ·
        refine ⟨25244609771000335626937331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16829739847333557084624887 25244609771000335626937331)
        ·
          refine ⟨37866914656500503440405997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25244609771000335626937331 37866914656500503440405997)
          ·
            refine ⟨14200092996187688790152249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37866914656500503440405997 14200092996187688790152249)
            ·
              refine ⟨10650069747140766592614187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14200092996187688790152249 10650069747140766592614187)
              ·
                refine ⟨15975104620711149888921281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10650069747140766592614187 15975104620711149888921281)
                ·
                  refine ⟨11981328465533362416690961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15975104620711149888921281 11981328465533362416690961)
                  ·
                    refine ⟨8985996349150021812518221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11981328465533362416690961 8985996349150021812518221)
                    ·
                      refine ⟨3369748630931258179694333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8985996349150021812518221 3369748630931258179694333)
                      ·
                        rfl

theorem cell23_6562562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_6562562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562562 prefixEnd_6562562 := by exact prefixLift 6562562
  have htrace : WordTrace (prefixWord ++ tailWord_6562562) baseStart_6562562 baseEnd_6562562 := by
    simpa [prefixWord, tailWord_6562562, baseEnd_6562562] using wordTrace_append hprefix tailTrace_6562562
  have hstable : (prefixWord ++ tailWord_6562562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562562).length < 2 ^ (prefixWord ++ tailWord_6562562).sum := by decide
  have hdescent : baseEnd_6562562 < baseStart_6562562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562648 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 3, 3, 3]
def baseStart_6562648 : Nat := 118140960795 + 6562648 * 2 ^ 59
def prefixEnd_6562648 : Nat := 4983230072969 + 3 ^ 40 * 6562648 * 2
def baseEnd_6562648 : Nat := 3369792790267544843218937

theorem tailTrace_6562648 : CollatzResearch.WordTrace tailWord_6562648 prefixEnd_6562648 3369792790267544843218937 := by
  unfold tailWord_6562648
  simp only [CollatzResearch.WordTrace]
  refine ⟨119679718364327290945592299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159572957819103054594123065 119679718364327290945592299)
  ·
    refine ⟨179519577546490936418388449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119679718364327290945592299 179519577546490936418388449)
    ·
      refine ⟨134639683159868202313791337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179519577546490936418388449 134639683159868202313791337)
      ·
        refine ⟨100979762369901151735343503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134639683159868202313791337 100979762369901151735343503)
        ·
          refine ⟨151469643554851727603015255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100979762369901151735343503 151469643554851727603015255)
          ·
            refine ⟨227204465332277591404522883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151469643554851727603015255 227204465332277591404522883)
            ·
              refine ⟨340806697998416387106784325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227204465332277591404522883 340806697998416387106784325)
              ·
                refine ⟨63901255874703072582522061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340806697998416387106784325 63901255874703072582522061)
                ·
                  refine ⟨23962970953013652218445773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63901255874703072582522061 23962970953013652218445773)
                  ·
                    refine ⟨8986114107380119581917165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23962970953013652218445773 8986114107380119581917165)
                    ·
                      refine ⟨3369792790267544843218937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8986114107380119581917165 3369792790267544843218937)
                      ·
                        rfl

theorem cell23_6562648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_6562648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562648 prefixEnd_6562648 := by exact prefixLift 6562648
  have htrace : WordTrace (prefixWord ++ tailWord_6562648) baseStart_6562648 baseEnd_6562648 := by
    simpa [prefixWord, tailWord_6562648, baseEnd_6562648] using wordTrace_append hprefix tailTrace_6562648
  have hstable : (prefixWord ++ tailWord_6562648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562648).length < 2 ^ (prefixWord ++ tailWord_6562648).sum := by decide
  have hdescent : baseEnd_6562648 < baseStart_6562648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562649 : List Nat := [1, 2, 1, 2, 2, 4, 2, 4, 1, 2, 2]
def baseStart_6562649 : Nat := 118140960795 + 6562649 * 2 ^ 59
def prefixEnd_6562649 : Nat := 4983230072969 + 3 ^ 40 * 6562649 * 2
def baseEnd_6562649 : Nat := 3369793303748199339306433

theorem tailTrace_6562649 : CollatzResearch.WordTrace tailWord_6562649 prefixEnd_6562649 3369793303748199339306433 := by
  unfold tailWord_6562649
  simp only [CollatzResearch.WordTrace]
  refine ⟨239359473201650959061971001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159572982134433972707980667 239359473201650959061971001)
  ·
    refine ⟨179519604901238219296478251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239359473201650959061971001 179519604901238219296478251)
    ·
      refine ⟨269279407351857328944717377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179519604901238219296478251 269279407351857328944717377)
      ·
        refine ⟨201959555513892996708538033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269279407351857328944717377 201959555513892996708538033)
        ·
          refine ⟨151469666635419747531403525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201959555513892996708538033 151469666635419747531403525)
          ·
            refine ⟨28400562494141202662138161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151469666635419747531403525 28400562494141202662138161)
            ·
              refine ⟨21300421870605901996603621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28400562494141202662138161 21300421870605901996603621)
              ·
                refine ⟨3993829100738606624363179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21300421870605901996603621 3993829100738606624363179)
                ·
                  refine ⟨5990743651107909936544769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3993829100738606624363179 5990743651107909936544769)
                  ·
                    refine ⟨4493057738330932452408577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5990743651107909936544769 4493057738330932452408577)
                    ·
                      refine ⟨3369793303748199339306433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493057738330932452408577 3369793303748199339306433)
                      ·
                        rfl

theorem cell23_6562649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_6562649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562649 prefixEnd_6562649 := by exact prefixLift 6562649
  have htrace : WordTrace (prefixWord ++ tailWord_6562649) baseStart_6562649 baseEnd_6562649 := by
    simpa [prefixWord, tailWord_6562649, baseEnd_6562649] using wordTrace_append hprefix tailTrace_6562649
  have hstable : (prefixWord ++ tailWord_6562649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562649).length < 2 ^ (prefixWord ++ tailWord_6562649).sum := by decide
  have hdescent : baseEnd_6562649 < baseStart_6562649 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562651 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 8, 7]
def baseStart_6562651 : Nat := 118140960795 + 6562651 * 2 ^ 59
def prefixEnd_6562651 : Nat := 4983230072969 + 3 ^ 40 * 6562651 * 2
def baseEnd_6562651 : Nat := 1123264776903169443827141

theorem tailTrace_6562651 : CollatzResearch.WordTrace tailWord_6562651 prefixEnd_6562651 1123264776903169443827141 := by
  unfold tailWord_6562651
  simp only [CollatzResearch.WordTrace]
  refine ⟨239359546147643713403543807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159573030765095808935695871 239359546147643713403543807)
  ·
    refine ⟨359039319221465570105315711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239359546147643713403543807 359039319221465570105315711)
    ·
      refine ⟨538558978832198355157973567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359039319221465570105315711 538558978832198355157973567)
      ·
        refine ⟨807838468248297532736960351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538558978832198355157973567 807838468248297532736960351)
        ·
          refine ⟨1211757702372446299105440527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807838468248297532736960351 1211757702372446299105440527)
          ·
            refine ⟨1817636553558669448658160791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211757702372446299105440527 1817636553558669448658160791)
            ·
              refine ⟨2726454830338004172987241187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817636553558669448658160791 2726454830338004172987241187)
              ·
                refine ⟨4089682245507006259480861781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726454830338004172987241187 4089682245507006259480861781)
                ·
                  refine ⟨47925963814535229603291349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4089682245507006259480861781 47925963814535229603291349)
                  ·
                    refine ⟨1123264776903169443827141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47925963814535229603291349 1123264776903169443827141)
                    ·
                      rfl

theorem cell23_6562651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 7].length) (baseStart_6562651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562651 prefixEnd_6562651 := by exact prefixLift 6562651
  have htrace : WordTrace (prefixWord ++ tailWord_6562651) baseStart_6562651 baseEnd_6562651 := by
    simpa [prefixWord, tailWord_6562651, baseEnd_6562651] using wordTrace_append hprefix tailTrace_6562651
  have hstable : (prefixWord ++ tailWord_6562651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562651).length < 2 ^ (prefixWord ++ tailWord_6562651).sum := by decide
  have hdescent : baseEnd_6562651 < baseStart_6562651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562675 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 3, 3, 2]
def baseStart_6562675 : Nat := 118140960795 + 6562675 * 2 ^ 59
def prefixEnd_6562675 : Nat := 4983230072969 + 3 ^ 40 * 6562675 * 2
def baseEnd_6562675 : Nat := 3369806654245216237581313

theorem tailTrace_6562675 : CollatzResearch.WordTrace tailWord_6562675 prefixEnd_6562675 3369806654245216237581313 := by
  unfold tailWord_6562675
  simp only [CollatzResearch.WordTrace]
  refine ⟨239360421499556765502417479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159573614333037843668278319 239360421499556765502417479)
  ·
    refine ⟨359040632249335148253626219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239360421499556765502417479 359040632249335148253626219)
    ·
      refine ⟨538560948374002722380439329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359040632249335148253626219 538560948374002722380439329)
      ·
        refine ⟨403920711280502041785329497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538560948374002722380439329 403920711280502041785329497)
        ·
          refine ⟨302940533460376531338997123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403920711280502041785329497 302940533460376531338997123)
          ·
            refine ⟨454410800190564797008495685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302940533460376531338997123 454410800190564797008495685)
            ·
              refine ⟨85202025035730899439092941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 454410800190564797008495685 85202025035730899439092941)
              ·
                refine ⟨31950759388399087289659853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85202025035730899439092941 31950759388399087289659853)
                ·
                  refine ⟨11981534770649657733622445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31950759388399087289659853 11981534770649657733622445)
                  ·
                    refine ⟨4493075538993621650108417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11981534770649657733622445 4493075538993621650108417)
                    ·
                      refine ⟨3369806654245216237581313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493075538993621650108417 3369806654245216237581313)
                      ·
                        rfl

theorem cell23_6562675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 3, 3, 2].length) (baseStart_6562675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562675 prefixEnd_6562675 := by exact prefixLift 6562675
  have htrace : WordTrace (prefixWord ++ tailWord_6562675) baseStart_6562675 baseEnd_6562675 := by
    simpa [prefixWord, tailWord_6562675, baseEnd_6562675] using wordTrace_append hprefix tailTrace_6562675
  have hstable : (prefixWord ++ tailWord_6562675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562675).length < 2 ^ (prefixWord ++ tailWord_6562675).sum := by decide
  have hdescent : baseEnd_6562675 < baseStart_6562675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562772 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_6562772 : Nat := 118140960795 + 6562772 * 2 ^ 59
def prefixEnd_6562772 : Nat := 4983230072969 + 3 ^ 40 * 6562772 * 2
def baseEnd_6562772 : Nat := 3369856461868702358068367

theorem tailTrace_6562772 : CollatzResearch.WordTrace tailWord_6562772 prefixEnd_6562772 3369856461868702358068367 := by
  unfold tailWord_6562772
  simp only [CollatzResearch.WordTrace]
  refine ⟨119681979690102675534349285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159575972920136900712465713 119681979690102675534349285)
  ·
    refine ⟨22440371191894251662690491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119681979690102675534349285 22440371191894251662690491)
    ·
      refine ⟨33660556787841377494035737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22440371191894251662690491 33660556787841377494035737)
      ·
        refine ⟨25245417590881033120526803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33660556787841377494035737 25245417590881033120526803)
        ·
          refine ⟨37868126386321549680790205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25245417590881033120526803 37868126386321549680790205)
          ·
            refine ⟨14200547394870581130296327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37868126386321549680790205 14200547394870581130296327)
            ·
              refine ⟨21300821092305871695444491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14200547394870581130296327 21300821092305871695444491)
              ·
                refine ⟨31951231638458807543166737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21300821092305871695444491 31951231638458807543166737)
                ·
                  refine ⟨23963423728844105657375053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31951231638458807543166737 23963423728844105657375053)
                  ·
                    refine ⟨8986283898316539621515645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23963423728844105657375053 8986283898316539621515645)
                    ·
                      refine ⟨3369856461868702358068367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8986283898316539621515645 3369856461868702358068367)
                      ·
                        rfl

theorem cell23_6562772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_6562772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562772 prefixEnd_6562772 := by exact prefixLift 6562772
  have htrace : WordTrace (prefixWord ++ tailWord_6562772) baseStart_6562772 baseEnd_6562772 := by
    simpa [prefixWord, tailWord_6562772, baseEnd_6562772] using wordTrace_append hprefix tailTrace_6562772
  have hstable : (prefixWord ++ tailWord_6562772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562772).length < 2 ^ (prefixWord ++ tailWord_6562772).sum := by decide
  have hdescent : baseEnd_6562772 < baseStart_6562772 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562788 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_6562788 : Nat := 118140960795 + 6562788 * 2 ^ 59
def prefixEnd_6562788 : Nat := 4983230072969 + 3 ^ 40 * 6562788 * 2
def baseEnd_6562788 : Nat := 1123288225853058098489431

theorem tailTrace_6562788 : CollatzResearch.WordTrace tailWord_6562788 prefixEnd_6562788 1123288225853058098489431 := by
  unfold tailWord_6562788
  simp only [CollatzResearch.WordTrace]
  refine ⟨119682271474073692900640509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159576361965431590534187345 119682271474073692900640509)
  ·
    refine ⟨44880851802777634837740191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119682271474073692900640509 44880851802777634837740191)
    ·
      refine ⟨67321277704166452256610287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44880851802777634837740191 67321277704166452256610287)
      ·
        refine ⟨100981916556249678384915431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67321277704166452256610287 100981916556249678384915431)
        ·
          refine ⟨151472874834374517577373147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100981916556249678384915431 151472874834374517577373147)
          ·
            refine ⟨227209312251561776366059721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151472874834374517577373147 227209312251561776366059721)
            ·
              refine ⟨170406984188671332274544791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227209312251561776366059721 170406984188671332274544791)
              ·
                refine ⟨255610476283006998411817187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170406984188671332274544791 255610476283006998411817187)
                ·
                  refine ⟨383415714424510497617725781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255610476283006998411817187 383415714424510497617725781)
                  ·
                    refine ⟨1123288225853058098489431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 383415714424510497617725781 1123288225853058098489431)
                    ·
                      rfl

theorem cell23_6562788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_6562788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562788 prefixEnd_6562788 := by exact prefixLift 6562788
  have htrace : WordTrace (prefixWord ++ tailWord_6562788) baseStart_6562788 baseEnd_6562788 := by
    simpa [prefixWord, tailWord_6562788, baseEnd_6562788] using wordTrace_append hprefix tailTrace_6562788
  have hstable : (prefixWord ++ tailWord_6562788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562788).length < 2 ^ (prefixWord ++ tailWord_6562788).sum := by decide
  have hdescent : baseEnd_6562788 < baseStart_6562788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562812 : List Nat := [2, 2, 2, 1, 2, 3, 1, 2, 2, 4, 2]
def baseStart_6562812 : Nat := 118140960795 + 6562812 * 2 ^ 59
def prefixEnd_6562812 : Nat := 4983230072969 + 3 ^ 40 * 6562812 * 2
def baseEnd_6562812 : Nat := 3369877001094882201568183

theorem tailTrace_6562812 : CollatzResearch.WordTrace tailWord_6562812 prefixEnd_6562812 3369877001094882201568183 := by
  unfold tailWord_6562812
  simp only [CollatzResearch.WordTrace]
  refine ⟨119682709150030218950077345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159576945533373625266769793 119682709150030218950077345)
  ·
    refine ⟨89762031862522664212558009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119682709150030218950077345 89762031862522664212558009)
    ·
      refine ⟨67321523896891998159418507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89762031862522664212558009 67321523896891998159418507)
      ·
        refine ⟨100982285845337997239127761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67321523896891998159418507 100982285845337997239127761)
        ·
          refine ⟨75736714384003497929345821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100982285845337997239127761 75736714384003497929345821)
          ·
            refine ⟨28401267894001311723504683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75736714384003497929345821 28401267894001311723504683)
            ·
              refine ⟨42601901841001967585257025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28401267894001311723504683 42601901841001967585257025)
              ·
                refine ⟨31951426380751475688942769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42601901841001967585257025 31951426380751475688942769)
                ·
                  refine ⟨23963569785563606766707077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31951426380751475688942769 23963569785563606766707077)
                  ·
                    refine ⟨4493169334793176268757577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23963569785563606766707077 4493169334793176268757577)
                    ·
                      refine ⟨3369877001094882201568183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493169334793176268757577 3369877001094882201568183)
                      ·
                        rfl

theorem cell23_6562812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_6562812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562812 prefixEnd_6562812 := by exact prefixLift 6562812
  have htrace : WordTrace (prefixWord ++ tailWord_6562812) baseStart_6562812 baseEnd_6562812 := by
    simpa [prefixWord, tailWord_6562812, baseEnd_6562812] using wordTrace_append hprefix tailTrace_6562812
  have hstable : (prefixWord ++ tailWord_6562812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562812).length < 2 ^ (prefixWord ++ tailWord_6562812).sum := by decide
  have hdescent : baseEnd_6562812 < baseStart_6562812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562886 : List Nat := [6, 1, 1, 1, 1, 2, 4, 1, 6]
def baseStart_6562886 : Nat := 118140960795 + 6562886 * 2 ^ 59
def prefixEnd_6562886 : Nat := 4983230072969 + 3 ^ 40 * 6562886 * 2
def baseEnd_6562886 : Nat := 374434999851479434671427

theorem tailTrace_6562886 : CollatzResearch.WordTrace tailWord_6562886 prefixEnd_6562886 374434999851479434671427 := by
  unfold tailWord_6562886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480253665681010891823391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159578744867861565692232341 7480253665681010891823391)
  ·
    refine ⟨11220380498521516337735087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480253665681010891823391 11220380498521516337735087)
    ·
      refine ⟨16830570747782274506602631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11220380498521516337735087 16830570747782274506602631)
      ·
        refine ⟨25245856121673411759903947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16830570747782274506602631 25245856121673411759903947)
        ·
          refine ⟨37868784182510117639855921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25245856121673411759903947 37868784182510117639855921)
          ·
            refine ⟨28401588136882588229891941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37868784182510117639855921 28401588136882588229891941)
            ·
              refine ⟨5325297775665485293104739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28401588136882588229891941 5325297775665485293104739)
              ·
                refine ⟨7987946663498227939657109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325297775665485293104739 7987946663498227939657109)
                ·
                  refine ⟨374434999851479434671427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7987946663498227939657109 374434999851479434671427)
                  ·
                    rfl

theorem cell23_6562886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_6562886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562886 prefixEnd_6562886 := by exact prefixLift 6562886
  have htrace : WordTrace (prefixWord ++ tailWord_6562886) baseStart_6562886 baseEnd_6562886 := by
    simpa [prefixWord, tailWord_6562886, baseEnd_6562886] using wordTrace_append hprefix tailTrace_6562886
  have hstable : (prefixWord ++ tailWord_6562886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562886).length < 2 ^ (prefixWord ++ tailWord_6562886).sum := by decide
  have hdescent : baseEnd_6562886 < baseStart_6562886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562925 : List Nat := [1, 5, 1, 1, 2, 13]
def baseStart_6562925 : Nat := 118140960795 + 6562925 * 2 ^ 59
def prefixEnd_6562925 : Nat := 4983230072969 + 3 ^ 40 * 6562925 * 2
def baseEnd_6562925 : Nat := 13868045367937614236441

theorem tailTrace_6562925 : CollatzResearch.WordTrace tailWord_6562925 prefixEnd_6562925 13868045367937614236441 := by
  unfold tailWord_6562925
  simp only [CollatzResearch.WordTrace]
  refine ⟨239369539748651058199018229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159579693165767372132678819 239369539748651058199018229)
  ·
    refine ⟨22440894351436036706157959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239369539748651058199018229 22440894351436036706157959)
    ·
      refine ⟨33661341527154055059236939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22440894351436036706157959 33661341527154055059236939)
      ·
        refine ⟨50492012290731082588855409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33661341527154055059236939 50492012290731082588855409)
        ·
          refine ⟨37869009218048311941641557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50492012290731082588855409 37869009218048311941641557)
          ·
            refine ⟨13868045367937614236441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 37869009218048311941641557 13868045367937614236441)
            ·
              rfl

theorem cell23_6562925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 13].length) (baseStart_6562925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562925 prefixEnd_6562925 := by exact prefixLift 6562925
  have htrace : WordTrace (prefixWord ++ tailWord_6562925) baseStart_6562925 baseEnd_6562925 := by
    simpa [prefixWord, tailWord_6562925, baseEnd_6562925] using wordTrace_append hprefix tailTrace_6562925
  have hstable : (prefixWord ++ tailWord_6562925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562925).length < 2 ^ (prefixWord ++ tailWord_6562925).sum := by decide
  have hdescent : baseEnd_6562925 < baseStart_6562925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562949 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 4]
def baseStart_6562949 : Nat := 118140960795 + 6562949 * 2 ^ 59
def prefixEnd_6562949 : Nat := 4983230072969 + 3 ^ 40 * 6562949 * 2
def baseEnd_6562949 : Nat := 3369947347944548165555053

theorem tailTrace_6562949 : CollatzResearch.WordTrace tailWord_6562949 prefixEnd_6562949 3369947347944548165555053 := by
  unfold tailWord_6562949
  simp only [CollatzResearch.WordTrace]
  refine ⟨239370415100564110297891901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159580276733709406865261267 239370415100564110297891901)
  ·
    refine ⟨89763905662711541361709463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239370415100564110297891901 89763905662711541361709463)
    ·
      refine ⟨134645858494067312042564195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89763905662711541361709463 134645858494067312042564195)
      ·
        refine ⟨201968787741100968063846293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134645858494067312042564195 201968787741100968063846293)
        ·
          refine ⟨9467286925364107877992795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 201968787741100968063846293 9467286925364107877992795)
          ·
            refine ⟨14200930388046161816989193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467286925364107877992795 14200930388046161816989193)
            ·
              refine ⟨10650697791034621362741895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14200930388046161816989193 10650697791034621362741895)
              ·
                refine ⟨15976046686551932044112843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10650697791034621362741895 15976046686551932044112843)
                ·
                  refine ⟨23964070029827898066169265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15976046686551932044112843 23964070029827898066169265)
                  ·
                    refine ⟨17973052522370923549626949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23964070029827898066169265 17973052522370923549626949)
                    ·
                      refine ⟨3369947347944548165555053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17973052522370923549626949 3369947347944548165555053)
                      ·
                        rfl

theorem cell23_6562949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_6562949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562949 prefixEnd_6562949 := by exact prefixLift 6562949
  have htrace : WordTrace (prefixWord ++ tailWord_6562949) baseStart_6562949 baseEnd_6562949 := by
    simpa [prefixWord, tailWord_6562949, baseEnd_6562949] using wordTrace_append hprefix tailTrace_6562949
  have hstable : (prefixWord ++ tailWord_6562949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562949).length < 2 ^ (prefixWord ++ tailWord_6562949).sum := by decide
  have hdescent : baseEnd_6562949 < baseStart_6562949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6562970 : List Nat := [3, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6562970 : Nat := 118140960795 + 6562970 * 2 ^ 59
def prefixEnd_6562970 : Nat := 4983230072969 + 3 ^ 40 * 6562970 * 2
def baseEnd_6562970 : Nat := 3369958131038292583392457

theorem tailTrace_6562970 : CollatzResearch.WordTrace tailWord_6562970 prefixEnd_6562970 3369958131038292583392457 := by
  unfold tailWord_6562970
  simp only [CollatzResearch.WordTrace]
  refine ⟨59842795258372007721101591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159580787355658687256270909 59842795258372007721101591)
  ·
    refine ⟨89764192887558011581652387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59842795258372007721101591 89764192887558011581652387)
    ·
      refine ⟨134646289331337017372478581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89764192887558011581652387 134646289331337017372478581)
      ·
        refine ⟨12623089624812845378669867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134646289331337017372478581 12623089624812845378669867)
        ·
          refine ⟨18934634437219268068004801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12623089624812845378669867 18934634437219268068004801)
          ·
            refine ⟨14200975827914451051003601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18934634437219268068004801 14200975827914451051003601)
            ·
              refine ⟨10650731870935838288252701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14200975827914451051003601 10650731870935838288252701)
              ·
                refine ⟨3994024451600939358094763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10650731870935838288252701 3994024451600939358094763)
                ·
                  refine ⟨5991036677401409037142145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994024451600939358094763 5991036677401409037142145)
                  ·
                    refine ⟨4493277508051056777856609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5991036677401409037142145 4493277508051056777856609)
                    ·
                      refine ⟨3369958131038292583392457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493277508051056777856609 3369958131038292583392457)
                      ·
                        rfl

theorem cell23_6562970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6562970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6562970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6562970 prefixEnd_6562970 := by exact prefixLift 6562970
  have htrace : WordTrace (prefixWord ++ tailWord_6562970) baseStart_6562970 baseEnd_6562970 := by
    simpa [prefixWord, tailWord_6562970, baseEnd_6562970] using wordTrace_append hprefix tailTrace_6562970
  have hstable : (prefixWord ++ tailWord_6562970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6562970).length < 2 ^ (prefixWord ++ tailWord_6562970).sum := by decide
  have hdescent : baseEnd_6562970 < baseStart_6562970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6562970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563010 : List Nat := [3, 5, 1, 1, 3, 1, 2, 7]
def baseStart_6563010 : Nat := 118140960795 + 6563010 * 2 ^ 59
def prefixEnd_6563010 : Nat := 4983230072969 + 3 ^ 40 * 6563010 * 2
def baseEnd_6563010 : Nat := 124814024824610089884899

theorem tailTrace_6563010 : CollatzResearch.WordTrace tailWord_6563010 prefixEnd_6563010 124814024824610089884899 := by
  unfold tailWord_6563010
  simp only [CollatzResearch.WordTrace]
  refine ⟨59843159988335779428965621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159581759968895411810574989 59843159988335779428965621)
  ·
    refine ⟨5610296248906479321465527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59843159988335779428965621 5610296248906479321465527)
    ·
      refine ⟨8415444373359718982198291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5610296248906479321465527 8415444373359718982198291)
      ·
        refine ⟨12623166560039578473297437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415444373359718982198291 12623166560039578473297437)
        ·
          refine ⟨4733687460014841927486539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12623166560039578473297437 4733687460014841927486539)
          ·
            refine ⟨7100531190022262891229809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733687460014841927486539 7100531190022262891229809)
            ·
              refine ⟨5325398392516697168422357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7100531190022262891229809 5325398392516697168422357)
              ·
                refine ⟨124814024824610089884899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5325398392516697168422357 124814024824610089884899)
                ·
                  rfl

theorem cell23_6563010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 7].length) (baseStart_6563010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563010 prefixEnd_6563010 := by exact prefixLift 6563010
  have htrace : WordTrace (prefixWord ++ tailWord_6563010) baseStart_6563010 baseEnd_6563010 := by
    simpa [prefixWord, tailWord_6563010, baseEnd_6563010] using wordTrace_append hprefix tailTrace_6563010
  have hstable : (prefixWord ++ tailWord_6563010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563010).length < 2 ^ (prefixWord ++ tailWord_6563010).sum := by decide
  have hdescent : baseEnd_6563010 < baseStart_6563010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563021 : List Nat := [1, 6, 2, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6563021 : Nat := 118140960795 + 6563021 * 2 ^ 59
def prefixEnd_6563021 : Nat := 4983230072969 + 3 ^ 40 * 6563021 * 2
def baseEnd_6563021 : Nat := 3369984318551671883854723

theorem tailTrace_6563021 : CollatzResearch.WordTrace tailWord_6563021 prefixEnd_6563021 3369984318551671883854723 := by
  unfold tailWord_6563021
  simp only [CollatzResearch.WordTrace]
  refine ⟨239373041156303266594512917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159582027437535511063008611 239373041156303266594512917)
  ·
    refine ⟨11220611304201715621617793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239373041156303266594512917 11220611304201715621617793)
    ·
      refine ⟨8415458478151286716213345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11220611304201715621617793 8415458478151286716213345)
      ·
        refine ⟨6311593858613465037160009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8415458478151286716213345 6311593858613465037160009)
        ·
          refine ⟨4733695393960098777870007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6311593858613465037160009 4733695393960098777870007)
          ·
            refine ⟨7100543090940148166805011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733695393960098777870007 7100543090940148166805011)
            ·
              refine ⟨10650814636410222250207517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100543090940148166805011 10650814636410222250207517)
              ·
                refine ⟨3994055488653833343827819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10650814636410222250207517 3994055488653833343827819)
                ·
                  refine ⟨5991083232980750015741729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994055488653833343827819 5991083232980750015741729)
                  ·
                    refine ⟨4493312424735562511806297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5991083232980750015741729 4493312424735562511806297)
                    ·
                      refine ⟨3369984318551671883854723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493312424735562511806297 3369984318551671883854723)
                      ·
                        rfl

theorem cell23_6563021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6563021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563021 prefixEnd_6563021 := by exact prefixLift 6563021
  have htrace : WordTrace (prefixWord ++ tailWord_6563021) baseStart_6563021 baseEnd_6563021 := by
    simpa [prefixWord, tailWord_6563021, baseEnd_6563021] using wordTrace_append hprefix tailTrace_6563021
  have hstable : (prefixWord ++ tailWord_6563021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563021).length < 2 ^ (prefixWord ++ tailWord_6563021).sum := by decide
  have hdescent : baseEnd_6563021 < baseStart_6563021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563026 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 6, 2, 2]
def baseStart_6563026 : Nat := 118140960795 + 6563026 * 2 ^ 59
def prefixEnd_6563026 : Nat := 4983230072969 + 3 ^ 40 * 6563026 * 2
def baseEnd_6563026 : Nat := 3369986885954944364292199

theorem tailTrace_6563026 : CollatzResearch.WordTrace tailWord_6563026 prefixEnd_6563026 3369986885954944364292199 := by
  unfold tailWord_6563026
  simp only [CollatzResearch.WordTrace]
  refine ⟨59843305880321288112111233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159582149014190101632296621 59843305880321288112111233)
  ·
    refine ⟨44882479410240966084083425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59843305880321288112111233 44882479410240966084083425)
    ·
      refine ⟨33661859557680724563062569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44882479410240966084083425 33661859557680724563062569)
      ·
        refine ⟨25246394668260543422296927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33661859557680724563062569 25246394668260543422296927)
        ·
          refine ⟨37869592002390815133445391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25246394668260543422296927 37869592002390815133445391)
          ·
            refine ⟨56804388003586222700168087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37869592002390815133445391 56804388003586222700168087)
            ·
              refine ⟨85206582005379334050252131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56804388003586222700168087 85206582005379334050252131)
              ·
                refine ⟨127809873008069001075378197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85206582005379334050252131 127809873008069001075378197)
                ·
                  refine ⟨5991087797253234425408353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127809873008069001075378197 5991087797253234425408353)
                  ·
                    refine ⟨4493315847939925819056265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5991087797253234425408353 4493315847939925819056265)
                    ·
                      refine ⟨3369986885954944364292199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493315847939925819056265 3369986885954944364292199)
                      ·
                        rfl

theorem cell23_6563026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_6563026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563026 prefixEnd_6563026 := by exact prefixLift 6563026
  have htrace : WordTrace (prefixWord ++ tailWord_6563026) baseStart_6563026 baseEnd_6563026 := by
    simpa [prefixWord, tailWord_6563026, baseEnd_6563026] using wordTrace_append hprefix tailTrace_6563026
  have hstable : (prefixWord ++ tailWord_6563026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563026).length < 2 ^ (prefixWord ++ tailWord_6563026).sum := by decide
  have hdescent : baseEnd_6563026 < baseStart_6563026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563029 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6563029 : Nat := 118140960795 + 6563029 * 2 ^ 59
def prefixEnd_6563029 : Nat := 4983230072969 + 3 ^ 40 * 6563029 * 2
def baseEnd_6563029 : Nat := 3369988426396907852554685

theorem tailTrace_6563029 : CollatzResearch.WordTrace tailWord_6563029 prefixEnd_6563029 3369988426396907852554685 := by
  unfold tailWord_6563029
  simp only [CollatzResearch.WordTrace]
  refine ⟨239373332940274283960804141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159582221960182855973869427 239373332940274283960804141)
  ·
    refine ⟨89764999852602856485301553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239373332940274283960804141 89764999852602856485301553)
    ·
      refine ⟨67323749889452142363976165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89764999852602856485301553 67323749889452142363976165)
      ·
        refine ⟨12623203104272276693245531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67323749889452142363976165 12623203104272276693245531)
        ·
          refine ⟨18934804656408415039868297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12623203104272276693245531 18934804656408415039868297)
          ·
            refine ⟨14201103492306311279901223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18934804656408415039868297 14201103492306311279901223)
            ·
              refine ⟨21301655238459466919851835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14201103492306311279901223 21301655238459466919851835)
              ·
                refine ⟨31952482857689200379777753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21301655238459466919851835 31952482857689200379777753)
                ·
                  refine ⟨23964362143266900284833315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31952482857689200379777753 23964362143266900284833315)
                  ·
                    refine ⟨35946543214900350427249973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23964362143266900284833315 35946543214900350427249973)
                    ·
                      refine ⟨3369988426396907852554685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35946543214900350427249973 3369988426396907852554685)
                      ·
                        rfl

theorem cell23_6563029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6563029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563029 prefixEnd_6563029 := by exact prefixLift 6563029
  have htrace : WordTrace (prefixWord ++ tailWord_6563029) baseStart_6563029 baseEnd_6563029 := by
    simpa [prefixWord, tailWord_6563029, baseEnd_6563029] using wordTrace_append hprefix tailTrace_6563029
  have hstable : (prefixWord ++ tailWord_6563029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563029).length < 2 ^ (prefixWord ++ tailWord_6563029).sum := by decide
  have hdescent : baseEnd_6563029 < baseStart_6563029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563035 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8]
def baseStart_6563035 : Nat := 118140960795 + 6563035 * 2 ^ 59
def prefixEnd_6563035 : Nat := 4983230072969 + 3 ^ 40 * 6563035 * 2
def baseEnd_6563035 : Nat := 3369991507280834829079657

theorem tailTrace_6563035 : CollatzResearch.WordTrace tailWord_6563035 prefixEnd_6563035 3369991507280834829079657 := by
  unfold tailWord_6563035
  simp only [CollatzResearch.WordTrace]
  refine ⟨239373551778252546985522559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159582367852168364657015039 239373551778252546985522559)
  ·
    refine ⟨359060327667378820478283839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239373551778252546985522559 359060327667378820478283839)
    ·
      refine ⟨538590491501068230717425759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359060327667378820478283839 538590491501068230717425759)
      ·
        refine ⟨807885737251602346076138639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538590491501068230717425759 807885737251602346076138639)
        ·
          refine ⟨1211828605877403519114207959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807885737251602346076138639 1211828605877403519114207959)
          ·
            refine ⟨1817742908816105278671311939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211828605877403519114207959 1817742908816105278671311939)
            ·
              refine ⟨2726614363224157918006967909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817742908816105278671311939 2726614363224157918006967909)
              ·
                refine ⟨511240193104529609626306483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2726614363224157918006967909 511240193104529609626306483)
                ·
                  refine ⟨766860289656794414439459725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511240193104529609626306483 766860289656794414439459725)
                  ·
                    refine ⟨287572608621297905414797397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 766860289656794414439459725 287572608621297905414797397)
                    ·
                      refine ⟨3369991507280834829079657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 287572608621297905414797397 3369991507280834829079657)
                      ·
                        rfl

theorem cell23_6563035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 8].length) (baseStart_6563035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563035 prefixEnd_6563035 := by exact prefixLift 6563035
  have htrace : WordTrace (prefixWord ++ tailWord_6563035) baseStart_6563035 baseEnd_6563035 := by
    simpa [prefixWord, tailWord_6563035, baseEnd_6563035] using wordTrace_append hprefix tailTrace_6563035
  have hstable : (prefixWord ++ tailWord_6563035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563035).length < 2 ^ (prefixWord ++ tailWord_6563035).sum := by decide
  have hdescent : baseEnd_6563035 < baseStart_6563035 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563099 : List Nat := [1, 1, 1, 1, 1, 1, 5, 4, 2, 4, 2]
def baseStart_6563099 : Nat := 118140960795 + 6563099 * 2 ^ 59
def prefixEnd_6563099 : Nat := 4983230072969 + 3 ^ 40 * 6563099 * 2
def baseEnd_6563099 : Nat := 3370024370042722578679363

theorem tailTrace_6563099 : CollatzResearch.WordTrace tailWord_6563099 prefixEnd_6563099 3370024370042722578679363 := by
  unfold tailWord_6563099
  simp only [CollatzResearch.WordTrace]
  refine ⟨239375886050020685915852351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159583924033347123943901567 239375886050020685915852351)
  ·
    refine ⟨359063829075031028873778527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239375886050020685915852351 359063829075031028873778527)
    ·
      refine ⟨538595743612546543310667791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359063829075031028873778527 538595743612546543310667791)
      ·
        refine ⟨807893615418819814966001687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538595743612546543310667791 807893615418819814966001687)
        ·
          refine ⟨1211840423128229722449002531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807893615418819814966001687 1211840423128229722449002531)
          ·
            refine ⟨1817760634692344583673503797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211840423128229722449002531 1817760634692344583673503797)
            ·
              refine ⟨170415059502407304719390981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1817760634692344583673503797 170415059502407304719390981)
              ·
                refine ⟨31952823656701369634885809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170415059502407304719390981 31952823656701369634885809)
                ·
                  refine ⟨23964617742526027226164357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31952823656701369634885809 23964617742526027226164357)
                  ·
                    refine ⟨4493365826723630104905817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23964617742526027226164357 4493365826723630104905817)
                    ·
                      refine ⟨3370024370042722578679363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493365826723630104905817 3370024370042722578679363)
                      ·
                        rfl

theorem cell23_6563099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2, 4, 2].length) (baseStart_6563099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563099 prefixEnd_6563099 := by exact prefixLift 6563099
  have htrace : WordTrace (prefixWord ++ tailWord_6563099) baseStart_6563099 baseEnd_6563099 := by
    simpa [prefixWord, tailWord_6563099, baseEnd_6563099] using wordTrace_append hprefix tailTrace_6563099
  have hstable : (prefixWord ++ tailWord_6563099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563099).length < 2 ^ (prefixWord ++ tailWord_6563099).sum := by decide
  have hdescent : baseEnd_6563099 < baseStart_6563099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563143 : List Nat := [1, 1, 4, 1, 2, 4, 2, 3, 1, 4]
def baseStart_6563143 : Nat := 118140960795 + 6563143 * 2 ^ 59
def prefixEnd_6563143 : Nat := 4983230072969 + 3 ^ 40 * 6563143 * 2
def baseEnd_6563143 : Nat := 1123348987730506802176387

theorem tailTrace_6563143 : CollatzResearch.WordTrace tailWord_6563143 prefixEnd_6563143 1123348987730506802176387 := by
  unfold tailWord_6563143
  simp only [CollatzResearch.WordTrace]
  refine ⟨239377490861861281430454083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159584993907907520953636055 239377490861861281430454083)
  ·
    refine ⟨359066236292791922145681125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239377490861861281430454083 359066236292791922145681125)
    ·
      refine ⟨67324919304898485402315211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359066236292791922145681125 67324919304898485402315211)
      ·
        refine ⟨100987378957347728103472817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67324919304898485402315211 100987378957347728103472817)
        ·
          refine ⟨75740534218010796077604613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100987378957347728103472817 75740534218010796077604613)
          ·
            refine ⟨14201350165877024264550865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75740534218010796077604613 14201350165877024264550865)
            ·
              refine ⟨10651012624407768198413149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14201350165877024264550865 10651012624407768198413149)
              ·
                refine ⟨3994129734152913074404931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10651012624407768198413149 3994129734152913074404931)
                ·
                  refine ⟨5991194601229369611607397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994129734152913074404931 5991194601229369611607397)
                  ·
                    refine ⟨1123348987730506802176387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5991194601229369611607397 1123348987730506802176387)
                    ·
                      rfl

theorem cell23_6563143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_6563143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563143 prefixEnd_6563143 := by exact prefixLift 6563143
  have htrace : WordTrace (prefixWord ++ tailWord_6563143) baseStart_6563143 baseEnd_6563143 := by
    simpa [prefixWord, tailWord_6563143, baseEnd_6563143] using wordTrace_append hprefix tailTrace_6563143
  have hstable : (prefixWord ++ tailWord_6563143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563143).length < 2 ^ (prefixWord ++ tailWord_6563143).sum := by decide
  have hdescent : baseEnd_6563143 < baseStart_6563143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563186 : List Nat := [3, 2, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_6563186 : Nat := 118140960795 + 6563186 * 2 ^ 59
def prefixEnd_6563186 : Nat := 4983230072969 + 3 ^ 40 * 6563186 * 2
def baseEnd_6563186 : Nat := 1123356347619887912763821

theorem tailTrace_6563186 : CollatzResearch.WordTrace tailWord_6563186 prefixEnd_6563186 1123356347619887912763821 := by
  unfold tailWord_6563186
  simp only [CollatzResearch.WordTrace]
  refine ⟨59844764800176374943567353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159586039467136999849512941 59844764800176374943567353)
  ·
    refine ⟨44883573600132281207675515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59844764800176374943567353 44883573600132281207675515)
    ·
      refine ⟨67325360400198421811513273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44883573600132281207675515 67325360400198421811513273)
      ·
        refine ⟨50494020300148816358634955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67325360400198421811513273 50494020300148816358634955)
        ·
          refine ⟨75741030450223224537952433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50494020300148816358634955 75741030450223224537952433)
          ·
            refine ⟨56805772837667418403464325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75741030450223224537952433 56805772837667418403464325)
            ·
              refine ⟨10651082407062640950649561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56805772837667418403464325 10651082407062640950649561)
              ·
                refine ⟨7988311805296980712987171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10651082407062640950649561 7988311805296980712987171)
                ·
                  refine ⟨11982467707945471069480757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988311805296980712987171 11982467707945471069480757)
                  ·
                    refine ⟨1123356347619887912763821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11982467707945471069480757 1123356347619887912763821)
                    ·
                      rfl

theorem cell23_6563186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_6563186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563186 prefixEnd_6563186 := by exact prefixLift 6563186
  have htrace : WordTrace (prefixWord ++ tailWord_6563186) baseStart_6563186 baseEnd_6563186 := by
    simpa [prefixWord, tailWord_6563186, baseEnd_6563186] using wordTrace_append hprefix tailTrace_6563186
  have hstable : (prefixWord ++ tailWord_6563186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563186).length < 2 ^ (prefixWord ++ tailWord_6563186).sum := by decide
  have hdescent : baseEnd_6563186 < baseStart_6563186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563226 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6563226 : Nat := 118140960795 + 6563226 * 2 ^ 59
def prefixEnd_6563226 : Nat := 4983230072969 + 3 ^ 40 * 6563226 * 2
def baseEnd_6563226 : Nat := 3370089582085843581791279

theorem tailTrace_6563226 : CollatzResearch.WordTrace tailWord_6563226 prefixEnd_6563226 3370089582085843581791279 := by
  unfold tailWord_6563226
  simp only [CollatzResearch.WordTrace]
  refine ⟨59845129530140146651431383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159587012080373724403817021 59845129530140146651431383)
  ·
    refine ⟨89767694295210219977147075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59845129530140146651431383 89767694295210219977147075)
    ·
      refine ⟨134651541442815329965720613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89767694295210219977147075 134651541442815329965720613)
      ·
        refine ⟨25247164020527874368572615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134651541442815329965720613 25247164020527874368572615)
        ·
          refine ⟨37870746030791811552858923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25247164020527874368572615 37870746030791811552858923)
          ·
            refine ⟨56806119046187717329288385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37870746030791811552858923 56806119046187717329288385)
            ·
              refine ⟨42604589284640787996966289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56806119046187717329288385 42604589284640787996966289)
              ·
                refine ⟨31953441963480590997724717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42604589284640787996966289 31953441963480590997724717)
                ·
                  refine ⟨11982540736305221624146769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31953441963480590997724717 11982540736305221624146769)
                  ·
                    refine ⟨8986905552228916218110077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11982540736305221624146769 8986905552228916218110077)
                    ·
                      refine ⟨3370089582085843581791279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8986905552228916218110077 3370089582085843581791279)
                      ·
                        rfl

theorem cell23_6563226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6563226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563226 prefixEnd_6563226 := by exact prefixLift 6563226
  have htrace : WordTrace (prefixWord ++ tailWord_6563226) baseStart_6563226 baseEnd_6563226 := by
    simpa [prefixWord, tailWord_6563226, baseEnd_6563226] using wordTrace_append hprefix tailTrace_6563226
  have hstable : (prefixWord ++ tailWord_6563226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563226).length < 2 ^ (prefixWord ++ tailWord_6563226).sum := by decide
  have hdescent : baseEnd_6563226 < baseStart_6563226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563229 : List Nat := [1, 4, 2, 1, 3, 1, 1, 10]
def baseStart_6563229 : Nat := 118140960795 + 6563229 * 2 ^ 59
def prefixEnd_6563229 : Nat := 4983230072969 + 3 ^ 40 * 6563229 * 2
def baseEnd_6563229 : Nat := 124818189723252113705695

theorem tailTrace_6563229 : CollatzResearch.WordTrace tailWord_6563229 prefixEnd_6563229 124818189723252113705695 := by
  unfold tailWord_6563229
  simp only [CollatzResearch.WordTrace]
  refine ⟨239380627539549718118084741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159587085026366478745389827 239380627539549718118084741)
  ·
    refine ⟨44883867663665572147140889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239380627539549718118084741 44883867663665572147140889)
    ·
      refine ⟨33662900747749179110355667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44883867663665572147140889 33662900747749179110355667)
      ·
        refine ⟨50494351121623768665533501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33662900747749179110355667 50494351121623768665533501)
        ·
          refine ⟨18935381670608913249575063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50494351121623768665533501 18935381670608913249575063)
          ·
            refine ⟨28403072505913369874362595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18935381670608913249575063 28403072505913369874362595)
            ·
              refine ⟨42604608758870054811543893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28403072505913369874362595 42604608758870054811543893)
              ·
                refine ⟨124818189723252113705695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42604608758870054811543893 124818189723252113705695)
                ·
                  rfl

theorem cell23_6563229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 10].length) (baseStart_6563229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563229 prefixEnd_6563229 := by exact prefixLift 6563229
  have htrace : WordTrace (prefixWord ++ tailWord_6563229) baseStart_6563229 baseEnd_6563229 := by
    simpa [prefixWord, tailWord_6563229, baseEnd_6563229] using wordTrace_append hprefix tailTrace_6563229
  have hstable : (prefixWord ++ tailWord_6563229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563229).length < 2 ^ (prefixWord ++ tailWord_6563229).sum := by decide
  have hdescent : baseEnd_6563229 < baseStart_6563229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563256 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 6, 1, 3]
def baseStart_6563256 : Nat := 118140960795 + 6563256 * 2 ^ 59
def prefixEnd_6563256 : Nat := 4983230072969 + 3 ^ 40 * 6563256 * 2
def baseEnd_6563256 : Nat := 3370104986505478464416141

theorem tailTrace_6563256 : CollatzResearch.WordTrace tailWord_6563256 prefixEnd_6563256 3370104986505478464416141 := by
  unfold tailWord_6563256
  simp only [CollatzResearch.WordTrace]
  refine ⟨119690806155225950864658811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159587741540301267819545081 119690806155225950864658811)
  ·
    refine ⟨179536209232838926296988217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119690806155225950864658811 179536209232838926296988217)
    ·
      refine ⟨134652156924629194722741163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179536209232838926296988217 134652156924629194722741163)
      ·
        refine ⟨201978235386943792084111745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134652156924629194722741163 201978235386943792084111745)
        ·
          refine ⟨151483676540207844063083809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201978235386943792084111745 151483676540207844063083809)
          ·
            refine ⟨113612757405155883047312857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151483676540207844063083809 113612757405155883047312857)
            ·
              refine ⟨85209568053866912285484643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113612757405155883047312857 85209568053866912285484643)
              ·
                refine ⟨127814352080800368428226965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85209568053866912285484643 127814352080800368428226965)
                ·
                  refine ⟨5991297753787517270073139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127814352080800368428226965 5991297753787517270073139)
                  ·
                    refine ⟨8986946630681275905109709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5991297753787517270073139 8986946630681275905109709)
                    ·
                      refine ⟨3370104986505478464416141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8986946630681275905109709 3370104986505478464416141)
                      ·
                        rfl

theorem cell23_6563256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 6, 1, 3].length) (baseStart_6563256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563256 prefixEnd_6563256 := by exact prefixLift 6563256
  have htrace : WordTrace (prefixWord ++ tailWord_6563256) baseStart_6563256 baseEnd_6563256 := by
    simpa [prefixWord, tailWord_6563256, baseEnd_6563256] using wordTrace_append hprefix tailTrace_6563256
  have hstable : (prefixWord ++ tailWord_6563256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563256).length < 2 ^ (prefixWord ++ tailWord_6563256).sum := by decide
  have hdescent : baseEnd_6563256 < baseStart_6563256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563260 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6563260 : Nat := 118140960795 + 6563260 * 2 ^ 59
def prefixEnd_6563260 : Nat := 4983230072969 + 3 ^ 40 * 6563260 * 2
def baseEnd_6563260 : Nat := 3370107040428096448766123

theorem tailTrace_6563260 : CollatzResearch.WordTrace tailWord_6563260 prefixEnd_6563260 3370107040428096448766123 := by
  unfold tailWord_6563260
  simp only [CollatzResearch.WordTrace]
  refine ⟨119690879101218705206231617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159587838801624940274975489 119690879101218705206231617)
  ·
    refine ⟨89768159325914028904673713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119690879101218705206231617 89768159325914028904673713)
    ·
      refine ⟨67326119494435521678505285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89768159325914028904673713 67326119494435521678505285)
      ·
        refine ⟨12623647405206660314719741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67326119494435521678505285 12623647405206660314719741)
        ·
          refine ⟨4733867776952497618019903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12623647405206660314719741 4733867776952497618019903)
          ·
            refine ⟨7100801665428746427029855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4733867776952497618019903 7100801665428746427029855)
            ·
              refine ⟨10651202498143119640544783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7100801665428746427029855 10651202498143119640544783)
              ·
                refine ⟨15976803747214679460817175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10651202498143119640544783 15976803747214679460817175)
                ·
                  refine ⟨23965205620822019191225763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15976803747214679460817175 23965205620822019191225763)
                  ·
                    refine ⟨35947808431233028786838645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23965205620822019191225763 35947808431233028786838645)
                    ·
                      refine ⟨3370107040428096448766123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35947808431233028786838645 3370107040428096448766123)
                      ·
                        rfl

theorem cell23_6563260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6563260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563260 prefixEnd_6563260 := by exact prefixLift 6563260
  have htrace : WordTrace (prefixWord ++ tailWord_6563260) baseStart_6563260 baseEnd_6563260 := by
    simpa [prefixWord, tailWord_6563260, baseEnd_6563260] using wordTrace_append hprefix tailTrace_6563260
  have hstable : (prefixWord ++ tailWord_6563260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563260).length < 2 ^ (prefixWord ++ tailWord_6563260).sum := by decide
  have hdescent : baseEnd_6563260 < baseStart_6563260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563274 : List Nat := [3, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_6563274 : Nat := 118140960795 + 6563274 * 2 ^ 59
def prefixEnd_6563274 : Nat := 4983230072969 + 3 ^ 40 * 6563274 * 2
def baseEnd_6563274 : Nat := 3370114229157259393991059

theorem tailTrace_6563274 : CollatzResearch.WordTrace tailWord_6563274 prefixEnd_6563274 3370114229157259393991059 := by
  unfold tailWord_6563274
  simp only [CollatzResearch.WordTrace]
  refine ⟨59845567206096672700868219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159588179216257793868981917 59845567206096672700868219)
  ·
    refine ⟨89768350809145009051302329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59845567206096672700868219 89768350809145009051302329)
    ·
      refine ⟨67326263106858756788476747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89768350809145009051302329 67326263106858756788476747)
      ·
        refine ⟨100989394660288135182715121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67326263106858756788476747 100989394660288135182715121)
        ·
          refine ⟨75742045995216101387036341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100989394660288135182715121 75742045995216101387036341)
          ·
            refine ⟨7100816812051509505034657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75742045995216101387036341 7100816812051509505034657)
            ·
              refine ⟨5325612609038632128775993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7100816812051509505034657 5325612609038632128775993)
              ·
                refine ⟨3994209456778974096581995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5325612609038632128775993 3994209456778974096581995)
                ·
                  refine ⟨5991314185168461144872993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994209456778974096581995 5991314185168461144872993)
                  ·
                    refine ⟨4493485638876345858654745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5991314185168461144872993 4493485638876345858654745)
                    ·
                      refine ⟨3370114229157259393991059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493485638876345858654745 3370114229157259393991059)
                      ·
                        rfl

theorem cell23_6563274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_6563274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563274 prefixEnd_6563274 := by exact prefixLift 6563274
  have htrace : WordTrace (prefixWord ++ tailWord_6563274) baseStart_6563274 baseEnd_6563274 := by
    simpa [prefixWord, tailWord_6563274, baseEnd_6563274] using wordTrace_append hprefix tailTrace_6563274
  have hstable : (prefixWord ++ tailWord_6563274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563274).length < 2 ^ (prefixWord ++ tailWord_6563274).sum := by decide
  have hdescent : baseEnd_6563274 < baseStart_6563274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563279 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_6563279 : Nat := 118140960795 + 6563279 * 2 ^ 59
def prefixEnd_6563279 : Nat := 4983230072969 + 3 ^ 40 * 6563279 * 2
def baseEnd_6563279 : Nat := 3370116796560531874428535

theorem tailTrace_6563279 : CollatzResearch.WordTrace tailWord_6563279 prefixEnd_6563279 3370116796560531874428535 := by
  unfold tailWord_6563279
  simp only [CollatzResearch.WordTrace]
  refine ⟨239382451189368576657404891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159588300792912384438269927 239382451189368576657404891)
  ·
    refine ⟨359073676784052864986107337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239382451189368576657404891 359073676784052864986107337)
    ·
      refine ⟨269305257588039648739580503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359073676784052864986107337 269305257588039648739580503)
      ·
        refine ⟨403957886382059473109370755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269305257588039648739580503 403957886382059473109370755)
        ·
          refine ⟨605936829573089209664056133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403957886382059473109370755 605936829573089209664056133)
          ·
            refine ⟨113613155544954226812010525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 605936829573089209664056133 113613155544954226812010525)
            ·
              refine ⟨42604933329357835054503947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113613155544954226812010525 42604933329357835054503947)
              ·
                refine ⟨63907399994036752581755921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42604933329357835054503947 63907399994036752581755921)
                ·
                  refine ⟨47930549995527564436316941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63907399994036752581755921 47930549995527564436316941)
                  ·
                    refine ⟨17973956248322836663618853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47930549995527564436316941 17973956248322836663618853)
                    ·
                      refine ⟨3370116796560531874428535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17973956248322836663618853 3370116796560531874428535)
                      ·
                        rfl

theorem cell23_6563279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_6563279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563279 prefixEnd_6563279 := by exact prefixLift 6563279
  have htrace : WordTrace (prefixWord ++ tailWord_6563279) baseStart_6563279 baseEnd_6563279 := by
    simpa [prefixWord, tailWord_6563279, baseEnd_6563279] using wordTrace_append hprefix tailTrace_6563279
  have hstable : (prefixWord ++ tailWord_6563279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563279).length < 2 ^ (prefixWord ++ tailWord_6563279).sum := by decide
  have hdescent : baseEnd_6563279 < baseStart_6563279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563289 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 1, 8]
def baseStart_6563289 : Nat := 118140960795 + 6563289 * 2 ^ 59
def prefixEnd_6563289 : Nat := 4983230072969 + 3 ^ 40 * 6563289 * 2
def baseEnd_6563289 : Nat := 1123373977122358945101163

theorem tailTrace_6563289 : CollatzResearch.WordTrace tailWord_6563289 prefixEnd_6563289 1123373977122358945101163 := by
  unfold tailWord_6563289
  simp only [CollatzResearch.WordTrace]
  refine ⟨239382815919332348365268921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159588543946221565576845947 239382815919332348365268921)
  ·
    refine ⟨179537111939499261273951691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239382815919332348365268921 179537111939499261273951691)
    ·
      refine ⟨269305667909248891910927537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179537111939499261273951691 269305667909248891910927537)
      ·
        refine ⟨201979250931936668933195653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269305667909248891910927537 201979250931936668933195653)
        ·
          refine ⟨37871109549738125424974185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201979250931936668933195653 37871109549738125424974185)
          ·
            refine ⟨28403332162303594068730639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37871109549738125424974185 28403332162303594068730639)
            ·
              refine ⟨42604998243455391103095959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28403332162303594068730639 42604998243455391103095959)
              ·
                refine ⟨63907497365183086654643939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42604998243455391103095959 63907497365183086654643939)
                ·
                  refine ⟨95861246047774629981965909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63907497365183086654643939 95861246047774629981965909)
                  ·
                    refine ⟨1123373977122358945101163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95861246047774629981965909 1123373977122358945101163)
                    ·
                      rfl

theorem cell23_6563289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 8].length) (baseStart_6563289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563289 prefixEnd_6563289 := by exact prefixLift 6563289
  have htrace : WordTrace (prefixWord ++ tailWord_6563289) baseStart_6563289 baseEnd_6563289 := by
    simpa [prefixWord, tailWord_6563289, baseEnd_6563289] using wordTrace_append hprefix tailTrace_6563289
  have hstable : (prefixWord ++ tailWord_6563289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563289).length < 2 ^ (prefixWord ++ tailWord_6563289).sum := by decide
  have hdescent : baseEnd_6563289 < baseStart_6563289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563313 : List Nat := [1, 2, 2, 2, 3, 2, 2, 2, 1, 4, 2]
def baseStart_6563313 : Nat := 118140960795 + 6563313 * 2 ^ 59
def prefixEnd_6563313 : Nat := 4983230072969 + 3 ^ 40 * 6563313 * 2
def baseEnd_6563313 : Nat := 3370134254902784741403379

theorem tailTrace_6563313 : CollatzResearch.WordTrace tailWord_6563313 prefixEnd_6563313 3370134254902784741403379 := by
  unfold tailWord_6563313
  simp only [CollatzResearch.WordTrace]
  refine ⟨239383691271245400464142593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159589127514163600309428395 239383691271245400464142593)
  ·
    refine ⟨179537768453434050348106945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239383691271245400464142593 179537768453434050348106945)
    ·
      refine ⟨134653326340075537761080209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179537768453434050348106945 134653326340075537761080209)
      ·
        refine ⟨100989994755056653320810157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134653326340075537761080209 100989994755056653320810157)
        ·
          refine ⟨37871248033146244995303809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100989994755056653320810157 37871248033146244995303809)
          ·
            refine ⟨28403436024859683746477857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37871248033146244995303809 28403436024859683746477857)
            ·
              refine ⟨21302577018644762809858393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28403436024859683746477857 21302577018644762809858393)
              ·
                refine ⟨15976932763983572107393795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21302577018644762809858393 15976932763983572107393795)
                ·
                  refine ⟨23965399145975358161090693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15976932763983572107393795 23965399145975358161090693)
                  ·
                    refine ⟨4493512339870379655204505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23965399145975358161090693 4493512339870379655204505)
                    ·
                      refine ⟨3370134254902784741403379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493512339870379655204505 3370134254902784741403379)
                      ·
                        rfl

theorem cell23_6563313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_6563313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563313 prefixEnd_6563313 := by exact prefixLift 6563313
  have htrace : WordTrace (prefixWord ++ tailWord_6563313) baseStart_6563313 baseEnd_6563313 := by
    simpa [prefixWord, tailWord_6563313, baseEnd_6563313] using wordTrace_append hprefix tailTrace_6563313
  have hstable : (prefixWord ++ tailWord_6563313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563313).length < 2 ^ (prefixWord ++ tailWord_6563313).sum := by decide
  have hdescent : baseEnd_6563313 < baseStart_6563313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563317 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6563317 : Nat := 118140960795 + 6563317 * 2 ^ 59
def prefixEnd_6563317 : Nat := 4983230072969 + 3 ^ 40 * 6563317 * 2
def baseEnd_6563317 : Nat := 3370136308825402725753361

theorem tailTrace_6563317 : CollatzResearch.WordTrace tailWord_6563317 prefixEnd_6563317 3370136308825402725753361 := by
  unfold tailWord_6563317
  simp only [CollatzResearch.WordTrace]
  refine ⟨239383837163230909147288205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159589224775487272764858803 239383837163230909147288205)
  ·
    refine ⟨89768938936211590930233077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239383837163230909147288205 89768938936211590930233077)
    ·
      refine ⟨8415838025269836649709351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89768938936211590930233077 8415838025269836649709351)
      ·
        refine ⟨12623757037904754974564027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415838025269836649709351 12623757037904754974564027)
        ·
          refine ⟨18935635556857132461846041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12623757037904754974564027 18935635556857132461846041)
          ·
            refine ⟨14201726667642849346384531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18935635556857132461846041 14201726667642849346384531)
            ·
              refine ⟨21302590001464274019576797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14201726667642849346384531 21302590001464274019576797)
              ·
                refine ⟨7988471250549102757341299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21302590001464274019576797 7988471250549102757341299)
                ·
                  refine ⟨11982706875823654136011949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988471250549102757341299 11982706875823654136011949)
                  ·
                    refine ⟨4493515078433870301004481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11982706875823654136011949 4493515078433870301004481)
                    ·
                      refine ⟨3370136308825402725753361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493515078433870301004481 3370136308825402725753361)
                      ·
                        rfl

theorem cell23_6563317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6563317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563317 prefixEnd_6563317 := by exact prefixLift 6563317
  have htrace : WordTrace (prefixWord ++ tailWord_6563317) baseStart_6563317 baseEnd_6563317 := by
    simpa [prefixWord, tailWord_6563317, baseEnd_6563317] using wordTrace_append hprefix tailTrace_6563317
  have hstable : (prefixWord ++ tailWord_6563317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563317).length < 2 ^ (prefixWord ++ tailWord_6563317).sum := by decide
  have hdescent : baseEnd_6563317 < baseStart_6563317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563341 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6563341 : Nat := 118140960795 + 6563341 * 2 ^ 59
def prefixEnd_6563341 : Nat := 4983230072969 + 3 ^ 40 * 6563341 * 2
def baseEnd_6563341 : Nat := 3370148632361110631853251

theorem tailTrace_6563341 : CollatzResearch.WordTrace tailWord_6563341 prefixEnd_6563341 3370148632361110631853251 := by
  unfold tailWord_6563341
  simp only [CollatzResearch.WordTrace]
  refine ⟨239384712515143961246161877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159589808343429307497441251 239384712515143961246161877)
  ·
    refine ⟨5610579199573686591706919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 239384712515143961246161877 5610579199573686591706919)
    ·
      refine ⟨8415868799360529887560379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5610579199573686591706919 8415868799360529887560379)
      ·
        refine ⟨12623803199040794831340569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8415868799360529887560379 12623803199040794831340569)
        ·
          refine ⟨9467852399280596123505427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12623803199040794831340569 9467852399280596123505427)
          ·
            refine ⟨14201778598920894185258141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467852399280596123505427 14201778598920894185258141)
            ·
              refine ⟨5325666974595335319471803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14201778598920894185258141 5325666974595335319471803)
              ·
                refine ⟨7988500461893002979207705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325666974595335319471803 7988500461893002979207705)
                ·
                  refine ⟨5991375346419752234405779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7988500461893002979207705 5991375346419752234405779)
                  ·
                    refine ⟨8987063019629628351608669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5991375346419752234405779 8987063019629628351608669)
                    ·
                      refine ⟨3370148632361110631853251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8987063019629628351608669 3370148632361110631853251)
                      ·
                        rfl

theorem cell23_6563341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6563341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563341 prefixEnd_6563341 := by exact prefixLift 6563341
  have htrace : WordTrace (prefixWord ++ tailWord_6563341) baseStart_6563341 baseEnd_6563341 := by
    simpa [prefixWord, tailWord_6563341, baseEnd_6563341] using wordTrace_append hprefix tailTrace_6563341
  have hstable : (prefixWord ++ tailWord_6563341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563341).length < 2 ^ (prefixWord ++ tailWord_6563341).sum := by decide
  have hdescent : baseEnd_6563341 < baseStart_6563341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563347 : List Nat := [1, 1, 1, 2, 1, 7, 3, 1, 2, 2, 2]
def baseStart_6563347 : Nat := 118140960795 + 6563347 * 2 ^ 59
def prefixEnd_6563347 : Nat := 4983230072969 + 3 ^ 40 * 6563347 * 2
def baseEnd_6563347 : Nat := 3370151713245037608378223

theorem tailTrace_6563347 : CollatzResearch.WordTrace tailWord_6563347 prefixEnd_6563347 3370151713245037608378223 := by
  unfold tailWord_6563347
  simp only [CollatzResearch.WordTrace]
  refine ⟨239384931353122224270880295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159589954235414816180586863 239384931353122224270880295)
  ·
    refine ⟨359077397029683336406320443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239384931353122224270880295 359077397029683336406320443)
    ·
      refine ⟨538616095544525004609480665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359077397029683336406320443 538616095544525004609480665)
      ·
        refine ⟨403962071658393753457110499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538616095544525004609480665 403962071658393753457110499)
        ·
          refine ⟨605943107487590630185665749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403962071658393753457110499 605943107487590630185665749)
          ·
            refine ⟨14201791581740405394976541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 605943107487590630185665749 14201791581740405394976541)
            ·
              refine ⟨5325671843152652023116203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14201791581740405394976541 5325671843152652023116203)
              ·
                refine ⟨7988507764728978034674305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325671843152652023116203 7988507764728978034674305)
                ·
                  refine ⟨5991380823546733526005729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7988507764728978034674305 5991380823546733526005729)
                  ·
                    refine ⟨4493535617660050144504297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5991380823546733526005729 4493535617660050144504297)
                    ·
                      refine ⟨3370151713245037608378223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493535617660050144504297 3370151713245037608378223)
                      ·
                        rfl

theorem cell23_6563347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 3, 1, 2, 2, 2].length) (baseStart_6563347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563347 prefixEnd_6563347 := by exact prefixLift 6563347
  have htrace : WordTrace (prefixWord ++ tailWord_6563347) baseStart_6563347 baseEnd_6563347 := by
    simpa [prefixWord, tailWord_6563347, baseEnd_6563347] using wordTrace_append hprefix tailTrace_6563347
  have hstable : (prefixWord ++ tailWord_6563347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563347).length < 2 ^ (prefixWord ++ tailWord_6563347).sum := by decide
  have hdescent : baseEnd_6563347 < baseStart_6563347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563398 : List Nat := [6, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6563398 : Nat := 118140960795 + 6563398 * 2 ^ 59
def prefixEnd_6563398 : Nat := 4983230072969 + 3 ^ 40 * 6563398 * 2
def baseEnd_6563398 : Nat := 3370177900758416908840489

theorem tailTrace_6563398 : CollatzResearch.WordTrace tailWord_6563398 prefixEnd_6563398 3370177900758416908840489 := by
  unfold tailWord_6563398
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480837233623045624405839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 159591194317291639987324565 7480837233623045624405839)
  ·
    refine ⟨11221255850434568436608759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7480837233623045624405839 11221255850434568436608759)
    ·
      refine ⟨16831883775651852654913139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11221255850434568436608759 16831883775651852654913139)
      ·
        refine ⟨25247825663477778982369709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831883775651852654913139 25247825663477778982369709)
        ·
          refine ⟨9467934623804167118388641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25247825663477778982369709 9467934623804167118388641)
          ·
            refine ⟨7100950967853125338791481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9467934623804167118388641 7100950967853125338791481)
            ·
              refine ⟨5325713225889844004093611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7100950967853125338791481 5325713225889844004093611)
              ·
                refine ⟨7988569838834766006140417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5325713225889844004093611 7988569838834766006140417)
                ·
                  refine ⟨5991427379126074504605313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7988569838834766006140417 5991427379126074504605313)
                  ·
                    refine ⟨4493570534344555878453985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5991427379126074504605313 4493570534344555878453985)
                    ·
                      refine ⟨3370177900758416908840489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493570534344555878453985 3370177900758416908840489)
                      ·
                        rfl

theorem cell23_6563398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6563398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563398 prefixEnd_6563398 := by exact prefixLift 6563398
  have htrace : WordTrace (prefixWord ++ tailWord_6563398) baseStart_6563398 baseEnd_6563398 := by
    simpa [prefixWord, tailWord_6563398, baseEnd_6563398] using wordTrace_append hprefix tailTrace_6563398
  have hstable : (prefixWord ++ tailWord_6563398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563398).length < 2 ^ (prefixWord ++ tailWord_6563398).sum := by decide
  have hdescent : baseEnd_6563398 < baseStart_6563398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563420 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_6563420 : Nat := 118140960795 + 6563420 * 2 ^ 59
def prefixEnd_6563420 : Nat := 4983230072969 + 3 ^ 40 * 6563420 * 2
def baseEnd_6563420 : Nat := 3370189197332815822765387

theorem tailTrace_6563420 : CollatzResearch.WordTrace tailWord_6563420 prefixEnd_6563420 3370189197332815822765387 := by
  unfold tailWord_6563420
  simp only [CollatzResearch.WordTrace]
  refine ⟨119693796940928878869143857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159591729254571838492191809 119693796940928878869143857)
  ·
    refine ⟨89770347705696659151857893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119693796940928878869143857 89770347705696659151857893)
    ·
      refine ⟨16831940194818123590973355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89770347705696659151857893 16831940194818123590973355)
      ·
        refine ⟨25247910292227185386460033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16831940194818123590973355 25247910292227185386460033)
        ·
          refine ⟨18935932719170389039845025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25247910292227185386460033 18935932719170389039845025)
          ·
            refine ⟨14201949539377791779883769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18935932719170389039845025 14201949539377791779883769)
            ·
              refine ⟨10651462154533343834912827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14201949539377791779883769 10651462154533343834912827)
              ·
                refine ⟨15977193231800015752369241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10651462154533343834912827 15977193231800015752369241)
                ·
                  refine ⟨11982894923850011814276931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15977193231800015752369241 11982894923850011814276931)
                  ·
                    refine ⟨17974342385775017721415397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11982894923850011814276931 17974342385775017721415397)
                    ·
                      refine ⟨3370189197332815822765387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17974342385775017721415397 3370189197332815822765387)
                      ·
                        rfl

theorem cell23_6563420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_6563420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563420 prefixEnd_6563420 := by exact prefixLift 6563420
  have htrace : WordTrace (prefixWord ++ tailWord_6563420) baseStart_6563420 baseEnd_6563420 := by
    simpa [prefixWord, tailWord_6563420, baseEnd_6563420] using wordTrace_append hprefix tailTrace_6563420
  have hstable : (prefixWord ++ tailWord_6563420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563420).length < 2 ^ (prefixWord ++ tailWord_6563420).sum := by decide
  have hdescent : baseEnd_6563420 < baseStart_6563420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563456 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 5, 5]
def baseStart_6563456 : Nat := 118140960795 + 6563456 * 2 ^ 59
def prefixEnd_6563456 : Nat := 4983230072969 + 3 ^ 40 * 6563456 * 2
def baseEnd_6563456 : Nat := 1123402560878792560638407

theorem tailTrace_6563456 : CollatzResearch.WordTrace tailWord_6563456 prefixEnd_6563456 1123402560878792560638407 := by
  unfold tailWord_6563456
  simp only [CollatzResearch.WordTrace]
  refine ⟨119694453454863667943299111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159592604606484890591065481 119694453454863667943299111)
  ·
    refine ⟨179541680182295501914948667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119694453454863667943299111 179541680182295501914948667)
    ·
      refine ⟨269312520273443252872423001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179541680182295501914948667 269312520273443252872423001)
      ·
        refine ⟨201984390205082439654317251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269312520273443252872423001 201984390205082439654317251)
        ·
          refine ⟨302976585307623659481475877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201984390205082439654317251 302976585307623659481475877)
          ·
            refine ⟨56808109745179436152776727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302976585307623659481475877 56808109745179436152776727)
            ·
              refine ⟨85212164617769154229165091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56808109745179436152776727 85212164617769154229165091)
              ·
                refine ⟨127818246926653731343747637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85212164617769154229165091 127818246926653731343747637)
                ·
                  refine ⟨11982960649373787313476341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127818246926653731343747637 11982960649373787313476341)
                  ·
                    refine ⟨1123402560878792560638407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11982960649373787313476341 1123402560878792560638407)
                    ·
                      rfl

theorem cell23_6563456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 5, 5].length) (baseStart_6563456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563456 prefixEnd_6563456 := by exact prefixLift 6563456
  have htrace : WordTrace (prefixWord ++ tailWord_6563456) baseStart_6563456 baseEnd_6563456 := by
    simpa [prefixWord, tailWord_6563456, baseEnd_6563456] using wordTrace_append hprefix tailTrace_6563456
  have hstable : (prefixWord ++ tailWord_6563456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563456).length < 2 ^ (prefixWord ++ tailWord_6563456).sum := by decide
  have hdescent : baseEnd_6563456 < baseStart_6563456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563470 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6563470 : Nat := 118140960795 + 6563470 * 2 ^ 59
def prefixEnd_6563470 : Nat := 4983230072969 + 3 ^ 40 * 6563470 * 2
def baseEnd_6563470 : Nat := 3370214871365540627140157

theorem tailTrace_6563470 : CollatzResearch.WordTrace tailWord_6563470 prefixEnd_6563470 3370214871365540627140157 := by
  unfold tailWord_6563470
  simp only [CollatzResearch.WordTrace]
  refine ⟨29923677191459577034700983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159592945021117744185071909 29923677191459577034700983)
  ·
    refine ⟨44885515787189365552051475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29923677191459577034700983 44885515787189365552051475)
    ·
      refine ⟨67328273680784048328077213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44885515787189365552051475 67328273680784048328077213)
      ·
        refine ⟨25248102630294018123028955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67328273680784048328077213 25248102630294018123028955)
        ·
          refine ⟨37872153945441027184543433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25248102630294018123028955 37872153945441027184543433)
          ·
            refine ⟨28404115459080770388407575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37872153945441027184543433 28404115459080770388407575)
            ·
              refine ⟨42606173188621155582611363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28404115459080770388407575 42606173188621155582611363)
              ·
                refine ⟨63909259782931733373917045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42606173188621155582611363 63909259782931733373917045)
                ·
                  refine ⟨5991493104649850003804723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63909259782931733373917045 5991493104649850003804723)
                  ·
                    refine ⟨8987239656974775005707085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5991493104649850003804723 8987239656974775005707085)
                    ·
                      refine ⟨3370214871365540627140157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8987239656974775005707085 3370214871365540627140157)
                      ·
                        rfl

theorem cell23_6563470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6563470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563470 prefixEnd_6563470 := by exact prefixLift 6563470
  have htrace : WordTrace (prefixWord ++ tailWord_6563470) baseStart_6563470 baseEnd_6563470 := by
    simpa [prefixWord, tailWord_6563470, baseEnd_6563470] using wordTrace_append hprefix tailTrace_6563470
  have hstable : (prefixWord ++ tailWord_6563470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563470).length < 2 ^ (prefixWord ++ tailWord_6563470).sum := by decide
  have hdescent : baseEnd_6563470 < baseStart_6563470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563474 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_6563474 : Nat := 118140960795 + 6563474 * 2 ^ 59
def prefixEnd_6563474 : Nat := 4983230072969 + 3 ^ 40 * 6563474 * 2
def baseEnd_6563474 : Nat := 3370216925288158611490139

theorem tailTrace_6563474 : CollatzResearch.WordTrace tailWord_6563474 prefixEnd_6563474 3370216925288158611490139 := by
  unfold tailWord_6563474
  simp only [CollatzResearch.WordTrace]
  refine ⟨59847390855915531240188369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159593042282441416640502317 59847390855915531240188369)
  ·
    refine ⟨44885543141936648430141277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59847390855915531240188369 44885543141936648430141277)
    ·
      refine ⟨16832078678226243161302979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44885543141936648430141277 16832078678226243161302979)
      ·
        refine ⟨25248118017339364741954469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16832078678226243161302979 25248118017339364741954469)
        ·
          refine ⟨4734022128251130889116463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25248118017339364741954469 4734022128251130889116463)
          ·
            refine ⟨7101033192376696333674695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734022128251130889116463 7101033192376696333674695)
            ·
              refine ⟨10651549788565044500512043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101033192376696333674695 10651549788565044500512043)
              ·
                refine ⟨15977324682847566750768065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10651549788565044500512043 15977324682847566750768065)
                ·
                  refine ⟨11982993512135675063076049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15977324682847566750768065 11982993512135675063076049)
                  ·
                    refine ⟨8987245134101756297307037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11982993512135675063076049 8987245134101756297307037)
                    ·
                      refine ⟨3370216925288158611490139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8987245134101756297307037 3370216925288158611490139)
                      ·
                        rfl

theorem cell23_6563474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_6563474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563474 prefixEnd_6563474 := by exact prefixLift 6563474
  have htrace : WordTrace (prefixWord ++ tailWord_6563474) baseStart_6563474 baseEnd_6563474 := by
    simpa [prefixWord, tailWord_6563474, baseEnd_6563474] using wordTrace_append hprefix tailTrace_6563474
  have hstable : (prefixWord ++ tailWord_6563474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563474).length < 2 ^ (prefixWord ++ tailWord_6563474).sum := by decide
  have hdescent : baseEnd_6563474 < baseStart_6563474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563480 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 1, 5, 2]
def baseStart_6563480 : Nat := 118140960795 + 6563480 * 2 ^ 59
def prefixEnd_6563480 : Nat := 4983230072969 + 3 ^ 40 * 6563480 * 2
def baseEnd_6563480 : Nat := 3370220006172085588015111

theorem tailTrace_6563480 : CollatzResearch.WordTrace tailWord_6563480 prefixEnd_6563480 3370220006172085588015111 := by
  unfold tailWord_6563480
  simp only [CollatzResearch.WordTrace]
  refine ⟨119694891130820193992735947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159593188174426925323647929 119694891130820193992735947)
  ·
    refine ⟨179542336696230290989103921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119694891130820193992735947 179542336696230290989103921)
    ·
      refine ⟨134656752522172718241827941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179542336696230290989103921 134656752522172718241827941)
      ·
        refine ⟨25248141097907384670342739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134656752522172718241827941 25248141097907384670342739)
        ·
          refine ⟨37872211646861077005514109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25248141097907384670342739 37872211646861077005514109)
          ·
            refine ⟨14202079367572903877067791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37872211646861077005514109 14202079367572903877067791)
            ·
              refine ⟨21303119051359355815601687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14202079367572903877067791 21303119051359355815601687)
              ·
                refine ⟨31954678577039033723402531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21303119051359355815601687 31954678577039033723402531)
                ·
                  refine ⟨47932017865558550585103797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31954678577039033723402531 47932017865558550585103797)
                  ·
                    refine ⟨4493626674896114117353481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47932017865558550585103797 4493626674896114117353481)
                    ·
                      refine ⟨3370220006172085588015111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493626674896114117353481 3370220006172085588015111)
                      ·
                        rfl

theorem cell23_6563480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_6563480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563480 prefixEnd_6563480 := by exact prefixLift 6563480
  have htrace : WordTrace (prefixWord ++ tailWord_6563480) baseStart_6563480 baseEnd_6563480 := by
    simpa [prefixWord, tailWord_6563480, baseEnd_6563480] using wordTrace_append hprefix tailTrace_6563480
  have hstable : (prefixWord ++ tailWord_6563480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563480).length < 2 ^ (prefixWord ++ tailWord_6563480).sum := by decide
  have hdescent : baseEnd_6563480 < baseStart_6563480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563503 : List Nat := [1, 1, 2, 1, 2, 4, 3, 1, 4, 4]
def baseStart_6563503 : Nat := 118140960795 + 6563503 * 2 ^ 59
def prefixEnd_6563503 : Nat := 4983230072969 + 3 ^ 40 * 6563503 * 2
def baseEnd_6563503 : Nat := 1123410605409046332675835

theorem tailTrace_6563503 : CollatzResearch.WordTrace tailWord_6563503 prefixEnd_6563503 1123410605409046332675835 := by
  unfold tailWord_6563503
  simp only [CollatzResearch.WordTrace]
  refine ⟨239390621140557062913559163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159593747427038041942372775 239390621140557062913559163)
  ·
    refine ⟨359085931710835594370338745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239390621140557062913559163 359085931710835594370338745)
    ·
      refine ⟨269314448783126695777754059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359085931710835594370338745 269314448783126695777754059)
      ·
        refine ⟨403971673174690043666631089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269314448783126695777754059 403971673174690043666631089)
        ·
          refine ⟨302978754881017532749973317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403971673174690043666631089 302978754881017532749973317)
          ·
            refine ⟨56808516540190787390619997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 302978754881017532749973317 56808516540190787390619997)
            ·
              refine ⟨21303193702571545271482499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56808516540190787390619997 21303193702571545271482499)
              ·
                refine ⟨31954790553857317907223749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21303193702571545271482499 31954790553857317907223749)
                ·
                  refine ⟨5991523228848247107604453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31954790553857317907223749 5991523228848247107604453)
                  ·
                    refine ⟨1123410605409046332675835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5991523228848247107604453 1123410605409046332675835)
                    ·
                      rfl

theorem cell23_6563503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 4, 4].length) (baseStart_6563503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563503 prefixEnd_6563503 := by exact prefixLift 6563503
  have htrace : WordTrace (prefixWord ++ tailWord_6563503) baseStart_6563503 baseEnd_6563503 := by
    simpa [prefixWord, tailWord_6563503, baseEnd_6563503] using wordTrace_append hprefix tailTrace_6563503
  have hstable : (prefixWord ++ tailWord_6563503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563503).length < 2 ^ (prefixWord ++ tailWord_6563503).sum := by decide
  have hdescent : baseEnd_6563503 < baseStart_6563503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563513 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6563513 : Nat := 118140960795 + 6563513 * 2 ^ 59
def prefixEnd_6563513 : Nat := 4983230072969 + 3 ^ 40 * 6563513 * 2
def baseEnd_6563513 : Nat := 3370236951033683958902459

theorem tailTrace_6563513 : CollatzResearch.WordTrace tailWord_6563513 prefixEnd_6563513 3370236951033683958902459 := by
  unfold tailWord_6563513
  simp only [CollatzResearch.WordTrace]
  refine ⟨239390985870520834621423193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159593990580347223080948795 239390985870520834621423193)
  ·
    refine ⟨179543239402890625966067395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239390985870520834621423193 179543239402890625966067395)
    ·
      refine ⟨269314859104335938949101093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179543239402890625966067395 269314859104335938949101093)
      ·
        refine ⟨50496536082062988552956455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269314859104335938949101093 50496536082062988552956455)
        ·
          refine ⟨75744804123094482829434683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50496536082062988552956455 75744804123094482829434683)
          ·
            refine ⟨113617206184641724244152025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75744804123094482829434683 113617206184641724244152025)
            ·
              refine ⟨85212904638481293183114019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113617206184641724244152025 85212904638481293183114019)
              ·
                refine ⟨127819356957721939774671029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85212904638481293183114019 127819356957721939774671029)
                ·
                  refine ⟨11983064714786431853875409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 127819356957721939774671029 11983064714786431853875409)
                  ·
                    refine ⟨8987298536089823890406557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11983064714786431853875409 8987298536089823890406557)
                    ·
                      refine ⟨3370236951033683958902459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8987298536089823890406557 3370236951033683958902459)
                      ·
                        rfl

theorem cell23_6563513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6563513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563513 prefixEnd_6563513 := by exact prefixLift 6563513
  have htrace : WordTrace (prefixWord ++ tailWord_6563513) baseStart_6563513 baseEnd_6563513 := by
    simpa [prefixWord, tailWord_6563513, baseEnd_6563513] using wordTrace_append hprefix tailTrace_6563513
  have hstable : (prefixWord ++ tailWord_6563513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563513).length < 2 ^ (prefixWord ++ tailWord_6563513).sum := by decide
  have hdescent : baseEnd_6563513 < baseStart_6563513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563543 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 3]
def baseStart_6563543 : Nat := 118140960795 + 6563543 * 2 ^ 59
def prefixEnd_6563543 : Nat := 4983230072969 + 3 ^ 40 * 6563543 * 2
def baseEnd_6563543 : Nat := 3370252355453318841527321

theorem tailTrace_6563543 : CollatzResearch.WordTrace tailWord_6563543 prefixEnd_6563543 3370252355453318841527321 := by
  unfold tailWord_6563543
  simp only [CollatzResearch.WordTrace]
  refine ⟨239392080060412149745015283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159594720040274766496676855 239392080060412149745015283)
  ·
    refine ⟨359088120090618224617522925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239392080060412149745015283 359088120090618224617522925)
    ·
      refine ⟨134658045033981834231571097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359088120090618224617522925 134658045033981834231571097)
      ·
        refine ⟨100993533775486375673678323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134658045033981834231571097 100993533775486375673678323)
        ·
          refine ⟨151490300663229563510517485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100993533775486375673678323 151490300663229563510517485)
          ·
            refine ⟨56808862748711086316444057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151490300663229563510517485 56808862748711086316444057)
            ·
              refine ⟨42606647061533314737333043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56808862748711086316444057 42606647061533314737333043)
              ·
                refine ⟨63909970592299972105999565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42606647061533314737333043 63909970592299972105999565)
                ·
                  refine ⟨23966238972112489539749837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63909970592299972105999565 23966238972112489539749837)
                  ·
                    refine ⟨8987339614542183577406189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23966238972112489539749837 8987339614542183577406189)
                    ·
                      refine ⟨3370252355453318841527321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8987339614542183577406189 3370252355453318841527321)
                      ·
                        rfl

theorem cell23_6563543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_6563543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563543 prefixEnd_6563543 := by exact prefixLift 6563543
  have htrace : WordTrace (prefixWord ++ tailWord_6563543) baseStart_6563543 baseEnd_6563543 := by
    simpa [prefixWord, tailWord_6563543, baseEnd_6563543] using wordTrace_append hprefix tailTrace_6563543
  have hstable : (prefixWord ++ tailWord_6563543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563543).length < 2 ^ (prefixWord ++ tailWord_6563543).sum := by decide
  have hdescent : baseEnd_6563543 < baseStart_6563543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563587 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 1, 3, 2]
def baseStart_6563587 : Nat := 118140960795 + 6563587 * 2 ^ 59
def prefixEnd_6563587 : Nat := 4983230072969 + 3 ^ 40 * 6563587 * 2
def baseEnd_6563587 : Nat := 3370274948602116669377119

theorem tailTrace_6563587 : CollatzResearch.WordTrace tailWord_6563587 prefixEnd_6563587 3370274948602116669377119 := by
  unfold tailWord_6563587
  simp only [CollatzResearch.WordTrace]
  refine ⟨239393684872252745259617015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159595789914835163506411343 239393684872252745259617015)
  ·
    refine ⟨359090527308379117889425523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239393684872252745259617015 359090527308379117889425523)
    ·
      refine ⟨538635790962568676834138285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359090527308379117889425523 538635790962568676834138285)
      ·
        refine ⟨201988421610963253812801857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538635790962568676834138285 201988421610963253812801857)
        ·
          refine ⟨151491316208222440359601393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201988421610963253812801857 151491316208222440359601393)
          ·
            refine ⟨113618487156166830269701045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151491316208222440359601393 113618487156166830269701045)
            ·
              refine ⟨10651733170890640337784473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113618487156166830269701045 10651733170890640337784473)
              ·
                refine ⟨7988799878167980253338355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10651733170890640337784473 7988799878167980253338355)
                ·
                  refine ⟨11983199817251970380007533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7988799878167980253338355 11983199817251970380007533)
                  ·
                    refine ⟨4493699931469488892502825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11983199817251970380007533 4493699931469488892502825)
                    ·
                      refine ⟨3370274948602116669377119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493699931469488892502825 3370274948602116669377119)
                      ·
                        rfl

theorem cell23_6563587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_6563587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563587 prefixEnd_6563587 := by exact prefixLift 6563587
  have htrace : WordTrace (prefixWord ++ tailWord_6563587) baseStart_6563587 baseEnd_6563587 := by
    simpa [prefixWord, tailWord_6563587, baseEnd_6563587] using wordTrace_append hprefix tailTrace_6563587
  have hstable : (prefixWord ++ tailWord_6563587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563587).length < 2 ^ (prefixWord ++ tailWord_6563587).sum := by decide
  have hdescent : baseEnd_6563587 < baseStart_6563587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563620 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_6563620 : Nat := 118140960795 + 6563620 * 2 ^ 59
def prefixEnd_6563620 : Nat := 4983230072969 + 3 ^ 40 * 6563620 * 2
def baseEnd_6563620 : Nat := 3370291893463715040264467

theorem tailTrace_6563620 : CollatzResearch.WordTrace tailWord_6563620 prefixEnd_6563620 3370291893463715040264467 := by
  unfold tailWord_6563620
  simp only [CollatzResearch.WordTrace]
  refine ⟨119697444240566595947784157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159596592320755461263712209 119697444240566595947784157)
  ·
    refine ⟨44886541590212473480419059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119697444240566595947784157 44886541590212473480419059)
    ·
      refine ⟨67329812385318710220628589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44886541590212473480419059 67329812385318710220628589)
      ·
        refine ⟨25248679644494516332735721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67329812385318710220628589 25248679644494516332735721)
        ·
          refine ⟨18936509733370887249551791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25248679644494516332735721 18936509733370887249551791)
          ·
            refine ⟨28404764600056330874327687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18936509733370887249551791 28404764600056330874327687)
            ·
              refine ⟨42607146900084496311491531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28404764600056330874327687 42607146900084496311491531)
              ·
                refine ⟨63910720350126744467237297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42607146900084496311491531 63910720350126744467237297)
                ·
                  refine ⟨47933040262595058350427973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63910720350126744467237297 47933040262595058350427973)
                  ·
                    refine ⟨8987445049236573440705245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47933040262595058350427973 8987445049236573440705245)
                    ·
                      refine ⟨3370291893463715040264467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8987445049236573440705245 3370291893463715040264467)
                      ·
                        rfl

theorem cell23_6563620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_6563620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563620 prefixEnd_6563620 := by exact prefixLift 6563620
  have htrace : WordTrace (prefixWord ++ tailWord_6563620) baseStart_6563620 baseEnd_6563620 := by
    simpa [prefixWord, tailWord_6563620, baseEnd_6563620] using wordTrace_append hprefix tailTrace_6563620
  have hstable : (prefixWord ++ tailWord_6563620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563620).length < 2 ^ (prefixWord ++ tailWord_6563620).sum := by decide
  have hdescent : baseEnd_6563620 < baseStart_6563620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563634 : List Nat := [3, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2]
def baseStart_6563634 : Nat := 118140960795 + 6563634 * 2 ^ 59
def prefixEnd_6563634 : Nat := 4983230072969 + 3 ^ 40 * 6563634 * 2
def baseEnd_6563634 : Nat := 3370299082192877985489403

theorem tailTrace_6563634 : CollatzResearch.WordTrace tailWord_6563634 prefixEnd_6563634 3370299082192877985489403 := by
  unfold tailWord_6563634
  simp only [CollatzResearch.WordTrace]
  refine ⟨59848849775770618071644489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159596932735388314857718637 59848849775770618071644489)
  ·
    refine ⟨44886637331827963553733367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59848849775770618071644489 44886637331827963553733367)
    ·
      refine ⟨67329955997741945330600051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44886637331827963553733367 67329955997741945330600051)
      ·
        refine ⟨100994933996612917995900077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67329955997741945330600051 100994933996612917995900077)
        ·
          refine ⟨37873100248729844248462529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100994933996612917995900077 37873100248729844248462529)
          ·
            refine ⟨28404825186547383186346897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37873100248729844248462529 28404825186547383186346897)
            ·
              refine ⟨21303618889910537389760173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28404825186547383186346897 21303618889910537389760173)
              ·
                refine ⟨7988857083716451521160065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21303618889910537389760173 7988857083716451521160065)
                ·
                  refine ⟨5991642812787338640870049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7988857083716451521160065 5991642812787338640870049)
                  ·
                    refine ⟨4493732109590503980652537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5991642812787338640870049 4493732109590503980652537)
                    ·
                      refine ⟨3370299082192877985489403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493732109590503980652537 3370299082192877985489403)
                      ·
                        rfl

theorem cell23_6563634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_6563634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563634 prefixEnd_6563634 := by exact prefixLift 6563634
  have htrace : WordTrace (prefixWord ++ tailWord_6563634) baseStart_6563634 baseEnd_6563634 := by
    simpa [prefixWord, tailWord_6563634, baseEnd_6563634] using wordTrace_append hprefix tailTrace_6563634
  have hstable : (prefixWord ++ tailWord_6563634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563634).length < 2 ^ (prefixWord ++ tailWord_6563634).sum := by decide
  have hdescent : baseEnd_6563634 < baseStart_6563634 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563653 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 1, 7]
def baseStart_6563653 : Nat := 118140960795 + 6563653 * 2 ^ 59
def prefixEnd_6563653 : Nat := 4983230072969 + 3 ^ 40 * 6563653 * 2
def baseEnd_6563653 : Nat := 1123436279441771137050605

theorem tailTrace_6563653 : CollatzResearch.WordTrace tailWord_6563653 prefixEnd_6563653 1123436279441771137050605 := by
  unfold tailWord_6563653
  simp only [CollatzResearch.WordTrace]
  refine ⟨239396092090013638531519613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159597394726675759021013075 239396092090013638531519613)
  ·
    refine ⟨89773534533755114449319855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239396092090013638531519613 89773534533755114449319855)
    ·
      refine ⟨134660301800632671673979783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89773534533755114449319855 134660301800632671673979783)
      ·
        refine ⟨201990452700949007510969675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134660301800632671673979783 201990452700949007510969675)
        ·
          refine ⟨302985679051423511266454513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201990452700949007510969675 302985679051423511266454513)
          ·
            refine ⟨227239259288567633449840885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302985679051423511266454513 227239259288567633449840885)
            ·
              refine ⟨21303680558303215635922583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227239259288567633449840885 21303680558303215635922583)
              ·
                refine ⟨31955520837454823453883875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21303680558303215635922583 31955520837454823453883875)
                ·
                  refine ⟨47933281256182235180825813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31955520837454823453883875 47933281256182235180825813)
                  ·
                    refine ⟨1123436279441771137050605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47933281256182235180825813 1123436279441771137050605)
                    ·
                      rfl

theorem cell23_6563653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 1, 7].length) (baseStart_6563653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563653 prefixEnd_6563653 := by exact prefixLift 6563653
  have htrace : WordTrace (prefixWord ++ tailWord_6563653) baseStart_6563653 baseEnd_6563653 := by
    simpa [prefixWord, tailWord_6563653, baseEnd_6563653] using wordTrace_append hprefix tailTrace_6563653
  have hstable : (prefixWord ++ tailWord_6563653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563653).length < 2 ^ (prefixWord ++ tailWord_6563653).sum := by decide
  have hdescent : baseEnd_6563653 < baseStart_6563653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563753 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 7]
def baseStart_6563753 : Nat := 118140960795 + 6563753 * 2 ^ 59
def prefixEnd_6563753 : Nat := 4983230072969 + 3 ^ 40 * 6563753 * 2
def baseEnd_6563753 : Nat := 3370360186390763019901355

theorem tailTrace_6563753 : CollatzResearch.WordTrace tailWord_6563753 prefixEnd_6563753 3370360186390763019901355 := by
  unfold tailWord_6563753
  simp only [CollatzResearch.WordTrace]
  refine ⟨239399739389651355610159913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159599826259767570406773275 239399739389651355610159913)
  ·
    refine ⟨179549804542238516707619935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239399739389651355610159913 179549804542238516707619935)
    ·
      refine ⟨269324706813357775061429903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179549804542238516707619935 269324706813357775061429903)
      ·
        refine ⟨403987060220036662592144855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269324706813357775061429903 403987060220036662592144855)
        ·
          refine ⟨605980590330054993888217283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403987060220036662592144855 605980590330054993888217283)
          ·
            refine ⟨908970885495082490832325925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605980590330054993888217283 908970885495082490832325925)
            ·
              refine ⟨170432041030327967031061111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 908970885495082490832325925 170432041030327967031061111)
              ·
                refine ⟨255648061545491950546591667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170432041030327967031061111 255648061545491950546591667)
                ·
                  refine ⟨383472092318237925819887501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255648061545491950546591667 383472092318237925819887501)
                  ·
                    refine ⟨143802034619339222182457813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383472092318237925819887501 143802034619339222182457813)
                    ·
                      refine ⟨3370360186390763019901355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143802034619339222182457813 3370360186390763019901355)
                      ·
                        rfl

theorem cell23_6563753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 3, 7].length) (baseStart_6563753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563753 prefixEnd_6563753 := by exact prefixLift 6563753
  have htrace : WordTrace (prefixWord ++ tailWord_6563753) baseStart_6563753 baseEnd_6563753 := by
    simpa [prefixWord, tailWord_6563753, baseEnd_6563753] using wordTrace_append hprefix tailTrace_6563753
  have hstable : (prefixWord ++ tailWord_6563753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563753).length < 2 ^ (prefixWord ++ tailWord_6563753).sum := by decide
  have hdescent : baseEnd_6563753 < baseStart_6563753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563758 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6563758 : Nat := 118140960795 + 6563758 * 2 ^ 59
def prefixEnd_6563758 : Nat := 4983230072969 + 3 ^ 40 * 6563758 * 2
def baseEnd_6563758 : Nat := 3370362753794035500338833

theorem tailTrace_6563758 : CollatzResearch.WordTrace tailWord_6563758 prefixEnd_6563758 3370362753794035500338833 := by
  unfold tailWord_6563758
  simp only [CollatzResearch.WordTrace]
  refine ⟨29924990219329155183011491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159599947836422160976061285 29924990219329155183011491)
  ·
    refine ⟨44887485328993732774517237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29924990219329155183011491 44887485328993732774517237)
    ·
      refine ⟨4208201749593162447610991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44887485328993732774517237 4208201749593162447610991)
      ·
        refine ⟨6312302624389743671416487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208201749593162447610991 6312302624389743671416487)
        ·
          refine ⟨9468453936584615507124731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6312302624389743671416487 9468453936584615507124731)
          ·
            refine ⟨14202680904876923260687097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9468453936584615507124731 14202680904876923260687097)
            ·
              refine ⟨10652010678657692445515323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14202680904876923260687097 10652010678657692445515323)
              ·
                refine ⟨15978016017986538668272985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652010678657692445515323 15978016017986538668272985)
                ·
                  refine ⟨11983512013489904001204739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15978016017986538668272985 11983512013489904001204739)
                  ·
                    refine ⟨17975268020234856001807109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11983512013489904001204739 17975268020234856001807109)
                    ·
                      refine ⟨3370362753794035500338833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17975268020234856001807109 3370362753794035500338833)
                      ·
                        rfl

theorem cell23_6563758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6563758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563758 prefixEnd_6563758 := by exact prefixLift 6563758
  have htrace : WordTrace (prefixWord ++ tailWord_6563758) baseStart_6563758 baseEnd_6563758 := by
    simpa [prefixWord, tailWord_6563758, baseEnd_6563758] using wordTrace_append hprefix tailTrace_6563758
  have hstable : (prefixWord ++ tailWord_6563758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563758).length < 2 ^ (prefixWord ++ tailWord_6563758).sum := by decide
  have hdescent : baseEnd_6563758 < baseStart_6563758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563784 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_6563784 : Nat := 118140960795 + 6563784 * 2 ^ 59
def prefixEnd_6563784 : Nat := 4983230072969 + 3 ^ 40 * 6563784 * 2
def baseEnd_6563784 : Nat := 3370376104291052398613713

theorem tailTrace_6563784 : CollatzResearch.WordTrace tailWord_6563784 prefixEnd_6563784 3370376104291052398613713 := by
  unfold tailWord_6563784
  simp only [CollatzResearch.WordTrace]
  refine ⟨119700435026269523952269203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159600580035026031936358937 119700435026269523952269203)
  ·
    refine ⟨179550652539404285928403805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119700435026269523952269203 179550652539404285928403805)
    ·
      refine ⟨67331494702276607223151427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179550652539404285928403805 67331494702276607223151427)
      ·
        refine ⟨100997242053414910834727141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67331494702276607223151427 100997242053414910834727141)
        ·
          refine ⟨18936982885015295781511339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100997242053414910834727141 18936982885015295781511339)
          ·
            refine ⟨28405474327522943672267009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18936982885015295781511339 28405474327522943672267009)
            ·
              refine ⟨21304105745642207754200257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28405474327522943672267009 21304105745642207754200257)
              ·
                refine ⟨15978079309231655815650193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21304105745642207754200257 15978079309231655815650193)
                ·
                  refine ⟨11983559481923741861737645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15978079309231655815650193 11983559481923741861737645)
                  ·
                    refine ⟨4493834805721403198151617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11983559481923741861737645 4493834805721403198151617)
                    ·
                      refine ⟨3370376104291052398613713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493834805721403198151617 3370376104291052398613713)
                      ·
                        rfl

theorem cell23_6563784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_6563784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563784 prefixEnd_6563784 := by exact prefixLift 6563784
  have htrace : WordTrace (prefixWord ++ tailWord_6563784) baseStart_6563784 baseEnd_6563784 := by
    simpa [prefixWord, tailWord_6563784, baseEnd_6563784] using wordTrace_append hprefix tailTrace_6563784
  have hstable : (prefixWord ++ tailWord_6563784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563784).length < 2 ^ (prefixWord ++ tailWord_6563784).sum := by decide
  have hdescent : baseEnd_6563784 < baseStart_6563784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563790 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_6563790 : Nat := 118140960795 + 6563790 * 2 ^ 59
def prefixEnd_6563790 : Nat := 4983230072969 + 3 ^ 40 * 6563790 * 2
def baseEnd_6563790 : Nat := 1123459728391659791712895

theorem tailTrace_6563790 : CollatzResearch.WordTrace tailWord_6563790 prefixEnd_6563790 1123459728391659791712895 := by
  unfold tailWord_6563790
  simp only [CollatzResearch.WordTrace]
  refine ⟨29925136111314663866157103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159600725927011540619504549 29925136111314663866157103)
  ·
    refine ⟨44887704166971995799235655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29925136111314663866157103 44887704166971995799235655)
    ·
      refine ⟨67331556250457993698853483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44887704166971995799235655 67331556250457993698853483)
      ·
        refine ⟨100997334375686990548280225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67331556250457993698853483 100997334375686990548280225)
        ·
          refine ⟨75748000781765242911210169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100997334375686990548280225 75748000781765242911210169)
          ·
            refine ⟨56811000586323932183407627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75748000781765242911210169 56811000586323932183407627)
            ·
              refine ⟨85216500879485898275111441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56811000586323932183407627 85216500879485898275111441)
              ·
                refine ⟨63912375659614423706333581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85216500879485898275111441 63912375659614423706333581)
                ·
                  refine ⟨23967140872355408889875093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63912375659614423706333581 23967140872355408889875093)
                  ·
                    refine ⟨1123459728391659791712895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23967140872355408889875093 1123459728391659791712895)
                    ·
                      rfl

theorem cell23_6563790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_6563790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563790 prefixEnd_6563790 := by exact prefixLift 6563790
  have htrace : WordTrace (prefixWord ++ tailWord_6563790) baseStart_6563790 baseEnd_6563790 := by
    simpa [prefixWord, tailWord_6563790, baseEnd_6563790] using wordTrace_append hprefix tailTrace_6563790
  have hstable : (prefixWord ++ tailWord_6563790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563790).length < 2 ^ (prefixWord ++ tailWord_6563790).sum := by decide
  have hdescent : baseEnd_6563790 < baseStart_6563790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563797 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6563797 : Nat := 118140960795 + 6563797 * 2 ^ 59
def prefixEnd_6563797 : Nat := 4983230072969 + 3 ^ 40 * 6563797 * 2
def baseEnd_6563797 : Nat := 3370382779539560847751153

theorem tailTrace_6563797 : CollatzResearch.WordTrace tailWord_6563797 prefixEnd_6563797 3370382779539560847751153 := by
  unfold tailWord_6563797
  simp only [CollatzResearch.WordTrace]
  refine ⟨239401344201491951124761645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159600896134327967416507763 239401344201491951124761645)
  ·
    refine ⟨89775504075559481671785617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239401344201491951124761645 89775504075559481671785617)
    ·
      refine ⟨67331628056669611253839213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89775504075559481671785617 67331628056669611253839213)
      ·
        refine ⟨25249360521251104220189705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67331628056669611253839213 25249360521251104220189705)
        ·
          refine ⟨18937020390938328165142279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25249360521251104220189705 18937020390938328165142279)
          ·
            refine ⟨28405530586407492247713419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18937020390938328165142279 28405530586407492247713419)
            ·
              refine ⟨42608295879611238371570129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28405530586407492247713419 42608295879611238371570129)
              ·
                refine ⟨31956221909708428778677597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42608295879611238371570129 31956221909708428778677597)
                ·
                  refine ⟨11983583216140660792004099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31956221909708428778677597 11983583216140660792004099)
                  ·
                    refine ⟨17975374824210991188006149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11983583216140660792004099 17975374824210991188006149)
                    ·
                      refine ⟨3370382779539560847751153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17975374824210991188006149 3370382779539560847751153)
                      ·
                        rfl

theorem cell23_6563797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6563797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563797 prefixEnd_6563797 := by exact prefixLift 6563797
  have htrace : WordTrace (prefixWord ++ tailWord_6563797) baseStart_6563797 baseEnd_6563797 := by
    simpa [prefixWord, tailWord_6563797, baseEnd_6563797] using wordTrace_append hprefix tailTrace_6563797
  have hstable : (prefixWord ++ tailWord_6563797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563797).length < 2 ^ (prefixWord ++ tailWord_6563797).sum := by decide
  have hdescent : baseEnd_6563797 < baseStart_6563797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563800 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 3, 1, 5]
def baseStart_6563800 : Nat := 118140960795 + 6563800 * 2 ^ 59
def prefixEnd_6563800 : Nat := 4983230072969 + 3 ^ 40 * 6563800 * 2
def baseEnd_6563800 : Nat := 3370384319981524336013639

theorem tailTrace_6563800 : CollatzResearch.WordTrace tailWord_6563800 prefixEnd_6563800 3370384319981524336013639 := by
  unfold tailWord_6563800
  simp only [CollatzResearch.WordTrace]
  refine ⟨119700726810240541318560427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159600969080320721758080569 119700726810240541318560427)
  ·
    refine ⟨179551090215360811977840641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119700726810240541318560427 179551090215360811977840641)
    ·
      refine ⟨134663317661520608983380481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179551090215360811977840641 134663317661520608983380481)
      ·
        refine ⟨100997488246140456737535361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134663317661520608983380481 100997488246140456737535361)
        ·
          refine ⟨75748116184605342553151521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100997488246140456737535361 75748116184605342553151521)
          ·
            refine ⟨56811087138454006914863641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75748116184605342553151521 56811087138454006914863641)
            ·
              refine ⟨42608315353840505186147731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56811087138454006914863641 42608315353840505186147731)
              ·
                refine ⟨63912473030760757779221597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42608315353840505186147731 63912473030760757779221597)
                ·
                  refine ⟨23967177386535284167208099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63912473030760757779221597 23967177386535284167208099)
                  ·
                    refine ⟨35950766079802926250812149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23967177386535284167208099 35950766079802926250812149)
                    ·
                      refine ⟨3370384319981524336013639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35950766079802926250812149 3370384319981524336013639)
                      ·
                        rfl

theorem cell23_6563800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_6563800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563800 prefixEnd_6563800 := by exact prefixLift 6563800
  have htrace : WordTrace (prefixWord ++ tailWord_6563800) baseStart_6563800 baseEnd_6563800 := by
    simpa [prefixWord, tailWord_6563800, baseEnd_6563800] using wordTrace_append hprefix tailTrace_6563800
  have hstable : (prefixWord ++ tailWord_6563800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563800).length < 2 ^ (prefixWord ++ tailWord_6563800).sum := by decide
  have hdescent : baseEnd_6563800 < baseStart_6563800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563807 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 1, 6]
def baseStart_6563807 : Nat := 118140960795 + 6563807 * 2 ^ 59
def prefixEnd_6563807 : Nat := 4983230072969 + 3 ^ 40 * 6563807 * 2
def baseEnd_6563807 : Nat := 1123462638115368602875369

theorem tailTrace_6563807 : CollatzResearch.WordTrace tailWord_6563807 prefixEnd_6563807 1123462638115368602875369 := by
  unfold tailWord_6563807
  simp only [CollatzResearch.WordTrace]
  refine ⟨239401708931455722832625675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159601139287637148555083783 239401708931455722832625675)
  ·
    refine ⟨359102563397183584248938513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239401708931455722832625675 359102563397183584248938513)
    ·
      refine ⟨269326922547887688186703885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359102563397183584248938513 269326922547887688186703885)
      ·
        refine ⟨100997595955457883070013957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269326922547887688186703885 100997595955457883070013957)
        ·
          refine ⟨18937049241648353075627617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100997595955457883070013957 18937049241648353075627617)
          ·
            refine ⟨14202786931236264806720713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18937049241648353075627617 14202786931236264806720713)
            ·
              refine ⟨10652090198427198605040535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14202786931236264806720713 10652090198427198605040535)
              ·
                refine ⟨15978135297640797907560803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652090198427198605040535 15978135297640797907560803)
                ·
                  refine ⟨23967202946461196861341205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15978135297640797907560803 23967202946461196861341205)
                  ·
                    refine ⟨1123462638115368602875369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23967202946461196861341205 1123462638115368602875369)
                    ·
                      rfl

theorem cell23_6563807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 1, 6].length) (baseStart_6563807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563807 prefixEnd_6563807 := by exact prefixLift 6563807
  have htrace : WordTrace (prefixWord ++ tailWord_6563807) baseStart_6563807 baseEnd_6563807 := by
    simpa [prefixWord, tailWord_6563807, baseEnd_6563807] using wordTrace_append hprefix tailTrace_6563807
  have hstable : (prefixWord ++ tailWord_6563807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563807).length < 2 ^ (prefixWord ++ tailWord_6563807).sum := by decide
  have hdescent : baseEnd_6563807 < baseStart_6563807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563861 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_6563861 : Nat := 118140960795 + 6563861 * 2 ^ 59
def prefixEnd_6563861 : Nat := 4983230072969 + 3 ^ 40 * 6563861 * 2
def baseEnd_6563861 : Nat := 3370415642301448597350859

theorem tailTrace_6563861 : CollatzResearch.WordTrace tailWord_6563861 prefixEnd_6563861 3370415642301448597350859 := by
  unfold tailWord_6563861
  simp only [CollatzResearch.WordTrace]
  refine ⟨239403678473260090055091437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159602452315506726703394291 239403678473260090055091437)
  ·
    refine ⟨89776379427472533770659289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239403678473260090055091437 89776379427472533770659289)
    ·
      refine ⟨67332284570604400327994467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89776379427472533770659289 67332284570604400327994467)
      ·
        refine ⟨100998426855906600491991701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67332284570604400327994467 100998426855906600491991701)
        ·
          refine ⟨4734301258870621898062111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100998426855906600491991701 4734301258870621898062111)
          ·
            refine ⟨7101451888305932847093167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734301258870621898062111 7101451888305932847093167)
            ·
              refine ⟨10652177832458899270639751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101451888305932847093167 10652177832458899270639751)
              ·
                refine ⟨15978266748688348905959627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652177832458899270639751 15978266748688348905959627)
                ·
                  refine ⟨23967400123032523358939441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15978266748688348905959627 23967400123032523358939441)
                  ·
                    refine ⟨17975550092274392519204581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23967400123032523358939441 17975550092274392519204581)
                    ·
                      refine ⟨3370415642301448597350859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17975550092274392519204581 3370415642301448597350859)
                      ·
                        rfl

theorem cell23_6563861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_6563861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563861 prefixEnd_6563861 := by exact prefixLift 6563861
  have htrace : WordTrace (prefixWord ++ tailWord_6563861) baseStart_6563861 baseEnd_6563861 := by
    simpa [prefixWord, tailWord_6563861, baseEnd_6563861] using wordTrace_append hprefix tailTrace_6563861
  have hstable : (prefixWord ++ tailWord_6563861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563861).length < 2 ^ (prefixWord ++ tailWord_6563861).sum := by decide
  have hdescent : baseEnd_6563861 < baseStart_6563861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563937 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 3]
def baseStart_6563937 : Nat := 118140960795 + 6563937 * 2 ^ 59
def prefixEnd_6563937 : Nat := 4983230072969 + 3 ^ 40 * 6563937 * 2
def baseEnd_6563937 : Nat := 3370454666831190300000509

theorem tailTrace_6563937 : CollatzResearch.WordTrace tailWord_6563937 prefixEnd_6563937 3370454666831190300000509 := by
  unfold tailWord_6563937
  simp only [CollatzResearch.WordTrace]
  refine ⟨239406450420984755034858065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159604300280656503356572043 239406450420984755034858065)
  ·
    refine ⟨179554837815738566276143549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239406450420984755034858065 179554837815738566276143549)
    ·
      refine ⟨67333064180901962353553831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179554837815738566276143549 67333064180901962353553831)
      ·
        refine ⟨100999596271352943530330747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67333064180901962353553831 100999596271352943530330747)
        ·
          refine ⟨151499394407029415295496121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100999596271352943530330747 151499394407029415295496121)
          ·
            refine ⟨113624545805272061471622091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151499394407029415295496121 113624545805272061471622091)
            ·
              refine ⟨170436818707908092207433137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113624545805272061471622091 170436818707908092207433137)
              ·
                refine ⟨127827614030931069155574853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170436818707908092207433137 127827614030931069155574853)
                ·
                  refine ⟨23967677630799575466670285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127827614030931069155574853 23967677630799575466670285)
                  ·
                    refine ⟨8987879111549840800001357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23967677630799575466670285 8987879111549840800001357)
                    ·
                      refine ⟨3370454666831190300000509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8987879111549840800001357 3370454666831190300000509)
                      ·
                        rfl

theorem cell23_6563937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_6563937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563937 prefixEnd_6563937 := by exact prefixLift 6563937
  have htrace : WordTrace (prefixWord ++ tailWord_6563937) baseStart_6563937 baseEnd_6563937 := by
    simpa [prefixWord, tailWord_6563937, baseEnd_6563937] using wordTrace_append hprefix tailTrace_6563937
  have hstable : (prefixWord ++ tailWord_6563937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563937).length < 2 ^ (prefixWord ++ tailWord_6563937).sum := by decide
  have hdescent : baseEnd_6563937 < baseStart_6563937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563938 : List Nat := [3, 3, 2, 2, 2, 1, 1, 2, 1, 4, 2]
def baseStart_6563938 : Nat := 118140960795 + 6563938 * 2 ^ 59
def prefixEnd_6563938 : Nat := 4983230072969 + 3 ^ 40 * 6563938 * 2
def baseEnd_6563938 : Nat := 3370455180311844796088005

theorem tailTrace_6563938 : CollatzResearch.WordTrace tailWord_6563938 prefixEnd_6563938 3370455180311844796088005 := by
  unfold tailWord_6563938
  simp only [CollatzResearch.WordTrace]
  refine ⟨59851621723495283051411117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159604324595987421470429645 59851621723495283051411117)
  ·
    refine ⟨22444358146310731144279169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59851621723495283051411117 22444358146310731144279169)
    ·
      refine ⟨16833268609733048358209377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22444358146310731144279169 16833268609733048358209377)
      ·
        refine ⟨12624951457299786268657033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16833268609733048358209377 12624951457299786268657033)
        ·
          refine ⟨9468713592974839701492775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12624951457299786268657033 9468713592974839701492775)
          ·
            refine ⟨14203070389462259552239163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9468713592974839701492775 14203070389462259552239163)
            ·
              refine ⟨21304605584193389328358745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14203070389462259552239163 21304605584193389328358745)
              ·
                refine ⟨15978454188145041996269059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21304605584193389328358745 15978454188145041996269059)
                ·
                  refine ⟨23967681282217562994403589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15978454188145041996269059 23967681282217562994403589)
                  ·
                    refine ⟨4493940240415793061450673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23967681282217562994403589 4493940240415793061450673)
                    ·
                      refine ⟨3370455180311844796088005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493940240415793061450673 3370455180311844796088005)
                      ·
                        rfl

theorem cell23_6563938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_6563938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563938 prefixEnd_6563938 := by exact prefixLift 6563938
  have htrace : WordTrace (prefixWord ++ tailWord_6563938) baseStart_6563938 baseEnd_6563938 := by
    simpa [prefixWord, tailWord_6563938, baseEnd_6563938] using wordTrace_append hprefix tailTrace_6563938
  have hstable : (prefixWord ++ tailWord_6563938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563938).length < 2 ^ (prefixWord ++ tailWord_6563938).sum := by decide
  have hdescent : baseEnd_6563938 < baseStart_6563938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563961 : List Nat := [1, 2, 1, 3, 4, 1, 4, 2, 5]
def baseStart_6563961 : Nat := 118140960795 + 6563961 * 2 ^ 59
def prefixEnd_6563961 : Nat := 4983230072969 + 3 ^ 40 * 6563961 * 2
def baseEnd_6563961 : Nat := 374496332262988689566711

theorem tailTrace_6563961 : CollatzResearch.WordTrace tailWord_6563961 prefixEnd_6563961 374496332262988689566711 := by
  unfold tailWord_6563961
  simp only [CollatzResearch.WordTrace]
  refine ⟨239407325772897807133731737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159604883848598538089154491 239407325772897807133731737)
  ·
    refine ⟨179555494329673355350298803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239407325772897807133731737 179555494329673355350298803)
    ·
      refine ⟨269333241494510033025448205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179555494329673355350298803 269333241494510033025448205)
      ·
        refine ⟨100999965560441262384543077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269333241494510033025448205 100999965560441262384543077)
        ·
          refine ⟨18937493542582736697101827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100999965560441262384543077 18937493542582736697101827)
          ·
            refine ⟨28406240313874105045652741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18937493542582736697101827 28406240313874105045652741)
            ·
              refine ⟨5326170058851394696059889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28406240313874105045652741 5326170058851394696059889)
              ·
                refine ⟨3994627544138546022044917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5326170058851394696059889 3994627544138546022044917)
                ·
                  refine ⟨374496332262988689566711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3994627544138546022044917 374496332262988689566711)
                  ·
                    rfl

theorem cell23_6563961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 5].length) (baseStart_6563961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563961 prefixEnd_6563961 := by exact prefixLift 6563961
  have htrace : WordTrace (prefixWord ++ tailWord_6563961) baseStart_6563961 baseEnd_6563961 := by
    simpa [prefixWord, tailWord_6563961, baseEnd_6563961] using wordTrace_append hprefix tailTrace_6563961
  have hstable : (prefixWord ++ tailWord_6563961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563961).length < 2 ^ (prefixWord ++ tailWord_6563961).sum := by decide
  have hdescent : baseEnd_6563961 < baseStart_6563961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563964 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 2, 5, 2]
def baseStart_6563964 : Nat := 118140960795 + 6563964 * 2 ^ 59
def prefixEnd_6563964 : Nat := 4983230072969 + 3 ^ 40 * 6563964 * 2
def baseEnd_6563964 : Nat := 3370468530808861694362885

theorem tailTrace_6563964 : CollatzResearch.WordTrace tailWord_6563964 prefixEnd_6563964 3370468530808861694362885 := by
  unfold tailWord_6563964
  simp only [CollatzResearch.WordTrace]
  refine ⟨119703717595943469323045473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159604956794591292430727297 119703717595943469323045473)
  ·
    refine ⟨89777788196957601992284105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119703717595943469323045473 89777788196957601992284105)
    ·
      refine ⟨67333341147718201494213079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89777788196957601992284105 67333341147718201494213079)
      ·
        refine ⟨101000011721577302241319619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67333341147718201494213079 101000011721577302241319619)
        ·
          refine ⟨151500017582365953361979429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101000011721577302241319619 151500017582365953361979429)
          ·
            refine ⟨28406253296693616255371143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151500017582365953361979429 28406253296693616255371143)
            ·
              refine ⟨42609379945040424383056715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28406253296693616255371143 42609379945040424383056715)
              ·
                refine ⟨63914069917560636574585073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42609379945040424383056715 63914069917560636574585073)
                ·
                  refine ⟨47935552438170477430938805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63914069917560636574585073 47935552438170477430938805)
                  ·
                    refine ⟨4493958041078482259150513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47935552438170477430938805 4493958041078482259150513)
                    ·
                      refine ⟨3370468530808861694362885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4493958041078482259150513 3370468530808861694362885)
                      ·
                        rfl

theorem cell23_6563964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_6563964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563964 prefixEnd_6563964 := by exact prefixLift 6563964
  have htrace : WordTrace (prefixWord ++ tailWord_6563964) baseStart_6563964 baseEnd_6563964 := by
    simpa [prefixWord, tailWord_6563964, baseEnd_6563964] using wordTrace_append hprefix tailTrace_6563964
  have hstable : (prefixWord ++ tailWord_6563964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563964).length < 2 ^ (prefixWord ++ tailWord_6563964).sum := by decide
  have hdescent : baseEnd_6563964 < baseStart_6563964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563977 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 4]
def baseStart_6563977 : Nat := 118140960795 + 6563977 * 2 ^ 59
def prefixEnd_6563977 : Nat := 4983230072969 + 3 ^ 40 * 6563977 * 2
def baseEnd_6563977 : Nat := 3370475206057370143500325

theorem tailTrace_6563977 : CollatzResearch.WordTrace tailWord_6563977 prefixEnd_6563977 3370475206057370143500325 := by
  unfold tailWord_6563977
  simp only [CollatzResearch.WordTrace]
  refine ⟨239407909340839841866314185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159605272893893227910876123 239407909340839841866314185)
  ·
    refine ⟨179555932005629881399735639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239407909340839841866314185 179555932005629881399735639)
    ·
      refine ⟨269333898008444822099603459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179555932005629881399735639 269333898008444822099603459)
      ·
        refine ⟨404000847012667233149405189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269333898008444822099603459 404000847012667233149405189)
        ·
          refine ⟨75750158814875106215513473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404000847012667233149405189 75750158814875106215513473)
          ·
            refine ⟨56812619111156329661635105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75750158814875106215513473 56812619111156329661635105)
            ·
              refine ⟨42609464333367247246226329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56812619111156329661635105 42609464333367247246226329)
              ·
                refine ⟨31957098250025435434669747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42609464333367247246226329 31957098250025435434669747)
                ·
                  refine ⟨47935647375038153152004621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31957098250025435434669747 47935647375038153152004621)
                  ·
                    refine ⟨17975867765639307432001733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47935647375038153152004621 17975867765639307432001733)
                    ·
                      refine ⟨3370475206057370143500325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17975867765639307432001733 3370475206057370143500325)
                      ·
                        rfl

theorem cell23_6563977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 3, 4].length) (baseStart_6563977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563977 prefixEnd_6563977 := by exact prefixLift 6563977
  have htrace : WordTrace (prefixWord ++ tailWord_6563977) baseStart_6563977 baseEnd_6563977 := by
    simpa [prefixWord, tailWord_6563977, baseEnd_6563977] using wordTrace_append hprefix tailTrace_6563977
  have hstable : (prefixWord ++ tailWord_6563977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563977).length < 2 ^ (prefixWord ++ tailWord_6563977).sum := by decide
  have hdescent : baseEnd_6563977 < baseStart_6563977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6563991 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 2, 5]
def baseStart_6563991 : Nat := 118140960795 + 6563991 * 2 ^ 59
def prefixEnd_6563991 : Nat := 4983230072969 + 3 ^ 40 * 6563991 * 2
def baseEnd_6563991 : Nat := 1123494131595511029575087

theorem tailTrace_6563991 : CollatzResearch.WordTrace tailWord_6563991 prefixEnd_6563991 1123494131595511029575087 := by
  unfold tailWord_6563991
  simp only [CollatzResearch.WordTrace]
  refine ⟨239408419962789122257323827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159605613308526081504882551 239408419962789122257323827)
  ·
    refine ⟨359112629944183683385985741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239408419962789122257323827 359112629944183683385985741)
    ·
      refine ⟨134667236229068881269744653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359112629944183683385985741 134667236229068881269744653)
      ·
        refine ⟨50500213585900830476154245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134667236229068881269744653 50500213585900830476154245)
        ·
          refine ⟨9468790047356405714278921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50500213585900830476154245 9468790047356405714278921)
          ·
            refine ⟨7101592535517304285709191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9468790047356405714278921 7101592535517304285709191)
            ·
              refine ⟨10652388803275956428563787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101592535517304285709191 10652388803275956428563787)
              ·
                refine ⟨15978583204913934642845681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652388803275956428563787 15978583204913934642845681)
                ·
                  refine ⟨11983937403685450982134261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15978583204913934642845681 11983937403685450982134261)
                  ·
                    refine ⟨1123494131595511029575087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11983937403685450982134261 1123494131595511029575087)
                    ·
                      rfl

theorem cell23_6563991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 2, 5].length) (baseStart_6563991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6563991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6563991 prefixEnd_6563991 := by exact prefixLift 6563991
  have htrace : WordTrace (prefixWord ++ tailWord_6563991) baseStart_6563991 baseEnd_6563991 := by
    simpa [prefixWord, tailWord_6563991, baseEnd_6563991] using wordTrace_append hprefix tailTrace_6563991
  have hstable : (prefixWord ++ tailWord_6563991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6563991).length < 2 ^ (prefixWord ++ tailWord_6563991).sum := by decide
  have hdescent : baseEnd_6563991 < baseStart_6563991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6563991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564064 : List Nat := [2, 1, 1, 3, 1, 3, 1, 5, 1, 5]
def baseStart_6564064 : Nat := 118140960795 + 6564064 * 2 ^ 59
def prefixEnd_6564064 : Nat := 4983230072969 + 3 ^ 40 * 6564064 * 2
def baseEnd_6564064 : Nat := 1123506626291437101037475

theorem tailTrace_6564064 : CollatzResearch.WordTrace tailWord_6564064 prefixEnd_6564064 1123506626291437101037475 := by
  unfold tailWord_6564064
  simp only [CollatzResearch.WordTrace]
  refine ⟨119705541245762327862365623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159607388327683103816487497 119705541245762327862365623)
  ·
    refine ⟨179558311868643491793548435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119705541245762327862365623 179558311868643491793548435)
    ·
      refine ⟨269337467802965237690322653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179558311868643491793548435 269337467802965237690322653)
      ·
        refine ⟨101001550426111964133870995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269337467802965237690322653 101001550426111964133870995)
        ·
          refine ⟨151502325639167946200806493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101001550426111964133870995 151502325639167946200806493)
          ·
            refine ⟨56813372114687979825302435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151502325639167946200806493 56813372114687979825302435)
            ·
              refine ⟨85220058172031969737953653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56813372114687979825302435 85220058172031969737953653)
              ·
                refine ⟨7989380453627997162933155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85220058172031969737953653 7989380453627997162933155)
                ·
                  refine ⟨11984070680441995744399733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7989380453627997162933155 11984070680441995744399733)
                  ·
                    refine ⟨1123506626291437101037475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11984070680441995744399733 1123506626291437101037475)
                    ·
                      rfl

theorem cell23_6564064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 5, 1, 5].length) (baseStart_6564064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564064 prefixEnd_6564064 := by exact prefixLift 6564064
  have htrace : WordTrace (prefixWord ++ tailWord_6564064) baseStart_6564064 baseEnd_6564064 := by
    simpa [prefixWord, tailWord_6564064, baseEnd_6564064] using wordTrace_append hprefix tailTrace_6564064
  have hstable : (prefixWord ++ tailWord_6564064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564064).length < 2 ^ (prefixWord ++ tailWord_6564064).sum := by decide
  have hdescent : baseEnd_6564064 < baseStart_6564064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564098 : List Nat := [3, 4, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_6564098 : Nat := 118140960795 + 6564098 * 2 ^ 59
def prefixEnd_6564098 : Nat := 4983230072969 + 3 ^ 40 * 6564098 * 2
def baseEnd_6564098 : Nat := 1123512445738854723362423

theorem tailTrace_6564098 : CollatzResearch.WordTrace tailWord_6564098 prefixEnd_6564098 1123512445738854723362423 := by
  unfold tailWord_6564098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59853080643350369882867237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159608215048934319687645965 59853080643350369882867237)
  ·
    refine ⟨11222452620628194353037607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59853080643350369882867237 11222452620628194353037607)
    ·
      refine ⟨16833678930942291529556411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11222452620628194353037607 16833678930942291529556411)
      ·
        refine ⟨25250518396413437294334617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16833678930942291529556411 25250518396413437294334617)
        ·
          refine ⟨18937888797310077970750963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25250518396413437294334617 18937888797310077970750963)
          ·
            refine ⟨28406833195965116956126445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18937888797310077970750963 28406833195965116956126445)
            ·
              refine ⟨10652562448486918858547417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28406833195965116956126445 10652562448486918858547417)
              ·
                refine ⟨7989421836365189143910563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10652562448486918858547417 7989421836365189143910563)
                ·
                  refine ⟨11984132754547783715865845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7989421836365189143910563 11984132754547783715865845)
                  ·
                    refine ⟨1123512445738854723362423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11984132754547783715865845 1123512445738854723362423)
                    ·
                      rfl

theorem cell23_6564098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_6564098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564098 prefixEnd_6564098 := by exact prefixLift 6564098
  have htrace : WordTrace (prefixWord ++ tailWord_6564098) baseStart_6564098 baseEnd_6564098 := by
    simpa [prefixWord, tailWord_6564098, baseEnd_6564098] using wordTrace_append hprefix tailTrace_6564098
  have hstable : (prefixWord ++ tailWord_6564098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564098).length < 2 ^ (prefixWord ++ tailWord_6564098).sum := by decide
  have hdescent : baseEnd_6564098 < baseStart_6564098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564107 : List Nat := [1, 1, 1, 1, 5, 2, 1, 11]
def baseStart_6564107 : Nat := 118140960795 + 6564107 * 2 ^ 59
def prefixEnd_6564107 : Nat := 4983230072969 + 3 ^ 40 * 6564107 * 2
def baseEnd_6564107 : Nat := 124834887353424245736101

theorem tailTrace_6564107 : CollatzResearch.WordTrace tailWord_6564107 prefixEnd_6564107 124834887353424245736101 := by
  unfold tailWord_6564107
  simp only [CollatzResearch.WordTrace]
  refine ⟨239412650830368874068546575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159608433886912582712364383 239412650830368874068546575)
  ·
    refine ⟨359118976245553311102819863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239412650830368874068546575 359118976245553311102819863)
    ·
      refine ⟨538678464368329966654229795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359118976245553311102819863 538678464368329966654229795)
      ·
        refine ⟨808017696552494949981344693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538678464368329966654229795 808017696552494949981344693)
        ·
          refine ⟨75751659051796401560751065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 808017696552494949981344693 75751659051796401560751065)
          ·
            refine ⟨56813744288847301170563299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75751659051796401560751065 56813744288847301170563299)
            ·
              refine ⟨85220616433270951755844949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56813744288847301170563299 85220616433270951755844949)
              ·
                refine ⟨124834887353424245736101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 85220616433270951755844949 124834887353424245736101)
                ·
                  rfl

theorem cell23_6564107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 11].length) (baseStart_6564107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564107 prefixEnd_6564107 := by exact prefixLift 6564107
  have htrace : WordTrace (prefixWord ++ tailWord_6564107) baseStart_6564107 baseEnd_6564107 := by
    simpa [prefixWord, tailWord_6564107, baseEnd_6564107] using wordTrace_append hprefix tailTrace_6564107
  have hstable : (prefixWord ++ tailWord_6564107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564107).length < 2 ^ (prefixWord ++ tailWord_6564107).sum := by decide
  have hdescent : baseEnd_6564107 < baseStart_6564107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564128 : List Nat := [2, 1, 1, 5, 2, 2, 2, 2, 2, 4]
def baseStart_6564128 : Nat := 118140960795 + 6564128 * 2 ^ 59
def prefixEnd_6564128 : Nat := 4983230072969 + 3 ^ 40 * 6564128 * 2
def baseEnd_6564128 : Nat := 1123517580545399684237377

theorem tailTrace_6564128 : CollatzResearch.WordTrace tailWord_6564128 prefixEnd_6564128 1123517580545399684237377 := by
  unfold tailWord_6564128
  simp only [CollatzResearch.WordTrace]
  refine ⟨119706708381646397327530519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159608944508861863103374025 119706708381646397327530519)
  ·
    refine ⟨179560062572469595991295779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119706708381646397327530519 179560062572469595991295779)
    ·
      refine ⟨269340093858704393986943669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179560062572469595991295779 269340093858704393986943669)
      ·
        refine ⟨25250633799253536936275969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 269340093858704393986943669 25250633799253536936275969)
        ·
          refine ⟨18937975349440152702206977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25250633799253536936275969 18937975349440152702206977)
          ·
            refine ⟨14203481512080114526655233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18937975349440152702206977 14203481512080114526655233)
            ·
              refine ⟨10652611134060085894991425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14203481512080114526655233 10652611134060085894991425)
              ·
                refine ⟨7989458350545064421243569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10652611134060085894991425 7989458350545064421243569)
                ·
                  refine ⟨5992093762908798315932677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7989458350545064421243569 5992093762908798315932677)
                  ·
                    refine ⟨1123517580545399684237377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5992093762908798315932677 1123517580545399684237377)
                    ·
                      rfl

theorem cell23_6564128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 2, 2, 4].length) (baseStart_6564128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564128 prefixEnd_6564128 := by exact prefixLift 6564128
  have htrace : WordTrace (prefixWord ++ tailWord_6564128) baseStart_6564128 baseEnd_6564128 := by
    simpa [prefixWord, tailWord_6564128, baseEnd_6564128] using wordTrace_append hprefix tailTrace_6564128
  have hstable : (prefixWord ++ tailWord_6564128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564128).length < 2 ^ (prefixWord ++ tailWord_6564128).sum := by decide
  have hdescent : baseEnd_6564128 < baseStart_6564128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564148 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_6564148 : Nat := 118140960795 + 6564148 * 2 ^ 59
def prefixEnd_6564148 : Nat := 4983230072969 + 3 ^ 40 * 6564148 * 2
def baseEnd_6564148 : Nat := 3370563011249288974462039

theorem tailTrace_6564148 : CollatzResearch.WordTrace tailWord_6564148 prefixEnd_6564148 3370563011249288974462039 := by
  unfold tailWord_6564148
  simp only [CollatzResearch.WordTrace]
  refine ⟨119707073111610169035394549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159609430815480225380526065 119707073111610169035394549)
  ·
    refine ⟨11222538104213453347068239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119707073111610169035394549 11222538104213453347068239)
    ·
      refine ⟨16833807156320180020602359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11222538104213453347068239 16833807156320180020602359)
      ·
        refine ⟨25250710734480270030903539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16833807156320180020602359 25250710734480270030903539)
        ·
          refine ⟨37876066101720405046355309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25250710734480270030903539 37876066101720405046355309)
          ·
            refine ⟨14203524788145151892383241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37876066101720405046355309 14203524788145151892383241)
            ·
              refine ⟨10652643591108863919287431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14203524788145151892383241 10652643591108863919287431)
              ·
                refine ⟨15978965386663295878931147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652643591108863919287431 15978965386663295878931147)
                ·
                  refine ⟨23968448079994943818396721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15978965386663295878931147 23968448079994943818396721)
                  ·
                    refine ⟨17976336059996207863797541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23968448079994943818396721 17976336059996207863797541)
                    ·
                      refine ⟨3370563011249288974462039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17976336059996207863797541 3370563011249288974462039)
                      ·
                        rfl

theorem cell23_6564148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_6564148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564148 prefixEnd_6564148 := by exact prefixLift 6564148
  have htrace : WordTrace (prefixWord ++ tailWord_6564148) baseStart_6564148 baseEnd_6564148 := by
    simpa [prefixWord, tailWord_6564148, baseEnd_6564148] using wordTrace_append hprefix tailTrace_6564148
  have hstable : (prefixWord ++ tailWord_6564148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564148).length < 2 ^ (prefixWord ++ tailWord_6564148).sum := by decide
  have hdescent : baseEnd_6564148 < baseStart_6564148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564174 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_6564174 : Nat := 118140960795 + 6564174 * 2 ^ 59
def prefixEnd_6564174 : Nat := 4983230072969 + 3 ^ 40 * 6564174 * 2
def baseEnd_6564174 : Nat := 3370576361746305872736919

theorem tailTrace_6564174 : CollatzResearch.WordTrace tailWord_6564174 prefixEnd_6564174 3370576361746305872736919 := by
  unfold tailWord_6564174
  simp only [CollatzResearch.WordTrace]
  refine ⟨29926886815140768063904447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159610063014084096340823717 29926886815140768063904447)
  ·
    refine ⟨44890330222711152095856671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29926886815140768063904447 44890330222711152095856671)
    ·
      refine ⟨67335495334066728143785007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44890330222711152095856671 67335495334066728143785007)
      ·
        refine ⟨101003243001100092215677511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67335495334066728143785007 101003243001100092215677511)
        ·
          refine ⟨151504864501650138323516267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101003243001100092215677511 151504864501650138323516267)
          ·
            refine ⟨227257296752475207485274401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151504864501650138323516267 227257296752475207485274401)
            ·
              refine ⟨170442972564356405613955801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227257296752475207485274401 170442972564356405613955801)
              ·
                refine ⟨127832229423267304210466851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 170442972564356405613955801 127832229423267304210466851)
                ·
                  refine ⟨191748344134900956315700277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127832229423267304210466851 191748344134900956315700277)
                  ·
                    refine ⟨17976407262646964654596901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 191748344134900956315700277 17976407262646964654596901)
                    ·
                      refine ⟨3370576361746305872736919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17976407262646964654596901 3370576361746305872736919)
                      ·
                        rfl

theorem cell23_6564174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_6564174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564174 prefixEnd_6564174 := by exact prefixLift 6564174
  have htrace : WordTrace (prefixWord ++ tailWord_6564174) baseStart_6564174 baseEnd_6564174 := by
    simpa [prefixWord, tailWord_6564174, baseEnd_6564174] using wordTrace_append hprefix tailTrace_6564174
  have hstable : (prefixWord ++ tailWord_6564174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564174).length < 2 ^ (prefixWord ++ tailWord_6564174).sum := by decide
  have hdescent : baseEnd_6564174 < baseStart_6564174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564191 : List Nat := [1, 1, 2, 3, 1, 2, 2, 2, 3, 4, 2]
def baseStart_6564191 : Nat := 118140960795 + 6564191 * 2 ^ 59
def prefixEnd_6564191 : Nat := 4983230072969 + 3 ^ 40 * 6564191 * 2
def baseEnd_6564191 : Nat := 3370585090917432306224341

theorem tailTrace_6564191 : CollatzResearch.WordTrace tailWord_6564191 prefixEnd_6564191 3370585090917432306224341 := by
  unfold tailWord_6564191
  simp only [CollatzResearch.WordTrace]
  refine ⟨239415714562064556414604427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159610476374709704276402951 239415714562064556414604427)
  ·
    refine ⟨359123571843096834621906641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239415714562064556414604427 359123571843096834621906641)
    ·
      refine ⟨269342678882322625966429981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359123571843096834621906641 269342678882322625966429981)
      ·
        refine ⟨101003504580870984737411243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269342678882322625966429981 101003504580870984737411243)
        ·
          refine ⟨151505256871306477106116865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101003504580870984737411243 151505256871306477106116865)
          ·
            refine ⟨113628942653479857829587649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151505256871306477106116865 113628942653479857829587649)
            ·
              refine ⟨85221706990109893372190737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113628942653479857829587649 85221706990109893372190737)
              ·
                refine ⟨63916280242582420029143053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85221706990109893372190737 63916280242582420029143053)
                ·
                  refine ⟨23968605090968407510928645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63916280242582420029143053 23968605090968407510928645)
                  ·
                    refine ⟨4494113454556576408299121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23968605090968407510928645 4494113454556576408299121)
                    ·
                      refine ⟨3370585090917432306224341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494113454556576408299121 3370585090917432306224341)
                      ·
                        rfl

theorem cell23_6564191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_6564191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564191 prefixEnd_6564191 := by exact prefixLift 6564191
  have htrace : WordTrace (prefixWord ++ tailWord_6564191) baseStart_6564191 baseEnd_6564191 := by
    simpa [prefixWord, tailWord_6564191, baseEnd_6564191] using wordTrace_append hprefix tailTrace_6564191
  have hstable : (prefixWord ++ tailWord_6564191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564191).length < 2 ^ (prefixWord ++ tailWord_6564191).sum := by decide
  have hdescent : baseEnd_6564191 < baseStart_6564191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564202 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_6564202 : Nat := 118140960795 + 6564202 * 2 ^ 59
def prefixEnd_6564202 : Nat := 4983230072969 + 3 ^ 40 * 6564202 * 2
def baseEnd_6564202 : Nat := 3370590739204631763186791

theorem tailTrace_6564202 : CollatzResearch.WordTrace tailWord_6564202 prefixEnd_6564202 3370590739204631763186791 := by
  unfold tailWord_6564202
  simp only [CollatzResearch.WordTrace]
  refine ⟨59854028941256176323313715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159610743843349803528836573 59854028941256176323313715)
  ·
    refine ⟨89781043411884264484970573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59854028941256176323313715 89781043411884264484970573)
    ·
      refine ⟨33667891279456599181863965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89781043411884264484970573 33667891279456599181863965)
      ·
        refine ⟨12625459229796224693198987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33667891279456599181863965 12625459229796224693198987)
        ·
          refine ⟨18938188844694337039798481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625459229796224693198987 18938188844694337039798481)
          ·
            refine ⟨14203641633520752779848861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18938188844694337039798481 14203641633520752779848861)
            ·
              refine ⟨5326365612570282292443323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14203641633520752779848861 5326365612570282292443323)
              ·
                refine ⟨7989548418855423438664985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326365612570282292443323 7989548418855423438664985)
                ·
                  refine ⟨5992161314141567578998739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7989548418855423438664985 5992161314141567578998739)
                  ·
                    refine ⟨8988241971212351368498109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5992161314141567578998739 8988241971212351368498109)
                    ·
                      refine ⟨3370590739204631763186791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8988241971212351368498109 3370590739204631763186791)
                      ·
                        rfl

theorem cell23_6564202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_6564202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564202 prefixEnd_6564202 := by exact prefixLift 6564202
  have htrace : WordTrace (prefixWord ++ tailWord_6564202) baseStart_6564202 baseEnd_6564202 := by
    simpa [prefixWord, tailWord_6564202, baseEnd_6564202] using wordTrace_append hprefix tailTrace_6564202
  have hstable : (prefixWord ++ tailWord_6564202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564202).length < 2 ^ (prefixWord ++ tailWord_6564202).sum := by decide
  have hdescent : baseEnd_6564202 < baseStart_6564202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564208 : List Nat := [2, 1, 1, 1, 4, 3, 3, 1, 1, 4, 2]
def baseStart_6564208 : Nat := 118140960795 + 6564208 * 2 ^ 59
def prefixEnd_6564208 : Nat := 4983230072969 + 3 ^ 40 * 6564208 * 2
def baseEnd_6564208 : Nat := 3370593820088558739711763

theorem tailTrace_6564208 : CollatzResearch.WordTrace tailWord_6564208 prefixEnd_6564208 3370593820088558739711763 := by
  unfold tailWord_6564208
  simp only [CollatzResearch.WordTrace]
  refine ⟨119708167301501484158986639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159610889735335312211982185 119708167301501484158986639)
  ·
    refine ⟨179562250952252226238479959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119708167301501484158986639 179562250952252226238479959)
    ·
      refine ⟨269343376428378339357719939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179562250952252226238479959 269343376428378339357719939)
      ·
        refine ⟨404015064642567509036579909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269343376428378339357719939 404015064642567509036579909)
        ·
          refine ⟨75752824620481407944358733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404015064642567509036579909 75752824620481407944358733)
          ·
            refine ⟨28407309232680527979134525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75752824620481407944358733 28407309232680527979134525)
            ·
              refine ⟨10652740962255197992175447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28407309232680527979134525 10652740962255197992175447)
              ·
                refine ⟨15979111443382796988263171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652740962255197992175447 15979111443382796988263171)
                ·
                  refine ⟨23968667165074195482394757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15979111443382796988263171 23968667165074195482394757)
                  ·
                    refine ⟨4494125093451411652949017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23968667165074195482394757 4494125093451411652949017)
                    ·
                      refine ⟨3370593820088558739711763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494125093451411652949017 3370593820088558739711763)
                      ·
                        rfl

theorem cell23_6564208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 1, 1, 4, 2].length) (baseStart_6564208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564208 prefixEnd_6564208 := by exact prefixLift 6564208
  have htrace : WordTrace (prefixWord ++ tailWord_6564208) baseStart_6564208 baseEnd_6564208 := by
    simpa [prefixWord, tailWord_6564208, baseEnd_6564208] using wordTrace_append hprefix tailTrace_6564208
  have hstable : (prefixWord ++ tailWord_6564208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564208).length < 2 ^ (prefixWord ++ tailWord_6564208).sum := by decide
  have hdescent : baseEnd_6564208 < baseStart_6564208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564225 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 4, 2, 2]
def baseStart_6564225 : Nat := 118140960795 + 6564225 * 2 ^ 59
def prefixEnd_6564225 : Nat := 4983230072969 + 3 ^ 40 * 6564225 * 2
def baseEnd_6564225 : Nat := 3370602549259685173199185

theorem tailTrace_6564225 : CollatzResearch.WordTrace tailWord_6564225 prefixEnd_6564225 3370602549259685173199185 := by
  unfold tailWord_6564225
  simp only [CollatzResearch.WordTrace]
  refine ⟨239416954643941380221342129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159611303095960920147561419 239416954643941380221342129)
  ·
    refine ⟨179562715982956035166006597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239416954643941380221342129 179562715982956035166006597)
    ·
      refine ⟨33668009246804256593626237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179562715982956035166006597 33668009246804256593626237)
      ·
        refine ⟨12625503467551596222609839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33668009246804256593626237 12625503467551596222609839)
        ·
          refine ⟨18938255201327394333914759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625503467551596222609839 18938255201327394333914759)
          ·
            refine ⟨28407382801991091500872139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18938255201327394333914759 28407382801991091500872139)
            ·
              refine ⟨42611074202986637251308209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28407382801991091500872139 42611074202986637251308209)
              ·
                refine ⟨31958305652239977938481157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42611074202986637251308209 31958305652239977938481157)
                ·
                  refine ⟨5992182309794995863465217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31958305652239977938481157 5992182309794995863465217)
                  ·
                    refine ⟨4494136732346246897598913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5992182309794995863465217 4494136732346246897598913)
                    ·
                      refine ⟨3370602549259685173199185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494136732346246897598913 3370602549259685173199185)
                      ·
                        rfl

theorem cell23_6564225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_6564225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564225 prefixEnd_6564225 := by exact prefixLift 6564225
  have htrace : WordTrace (prefixWord ++ tailWord_6564225) baseStart_6564225 baseEnd_6564225 := by
    simpa [prefixWord, tailWord_6564225, baseEnd_6564225] using wordTrace_append hprefix tailTrace_6564225
  have hstable : (prefixWord ++ tailWord_6564225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564225).length < 2 ^ (prefixWord ++ tailWord_6564225).sum := by decide
  have hdescent : baseEnd_6564225 < baseStart_6564225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564248 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 7]
def baseStart_6564248 : Nat := 118140960795 + 6564248 * 2 ^ 59
def prefixEnd_6564248 : Nat := 4983230072969 + 3 ^ 40 * 6564248 * 2
def baseEnd_6564248 : Nat := 374512706590526509245731

theorem tailTrace_6564248 : CollatzResearch.WordTrace tailWord_6564248 prefixEnd_6564248 374512706590526509245731 := by
  unfold tailWord_6564248
  simp only [CollatzResearch.WordTrace]
  refine ⟨119708896761429027574714699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159611862348572036766286265 119708896761429027574714699)
  ·
    refine ⟨179563345142143541362072049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119708896761429027574714699 179563345142143541362072049)
    ·
      refine ⟨134672508856607656021554037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179563345142143541362072049 134672508856607656021554037)
      ·
        refine ⟨12625547705306967752020691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134672508856607656021554037 12625547705306967752020691)
        ·
          refine ⟨18938321557960451628031037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625547705306967752020691 18938321557960451628031037)
          ·
            refine ⟨7101870584235169360511639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18938321557960451628031037 7101870584235169360511639)
            ·
              refine ⟨10652805876352754040767459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7101870584235169360511639 10652805876352754040767459)
              ·
                refine ⟨15979208814529131061151189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10652805876352754040767459 15979208814529131061151189)
                ·
                  refine ⟨374512706590526509245731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15979208814529131061151189 374512706590526509245731)
                  ·
                    rfl

theorem cell23_6564248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 7].length) (baseStart_6564248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564248 prefixEnd_6564248 := by exact prefixLift 6564248
  have htrace : WordTrace (prefixWord ++ tailWord_6564248) baseStart_6564248 baseEnd_6564248 := by
    simpa [prefixWord, tailWord_6564248, baseEnd_6564248] using wordTrace_append hprefix tailTrace_6564248
  have hstable : (prefixWord ++ tailWord_6564248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564248).length < 2 ^ (prefixWord ++ tailWord_6564248).sum := by decide
  have hdescent : baseEnd_6564248 < baseStart_6564248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564298 : List Nat := [3, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_6564298 : Nat := 118140960795 + 6564298 * 2 ^ 59
def prefixEnd_6564298 : Nat := 4983230072969 + 3 ^ 40 * 6564298 * 2
def baseEnd_6564298 : Nat := 3370640033347463387586349

theorem tailTrace_6564298 : CollatzResearch.WordTrace tailWord_6564298 prefixEnd_6564298 3370640033347463387586349 := by
  unfold tailWord_6564298
  simp only [CollatzResearch.WordTrace]
  refine ⟨59854904293169228422187387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159613078115117942459166365 59854904293169228422187387)
  ·
    refine ⟨89782356439753842633281081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59854904293169228422187387 89782356439753842633281081)
    ·
      refine ⟨67336767329815381974960811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89782356439753842633281081 67336767329815381974960811)
      ·
        refine ⟨101005150994723072962441217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67336767329815381974960811 101005150994723072962441217)
        ·
          refine ⟨75753863246042304721830913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101005150994723072962441217 75753863246042304721830913)
          ·
            refine ⟨56815397434531728541373185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75753863246042304721830913 56815397434531728541373185)
            ·
              refine ⟨42611548075898796406029889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56815397434531728541373185 42611548075898796406029889)
              ·
                refine ⟨31958661056924097304522417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42611548075898796406029889 31958661056924097304522417)
                ·
                  refine ⟨23968995792693072978391813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31958661056924097304522417 23968995792693072978391813)
                  ·
                    refine ⟨4494186711129951183448465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23968995792693072978391813 4494186711129951183448465)
                    ·
                      refine ⟨3370640033347463387586349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494186711129951183448465 3370640033347463387586349)
                      ·
                        rfl

theorem cell23_6564298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_6564298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564298 prefixEnd_6564298 := by exact prefixLift 6564298
  have htrace : WordTrace (prefixWord ++ tailWord_6564298) baseStart_6564298 baseEnd_6564298 := by
    simpa [prefixWord, tailWord_6564298, baseEnd_6564298] using wordTrace_append hprefix tailTrace_6564298
  have hstable : (prefixWord ++ tailWord_6564298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564298).length < 2 ^ (prefixWord ++ tailWord_6564298).sum := by decide
  have hdescent : baseEnd_6564298 < baseStart_6564298 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564321 : List Nat := [1, 2, 3, 1, 2, 2, 1, 5, 6]
def baseStart_6564321 : Nat := 118140960795 + 6564321 * 2 ^ 59
def prefixEnd_6564321 : Nat := 4983230072969 + 3 ^ 40 * 6564321 * 2
def baseEnd_6564321 : Nat := 374516871489168533066527

theorem tailTrace_6564321 : CollatzResearch.WordTrace tailWord_6564321 prefixEnd_6564321 374516871489168533066527 := by
  unfold tailWord_6564321
  simp only [CollatzResearch.WordTrace]
  refine ⟨239420456051593588616836817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159613637367729059077891211 239420456051593588616836817)
  ·
    refine ⟨179565342038695191462627613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239420456051593588616836817 179565342038695191462627613)
    ·
      refine ⟨67337003264510696798485355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179565342038695191462627613 67337003264510696798485355)
      ·
        refine ⟨101005504896766045197728033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67337003264510696798485355 101005504896766045197728033)
        ·
          refine ⟨75754128672574533898296025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101005504896766045197728033 75754128672574533898296025)
          ·
            refine ⟨56815596504430900423722019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75754128672574533898296025 56815596504430900423722019)
            ·
              refine ⟨85223394756646350635583029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56815596504430900423722019 85223394756646350635583029)
              ·
                refine ⟨7989693258435595372085909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85223394756646350635583029 7989693258435595372085909)
                ·
                  refine ⟨374516871489168533066527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7989693258435595372085909 374516871489168533066527)
                  ·
                    rfl

theorem cell23_6564321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 6].length) (baseStart_6564321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564321 prefixEnd_6564321 := by exact prefixLift 6564321
  have htrace : WordTrace (prefixWord ++ tailWord_6564321) baseStart_6564321 baseEnd_6564321 := by
    simpa [prefixWord, tailWord_6564321, baseEnd_6564321] using wordTrace_append hprefix tailTrace_6564321
  have hstable : (prefixWord ++ tailWord_6564321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564321).length < 2 ^ (prefixWord ++ tailWord_6564321).sum := by decide
  have hdescent : baseEnd_6564321 < baseStart_6564321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564325 : List Nat := [1, 3, 1, 5, 2, 1, 1, 2, 3, 4]
def baseStart_6564325 : Nat := 118140960795 + 6564325 * 2 ^ 59
def prefixEnd_6564325 : Nat := 4983230072969 + 3 ^ 40 * 6564325 * 2
def baseEnd_6564325 : Nat := 1123551299108378260649575

theorem tailTrace_6564325 : CollatzResearch.WordTrace tailWord_6564325 prefixEnd_6564325 1123551299108378260649575 := by
  unfold tailWord_6564325
  simp only [CollatzResearch.WordTrace]
  refine ⟨239420601943579097299982429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159613734629052731533321619 239420601943579097299982429)
  ·
    refine ⟨89782725728842161487493411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239420601943579097299982429 89782725728842161487493411)
    ·
      refine ⟨134674088593263242231240117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89782725728842161487493411 134674088593263242231240117)
      ·
        refine ⟨12625695805618428959178761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134674088593263242231240117 12625695805618428959178761)
        ·
          refine ⟨9469271854213821719384071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12625695805618428959178761 9469271854213821719384071)
          ·
            refine ⟨14203907781320732579076107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469271854213821719384071 14203907781320732579076107)
            ·
              refine ⟨21305861671981098868614161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14203907781320732579076107 21305861671981098868614161)
              ·
                refine ⟨15979396253985824151460621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21305861671981098868614161 15979396253985824151460621)
                ·
                  refine ⟨5992273595244684056797733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15979396253985824151460621 5992273595244684056797733)
                  ·
                    refine ⟨1123551299108378260649575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5992273595244684056797733 1123551299108378260649575)
                    ·
                      rfl

theorem cell23_6564325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 3, 4].length) (baseStart_6564325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564325 prefixEnd_6564325 := by exact prefixLift 6564325
  have htrace : WordTrace (prefixWord ++ tailWord_6564325) baseStart_6564325 baseEnd_6564325 := by
    simpa [prefixWord, tailWord_6564325, baseEnd_6564325] using wordTrace_append hprefix tailTrace_6564325
  have hstable : (prefixWord ++ tailWord_6564325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564325).length < 2 ^ (prefixWord ++ tailWord_6564325).sum := by decide
  have hdescent : baseEnd_6564325 < baseStart_6564325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564342 : List Nat := [5, 1, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_6564342 : Nat := 118140960795 + 6564342 * 2 ^ 59
def prefixEnd_6564342 : Nat := 4983230072969 + 3 ^ 40 * 6564342 * 2
def baseEnd_6564342 : Nat := 1123554208832087071812049

theorem tailTrace_6564342 : CollatzResearch.WordTrace tailWord_6564342 prefixEnd_6564342 1123554208832087071812049 := by
  unfold tailWord_6564342
  simp only [CollatzResearch.WordTrace]
  refine ⟨14963826374032344325209455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159614147989678339468900853 14963826374032344325209455)
  ·
    refine ⟨22445739561048516487814183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14963826374032344325209455 22445739561048516487814183)
    ·
      refine ⟨33668609341572774731721275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22445739561048516487814183 33668609341572774731721275)
      ·
        refine ⟨50502914012359162097581913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33668609341572774731721275 50502914012359162097581913)
        ·
          refine ⟨37877185509269371573186435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50502914012359162097581913 37877185509269371573186435)
          ·
            refine ⟨56815778263904057359779653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37877185509269371573186435 56815778263904057359779653)
            ·
              refine ⟨10652958424482010754958685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56815778263904057359779653 10652958424482010754958685)
              ·
                refine ⟨3994859409180754033109507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10652958424482010754958685 3994859409180754033109507)
                ·
                  refine ⟨5992289113771131049664261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3994859409180754033109507 5992289113771131049664261)
                  ·
                    refine ⟨1123554208832087071812049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5992289113771131049664261 1123554208832087071812049)
                    ·
                      rfl

theorem cell23_6564342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_6564342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564342 prefixEnd_6564342 := by exact prefixLift 6564342
  have htrace : WordTrace (prefixWord ++ tailWord_6564342) baseStart_6564342 baseEnd_6564342 := by
    simpa [prefixWord, tailWord_6564342, baseEnd_6564342] using wordTrace_append hprefix tailTrace_6564342
  have hstable : (prefixWord ++ tailWord_6564342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564342).length < 2 ^ (prefixWord ++ tailWord_6564342).sum := by decide
  have hdescent : baseEnd_6564342 < baseStart_6564342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564348 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 7, 1, 3]
def baseStart_6564348 : Nat := 118140960795 + 6564348 * 2 ^ 59
def prefixEnd_6564348 : Nat := 4983230072969 + 3 ^ 40 * 6564348 * 2
def baseEnd_6564348 : Nat := 3370665707380188191961119

theorem tailTrace_6564348 : CollatzResearch.WordTrace tailWord_6564348 prefixEnd_6564348 3370665707380188191961119 := by
  unfold tailWord_6564348
  simp only [CollatzResearch.WordTrace]
  refine ⟨119710720411247886114034849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159614293881663848152046465 119710720411247886114034849)
  ·
    refine ⟨89783040308435914585526137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119710720411247886114034849 89783040308435914585526137)
    ·
      refine ⟨67337280231326935939144603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89783040308435914585526137 67337280231326935939144603)
      ·
        refine ⟨101005920346990403908716905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67337280231326935939144603 101005920346990403908716905)
        ·
          refine ⟨75754440260242802931537679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101005920346990403908716905 75754440260242802931537679)
          ·
            refine ⟨113631660390364204397306519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75754440260242802931537679 113631660390364204397306519)
            ·
              refine ⟨170447490585546306595959779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113631660390364204397306519 170447490585546306595959779)
              ·
                refine ⟨255671235878319459893939669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170447490585546306595959779 255671235878319459893939669)
                ·
                  refine ⟨5992294590898112341264211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 255671235878319459893939669 5992294590898112341264211)
                  ·
                    refine ⟨8988441886347168511896317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5992294590898112341264211 8988441886347168511896317)
                    ·
                      refine ⟨3370665707380188191961119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8988441886347168511896317 3370665707380188191961119)
                      ·
                        rfl

theorem cell23_6564348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_6564348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564348 prefixEnd_6564348 := by exact prefixLift 6564348
  have htrace : WordTrace (prefixWord ++ tailWord_6564348) baseStart_6564348 baseEnd_6564348 := by
    simpa [prefixWord, tailWord_6564348, baseEnd_6564348] using wordTrace_append hprefix tailTrace_6564348
  have hstable : (prefixWord ++ tailWord_6564348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564348).length < 2 ^ (prefixWord ++ tailWord_6564348).sum := by decide
  have hdescent : baseEnd_6564348 < baseStart_6564348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564372 : List Nat := [2, 4, 3, 1, 1, 2, 3, 1, 6]
def baseStart_6564372 : Nat := 118140960795 + 6564372 * 2 ^ 59
def prefixEnd_6564372 : Nat := 4983230072969 + 3 ^ 40 * 6564372 * 2
def baseEnd_6564372 : Nat := 374519781212877344229001

theorem tailTrace_6564372 : CollatzResearch.WordTrace tailWord_6564372 prefixEnd_6564372 374519781212877344229001 := by
  unfold tailWord_6564372
  simp only [CollatzResearch.WordTrace]
  refine ⟨119711158087204412163471685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159614877449605882884628913 119711158087204412163471685)
  ·
    refine ⟨22445842141350827280650941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119711158087204412163471685 22445842141350827280650941)
    ·
      refine ⟨8417190803006560230244103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22445842141350827280650941 8417190803006560230244103)
      ·
        refine ⟨12625786204509840345366155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8417190803006560230244103 12625786204509840345366155)
        ·
          refine ⟨18938679306764760518049233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12625786204509840345366155 18938679306764760518049233)
          ·
            refine ⟨14204009480073570388536925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18938679306764760518049233 14204009480073570388536925)
            ·
              refine ⟨5326503555027588895701347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14204009480073570388536925 5326503555027588895701347)
              ·
                refine ⟨7989755332541383343552021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326503555027588895701347 7989755332541383343552021)
                ·
                  refine ⟨374519781212877344229001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7989755332541383343552021 374519781212877344229001)
                  ·
                    rfl

theorem cell23_6564372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_6564372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564372 prefixEnd_6564372 := by exact prefixLift 6564372
  have htrace : WordTrace (prefixWord ++ tailWord_6564372) baseStart_6564372 baseEnd_6564372 := by
    simpa [prefixWord, tailWord_6564372, baseEnd_6564372] using wordTrace_append hprefix tailTrace_6564372
  have hstable : (prefixWord ++ tailWord_6564372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564372).length < 2 ^ (prefixWord ++ tailWord_6564372).sum := by decide
  have hdescent : baseEnd_6564372 < baseStart_6564372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564408 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 1, 1, 5]
def baseStart_6564408 : Nat := 118140960795 + 6564408 * 2 ^ 59
def prefixEnd_6564408 : Nat := 4983230072969 + 3 ^ 40 * 6564408 * 2
def baseEnd_6564408 : Nat := 3370696516219457957210843

theorem tailTrace_6564408 : CollatzResearch.WordTrace tailWord_6564408 prefixEnd_6564408 3370696516219457957210843 := by
  unfold tailWord_6564408
  simp only [CollatzResearch.WordTrace]
  refine ⟨119711814601139201237626939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159615752801518934983502585 119711814601139201237626939)
  ·
    refine ⟨179567721901708801856440409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119711814601139201237626939 179567721901708801856440409)
    ·
      refine ⟨134675791426281601392330307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179567721901708801856440409 134675791426281601392330307)
      ·
        refine ⟨202013687139422402088495461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134675791426281601392330307 202013687139422402088495461)
        ·
          refine ⟨37877566338641700391592899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202013687139422402088495461 37877566338641700391592899)
          ·
            refine ⟨56816349507962550587389349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37877566338641700391592899 56816349507962550587389349)
            ·
              refine ⟨10653065532742978235135503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56816349507962550587389349 10653065532742978235135503)
              ·
                refine ⟨15979598299114467352703255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10653065532742978235135503 15979598299114467352703255)
                ·
                  refine ⟨23969397448671701029054883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15979598299114467352703255 23969397448671701029054883)
                  ·
                    refine ⟨35954096173007551543582325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23969397448671701029054883 35954096173007551543582325)
                    ·
                      refine ⟨3370696516219457957210843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35954096173007551543582325 3370696516219457957210843)
                      ·
                        rfl

theorem cell23_6564408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 1, 1, 5].length) (baseStart_6564408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564408 prefixEnd_6564408 := by exact prefixLift 6564408
  have htrace : WordTrace (prefixWord ++ tailWord_6564408) baseStart_6564408 baseEnd_6564408 := by
    simpa [prefixWord, tailWord_6564408, baseEnd_6564408] using wordTrace_append hprefix tailTrace_6564408
  have hstable : (prefixWord ++ tailWord_6564408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564408).length < 2 ^ (prefixWord ++ tailWord_6564408).sum := by decide
  have hdescent : baseEnd_6564408 < baseStart_6564408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564525 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_6564525 : Nat := 118140960795 + 6564525 * 2 ^ 59
def prefixEnd_6564525 : Nat := 4983230072969 + 3 ^ 40 * 6564525 * 2
def baseEnd_6564525 : Nat := 3370756593456033999447805

theorem tailTrace_6564525 : CollatzResearch.WordTrace tailWord_6564525 prefixEnd_6564525 3370756593456033999447805 := by
  unfold tailWord_6564525
  simp only [CollatzResearch.WordTrace]
  refine ⟨239427896542854531457263029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159618597695236354304842019 239427896542854531457263029)
  ·
    refine ⟨22446365300892612324118409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239427896542854531457263029 22446365300892612324118409)
    ·
      refine ⟨16834773975669459243088807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22446365300892612324118409 16834773975669459243088807)
      ·
        refine ⟨25252160963504188864633211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16834773975669459243088807 25252160963504188864633211)
        ·
          refine ⟨37878241445256283296949817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25252160963504188864633211 37878241445256283296949817)
          ·
            refine ⟨28408681083942212472712363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37878241445256283296949817 28408681083942212472712363)
            ·
              refine ⟨42613021625913318709068545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28408681083942212472712363 42613021625913318709068545)
              ·
                refine ⟨31959766219434989031801409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42613021625913318709068545 31959766219434989031801409)
                ·
                  refine ⟨23969824664576241773851057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31959766219434989031801409 23969824664576241773851057)
                  ·
                    refine ⟨17977368498432181330388293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23969824664576241773851057 17977368498432181330388293)
                    ·
                      refine ⟨3370756593456033999447805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17977368498432181330388293 3370756593456033999447805)
                      ·
                        rfl

theorem cell23_6564525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_6564525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564525 prefixEnd_6564525 := by exact prefixLift 6564525
  have htrace : WordTrace (prefixWord ++ tailWord_6564525) baseStart_6564525 baseEnd_6564525 := by
    simpa [prefixWord, tailWord_6564525, baseEnd_6564525] using wordTrace_append hprefix tailTrace_6564525
  have hstable : (prefixWord ++ tailWord_6564525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564525).length < 2 ^ (prefixWord ++ tailWord_6564525).sum := by decide
  have hdescent : baseEnd_6564525 < baseStart_6564525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564535 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 7]
def baseStart_6564535 : Nat := 118140960795 + 6564535 * 2 ^ 59
def prefixEnd_6564535 : Nat := 4983230072969 + 3 ^ 40 * 6564535 * 2
def baseEnd_6564535 : Nat := 374529080918064328924751

theorem tailTrace_6564535 : CollatzResearch.WordTrace tailWord_6564535 prefixEnd_6564535 374529080918064328924751 := by
  unfold tailWord_6564535
  simp only [CollatzResearch.WordTrace]
  refine ⟨239428261272818303165127059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159618840848545535443418039 239428261272818303165127059)
  ·
    refine ⟨359142391909227454747690589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239428261272818303165127059 359142391909227454747690589)
    ·
      refine ⟨134678396965960295530383971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359142391909227454747690589 134678396965960295530383971)
      ·
        refine ⟨202017595448940443295575957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134678396965960295530383971 202017595448940443295575957)
        ·
          refine ⟨9469574786669083279480123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 202017595448940443295575957 9469574786669083279480123)
          ·
            refine ⟨14204362180003624919220185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9469574786669083279480123 14204362180003624919220185)
            ·
              refine ⟨10653271635002718689415139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14204362180003624919220185 10653271635002718689415139)
              ·
                refine ⟨15979907452504078034122709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10653271635002718689415139 15979907452504078034122709)
                ·
                  refine ⟨374529080918064328924751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15979907452504078034122709 374529080918064328924751)
                  ·
                    rfl

theorem cell23_6564535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 7].length) (baseStart_6564535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564535 prefixEnd_6564535 := by exact prefixLift 6564535
  have htrace : WordTrace (prefixWord ++ tailWord_6564535) baseStart_6564535 baseEnd_6564535 := by
    simpa [prefixWord, tailWord_6564535, baseEnd_6564535] using wordTrace_append hprefix tailTrace_6564535
  have hstable : (prefixWord ++ tailWord_6564535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564535).length < 2 ^ (prefixWord ++ tailWord_6564535).sum := by decide
  have hdescent : baseEnd_6564535 < baseStart_6564535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564585 : List Nat := [1, 2, 1, 1, 1, 2, 4, 1, 4, 4, 2]
def baseStart_6564585 : Nat := 118140960795 + 6564585 * 2 ^ 59
def prefixEnd_6564585 : Nat := 4983230072969 + 3 ^ 40 * 6564585 * 2
def baseEnd_6564585 : Nat := 3370787402295303764697529

theorem tailTrace_6564585 : CollatzResearch.WordTrace tailWord_6564585 prefixEnd_6564585 3370787402295303764697529 := by
  unfold tailWord_6564585
  simp only [CollatzResearch.WordTrace]
  refine ⟨239430084922637161704447209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159620056615091441136298139 239430084922637161704447209)
  ·
    refine ⟨179572563691977871278335407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239430084922637161704447209 179572563691977871278335407)
    ·
      refine ⟨269358845537966806917503111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179572563691977871278335407 269358845537966806917503111)
      ·
        refine ⟨404038268306950210376254667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269358845537966806917503111 404038268306950210376254667)
        ·
          refine ⟨606057402460425315564382001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404038268306950210376254667 606057402460425315564382001)
          ·
            refine ⟨454543051845318986673286501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606057402460425315564382001 454543051845318986673286501)
            ·
              refine ⟨85226822220997310001241219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 454543051845318986673286501 85226822220997310001241219)
              ·
                refine ⟨127840233331495965001861829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85226822220997310001241219 127840233331495965001861829)
                ·
                  refine ⟨23970043749655493437849093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127840233331495965001861829 23970043749655493437849093)
                  ·
                    refine ⟨4494383203060405019596705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23970043749655493437849093 4494383203060405019596705)
                    ·
                      refine ⟨3370787402295303764697529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494383203060405019596705 3370787402295303764697529)
                      ·
                        rfl

theorem cell23_6564585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 4, 2].length) (baseStart_6564585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564585 prefixEnd_6564585 := by exact prefixLift 6564585
  have htrace : WordTrace (prefixWord ++ tailWord_6564585) baseStart_6564585 baseEnd_6564585 := by
    simpa [prefixWord, tailWord_6564585, baseEnd_6564585] using wordTrace_append hprefix tailTrace_6564585
  have hstable : (prefixWord ++ tailWord_6564585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564585).length < 2 ^ (prefixWord ++ tailWord_6564585).sum := by decide
  have hdescent : baseEnd_6564585 < baseStart_6564585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564597 : List Nat := [1, 3, 6, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6564597 : Nat := 118140960795 + 6564597 * 2 ^ 59
def prefixEnd_6564597 : Nat := 4983230072969 + 3 ^ 40 * 6564597 * 2
def baseEnd_6564597 : Nat := 3370793564063157717747475

theorem tailTrace_6564597 : CollatzResearch.WordTrace tailWord_6564597 prefixEnd_6564597 3370793564063157717747475 := by
  unfold tailWord_6564597
  simp only [CollatzResearch.WordTrace]
  refine ⟨239430522598593687753884045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159620348399062458502589363 239430522598593687753884045)
  ·
    refine ⟨89786445974472632907706517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239430522598593687753884045 89786445974472632907706517)
    ·
      refine ⟨4208739655053404667548743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 89786445974472632907706517 4208739655053404667548743)
      ·
        refine ⟨6313109482580107001323115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4208739655053404667548743 6313109482580107001323115)
        ·
          refine ⟨9469664223870160501984673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6313109482580107001323115 9469664223870160501984673)
          ·
            refine ⟨7102248167902620376488505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9469664223870160501984673 7102248167902620376488505)
            ·
              refine ⟨5326686125926965282366379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7102248167902620376488505 5326686125926965282366379)
              ·
                refine ⟨7990029188890447923549569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326686125926965282366379 7990029188890447923549569)
                ·
                  refine ⟨5992521891667835942662177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7990029188890447923549569 5992521891667835942662177)
                  ·
                    refine ⟨4494391418750876956996633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5992521891667835942662177 4494391418750876956996633)
                    ·
                      refine ⟨3370793564063157717747475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494391418750876956996633 3370793564063157717747475)
                      ·
                        rfl

theorem cell23_6564597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6564597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564597 prefixEnd_6564597 := by exact prefixLift 6564597
  have htrace : WordTrace (prefixWord ++ tailWord_6564597) baseStart_6564597 baseEnd_6564597 := by
    simpa [prefixWord, tailWord_6564597, baseEnd_6564597] using wordTrace_append hprefix tailTrace_6564597
  have hstable : (prefixWord ++ tailWord_6564597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564597).length < 2 ^ (prefixWord ++ tailWord_6564597).sum := by decide
  have hdescent : baseEnd_6564597 < baseStart_6564597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564605 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 3]
def baseStart_6564605 : Nat := 118140960795 + 6564605 * 2 ^ 59
def prefixEnd_6564605 : Nat := 4983230072969 + 3 ^ 40 * 6564605 * 2
def baseEnd_6564605 : Nat := 3370797671908393686447437

theorem tailTrace_6564605 : CollatzResearch.WordTrace tailWord_6564605 prefixEnd_6564605 3370797671908393686447437 := by
  unfold tailWord_6564605
  simp only [CollatzResearch.WordTrace]
  refine ⟨239430814382564705120175269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159620542921709803413450179 239430814382564705120175269)
  ·
    refine ⟨44893277696730882210032863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239430814382564705120175269 44893277696730882210032863)
    ·
      refine ⟨67339916545096323315049295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44893277696730882210032863 67339916545096323315049295)
      ·
        refine ⟨101009874817644484972573943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67339916545096323315049295 101009874817644484972573943)
        ·
          refine ⟨151514812226466727458860915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101009874817644484972573943 151514812226466727458860915)
          ·
            refine ⟨227272218339700091188291373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151514812226466727458860915 227272218339700091188291373)
            ·
              refine ⟨85227081877387534195609265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227272218339700091188291373 85227081877387534195609265)
              ·
                refine ⟨63920311408040650646706949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85227081877387534195609265 63920311408040650646706949)
                ·
                  refine ⟨11985058389007621996257553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63920311408040650646706949 11985058389007621996257553)
                  ·
                    refine ⟨8988793791755716497193165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11985058389007621996257553 8988793791755716497193165)
                    ·
                      refine ⟨3370797671908393686447437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8988793791755716497193165 3370797671908393686447437)
                      ·
                        rfl

theorem cell23_6564605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_6564605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564605 prefixEnd_6564605 := by exact prefixLift 6564605
  have htrace : WordTrace (prefixWord ++ tailWord_6564605) baseStart_6564605 baseEnd_6564605 := by
    simpa [prefixWord, tailWord_6564605, baseEnd_6564605] using wordTrace_append hprefix tailTrace_6564605
  have hstable : (prefixWord ++ tailWord_6564605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564605).length < 2 ^ (prefixWord ++ tailWord_6564605).sum := by decide
  have hdescent : baseEnd_6564605 < baseStart_6564605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564642 : List Nat := [3, 3, 1, 1, 2, 3, 2, 2, 6]
def baseStart_6564642 : Nat := 118140960795 + 6564642 * 2 ^ 59
def prefixEnd_6564642 : Nat := 4983230072969 + 3 ^ 40 * 6564642 * 2
def baseEnd_6564642 : Nat := 374535185632512226853863

theorem tailTrace_6564642 : CollatzResearch.WordTrace tailWord_6564642 prefixEnd_6564642 374535185632512226853863 := by
  unfold tailWord_6564642
  simp only [CollatzResearch.WordTrace]
  refine ⟨59858040970857665109818045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159621442588953773626181453 59858040970857665109818045)
  ·
    refine ⟨22446765364071624416181767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59858040970857665109818045 22446765364071624416181767)
    ·
      refine ⟨33670148046107436624272651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22446765364071624416181767 33670148046107436624272651)
      ·
        refine ⟨50505222069161154936408977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33670148046107436624272651 50505222069161154936408977)
        ·
          refine ⟨37878916551870866202306733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50505222069161154936408977 37878916551870866202306733)
          ·
            refine ⟨14204593706951574825865025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37878916551870866202306733 14204593706951574825865025)
            ·
              refine ⟨10653445280213681119398769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14204593706951574825865025 10653445280213681119398769)
              ·
                refine ⟨7990083960160260839549077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10653445280213681119398769 7990083960160260839549077)
                ·
                  refine ⟨374535185632512226853863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7990083960160260839549077 374535185632512226853863)
                  ·
                    rfl

theorem cell23_6564642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_6564642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564642 prefixEnd_6564642 := by exact prefixLift 6564642
  have htrace : WordTrace (prefixWord ++ tailWord_6564642) baseStart_6564642 baseEnd_6564642 := by
    simpa [prefixWord, tailWord_6564642, baseEnd_6564642] using wordTrace_append hprefix tailTrace_6564642
  have hstable : (prefixWord ++ tailWord_6564642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564642).length < 2 ^ (prefixWord ++ tailWord_6564642).sum := by decide
  have hdescent : baseEnd_6564642 < baseStart_6564642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564652 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 3]
def baseStart_6564652 : Nat := 118140960795 + 6564652 * 2 ^ 59
def prefixEnd_6564652 : Nat := 4983230072969 + 3 ^ 40 * 6564652 * 2
def baseEnd_6564652 : Nat := 3370821805499155002559721

theorem tailTrace_6564652 : CollatzResearch.WordTrace tailWord_6564652 prefixEnd_6564652 3370821805499155002559721 := by
  unfold tailWord_6564652
  simp only [CollatzResearch.WordTrace]
  refine ⟨119716264306697216073568105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159621685742262954764757473 119716264306697216073568105)
  ·
    refine ⟨89787198230022912055176079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119716264306697216073568105 89787198230022912055176079)
    ·
      refine ⟨134680797345034368082764119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89787198230022912055176079 134680797345034368082764119)
      ·
        refine ⟨202021196017551552124146179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134680797345034368082764119 202021196017551552124146179)
        ·
          refine ⟨303031794026327328186219269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202021196017551552124146179 303031794026327328186219269)
          ·
            refine ⟨56818461379936374034916113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303031794026327328186219269 56818461379936374034916113)
            ·
              refine ⟨42613846034952280526187085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56818461379936374034916113 42613846034952280526187085)
              ·
                refine ⟨15980192263107105197320157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42613846034952280526187085 15980192263107105197320157)
                ·
                  refine ⟨5992572098665164448995059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15980192263107105197320157 5992572098665164448995059)
                  ·
                    refine ⟨8988858147997746673492589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5992572098665164448995059 8988858147997746673492589)
                    ·
                      refine ⟨3370821805499155002559721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8988858147997746673492589 3370821805499155002559721)
                      ·
                        rfl

theorem cell23_6564652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 3].length) (baseStart_6564652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564652 prefixEnd_6564652 := by exact prefixLift 6564652
  have htrace : WordTrace (prefixWord ++ tailWord_6564652) baseStart_6564652 baseEnd_6564652 := by
    simpa [prefixWord, tailWord_6564652, baseEnd_6564652] using wordTrace_append hprefix tailTrace_6564652
  have hstable : (prefixWord ++ tailWord_6564652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564652).length < 2 ^ (prefixWord ++ tailWord_6564652).sum := by decide
  have hdescent : baseEnd_6564652 < baseStart_6564652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564673 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6564673 : Nat := 118140960795 + 6564673 * 2 ^ 59
def prefixEnd_6564673 : Nat := 4983230072969 + 3 ^ 40 * 6564673 * 2
def baseEnd_6564673 : Nat := 3370832588592899420397125

theorem tailTrace_6564673 : CollatzResearch.WordTrace tailWord_6564673 prefixEnd_6564673 3370832588592899420397125 := by
  unfold tailWord_6564673
  simp only [CollatzResearch.WordTrace]
  refine ⟨239433294546318352733650673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159622196364212235155767115 239433294546318352733650673)
  ·
    refine ⟨179574970909738764550238005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239433294546318352733650673 179574970909738764550238005)
    ·
      refine ⟨16835153522788009176584813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179574970909738764550238005 16835153522788009176584813)
      ·
        refine ⟨6313182571045503441219305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16835153522788009176584813 6313182571045503441219305)
        ·
          refine ⟨4734886928284127580914479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6313182571045503441219305 4734886928284127580914479)
          ·
            refine ⟨7102330392426191371371719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4734886928284127580914479 7102330392426191371371719)
            ·
              refine ⟨10653495588639287057057579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102330392426191371371719 10653495588639287057057579)
              ·
                refine ⟨15980243382958930585586369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10653495588639287057057579 15980243382958930585586369)
                ·
                  refine ⟨11985182537219197939189777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15980243382958930585586369 11985182537219197939189777)
                  ·
                    refine ⟨8988886902914398454392333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11985182537219197939189777 8988886902914398454392333)
                    ·
                      refine ⟨3370832588592899420397125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8988886902914398454392333 3370832588592899420397125)
                      ·
                        rfl

theorem cell23_6564673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6564673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564673 prefixEnd_6564673 := by exact prefixLift 6564673
  have htrace : WordTrace (prefixWord ++ tailWord_6564673) baseStart_6564673 baseEnd_6564673 := by
    simpa [prefixWord, tailWord_6564673, baseEnd_6564673] using wordTrace_append hprefix tailTrace_6564673
  have hstable : (prefixWord ++ tailWord_6564673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564673).length < 2 ^ (prefixWord ++ tailWord_6564673).sum := by decide
  have hdescent : baseEnd_6564673 < baseStart_6564673 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564675 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 4]
def baseStart_6564675 : Nat := 118140960795 + 6564675 * 2 ^ 59
def prefixEnd_6564675 : Nat := 4983230072969 + 3 ^ 40 * 6564675 * 2
def baseEnd_6564675 : Nat := 3370833615554208412572115

theorem tailTrace_6564675 : CollatzResearch.WordTrace tailWord_6564675 prefixEnd_6564675 3370833615554208412572115 := by
  unfold tailWord_6564675
  simp only [CollatzResearch.WordTrace]
  refine ⟨239433367492311107075223479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159622244994874071383482319 239433367492311107075223479)
  ·
    refine ⟨359150051238466660612835219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239433367492311107075223479 359150051238466660612835219)
    ·
      refine ⟨538725076857699990919252829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359150051238466660612835219 538725076857699990919252829)
      ·
        refine ⟨202021903821637496594719811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538725076857699990919252829 202021903821637496594719811)
        ·
          refine ⟨303032855732456244892079717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202021903821637496594719811 303032855732456244892079717)
          ·
            refine ⟨56818660449835545917264947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 303032855732456244892079717 56818660449835545917264947)
            ·
              refine ⟨85227990674753318875897421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56818660449835545917264947 85227990674753318875897421)
              ·
                refine ⟨31960496503032494578461533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85227990674753318875897421 31960496503032494578461533)
                ·
                  refine ⟨11985186188637185466923075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31960496503032494578461533 11985186188637185466923075)
                  ·
                    refine ⟨17977779282955778200384613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11985186188637185466923075 17977779282955778200384613)
                    ·
                      refine ⟨3370833615554208412572115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17977779282955778200384613 3370833615554208412572115)
                      ·
                        rfl

theorem cell23_6564675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_6564675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564675 prefixEnd_6564675 := by exact prefixLift 6564675
  have htrace : WordTrace (prefixWord ++ tailWord_6564675) baseStart_6564675 baseEnd_6564675 := by
    simpa [prefixWord, tailWord_6564675, baseEnd_6564675] using wordTrace_append hprefix tailTrace_6564675
  have hstable : (prefixWord ++ tailWord_6564675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564675).length < 2 ^ (prefixWord ++ tailWord_6564675).sum := by decide
  have hdescent : baseEnd_6564675 < baseStart_6564675 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564709 : List Nat := [1, 3, 1, 3, 1, 1, 3, 3, 3, 2, 2]
def baseStart_6564709 : Nat := 118140960795 + 6564709 * 2 ^ 59
def prefixEnd_6564709 : Nat := 4983230072969 + 3 ^ 40 * 6564709 * 2
def baseEnd_6564709 : Nat := 3370851073896461279546959

theorem tailTrace_6564709 : CollatzResearch.WordTrace tailWord_6564709 prefixEnd_6564709 3370851073896461279546959 := by
  unfold tailWord_6564709
  simp only [CollatzResearch.WordTrace]
  refine ⟨239434607574187930881961181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159623071716125287254640787 239434607574187930881961181)
  ·
    refine ⟨89787977840320474080735443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239434607574187930881961181 89787977840320474080735443)
    ·
      refine ⟨134681966760480711121103165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89787977840320474080735443 134681966760480711121103165)
      ·
        refine ⟨50505737535180266670413687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134681966760480711121103165 50505737535180266670413687)
        ·
          refine ⟨75758606302770400005620531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50505737535180266670413687 75758606302770400005620531)
          ·
            refine ⟨113637909454155600008430797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75758606302770400005620531 113637909454155600008430797)
            ·
              refine ⟨42614216045308350003161549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113637909454155600008430797 42614216045308350003161549)
              ·
                refine ⟨15980331016990631251185581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42614216045308350003161549 15980331016990631251185581)
                ·
                  refine ⟨5992624131371486719194593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15980331016990631251185581 5992624131371486719194593)
                  ·
                    refine ⟨4494468098528615039395945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5992624131371486719194593 4494468098528615039395945)
                    ·
                      refine ⟨3370851073896461279546959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494468098528615039395945 3370851073896461279546959)
                      ·
                        rfl

theorem cell23_6564709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_6564709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564709 prefixEnd_6564709 := by exact prefixLift 6564709
  have htrace : WordTrace (prefixWord ++ tailWord_6564709) baseStart_6564709 baseEnd_6564709 := by
    simpa [prefixWord, tailWord_6564709, baseEnd_6564709] using wordTrace_append hprefix tailTrace_6564709
  have hstable : (prefixWord ++ tailWord_6564709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564709).length < 2 ^ (prefixWord ++ tailWord_6564709).sum := by decide
  have hdescent : baseEnd_6564709 < baseStart_6564709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564712 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_6564712 : Nat := 118140960795 + 6564712 * 2 ^ 59
def prefixEnd_6564712 : Nat := 4983230072969 + 3 ^ 40 * 6564712 * 2
def baseEnd_6564712 : Nat := 3370852614338424767809445

theorem tailTrace_6564712 : CollatzResearch.WordTrace tailWord_6564712 prefixEnd_6564712 3370852614338424767809445 := by
  unfold tailWord_6564712
  simp only [CollatzResearch.WordTrace]
  refine ⟨119717358496588531197160195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159623144662118041596213593 119717358496588531197160195)
  ·
    refine ⟨179576037744882796795740293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119717358496588531197160195 179576037744882796795740293)
    ·
      refine ⟨33670507077165524399201305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179576037744882796795740293 33670507077165524399201305)
      ·
        refine ⟨25252880307874143299400979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33670507077165524399201305 25252880307874143299400979)
        ·
          refine ⟨37879320461811214949101469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25252880307874143299400979 37879320461811214949101469)
          ·
            refine ⟨14204745173179205605913051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37879320461811214949101469 14204745173179205605913051)
            ·
              refine ⟨21307117759768808408869577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14204745173179205605913051 21307117759768808408869577)
              ·
                refine ⟨15980338319826606306652183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21307117759768808408869577 15980338319826606306652183)
                ·
                  refine ⟨23970507479739909459978275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15980338319826606306652183 23970507479739909459978275)
                  ·
                    refine ⟨35955761219609864189967413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23970507479739909459978275 35955761219609864189967413)
                    ·
                      refine ⟨3370852614338424767809445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35955761219609864189967413 3370852614338424767809445)
                      ·
                        rfl

theorem cell23_6564712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_6564712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564712 prefixEnd_6564712 := by exact prefixLift 6564712
  have htrace : WordTrace (prefixWord ++ tailWord_6564712) baseStart_6564712 baseEnd_6564712 := by
    simpa [prefixWord, tailWord_6564712, baseEnd_6564712] using wordTrace_append hprefix tailTrace_6564712
  have hstable : (prefixWord ++ tailWord_6564712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564712).length < 2 ^ (prefixWord ++ tailWord_6564712).sum := by decide
  have hdescent : baseEnd_6564712 < baseStart_6564712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564722 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_6564722 : Nat := 118140960795 + 6564722 * 2 ^ 59
def prefixEnd_6564722 : Nat := 4983230072969 + 3 ^ 40 * 6564722 * 2
def baseEnd_6564722 : Nat := 3370857749144969728684399

theorem tailTrace_6564722 : CollatzResearch.WordTrace tailWord_6564722 prefixEnd_6564722 3370857749144969728684399 := by
  unfold tailWord_6564722
  simp only [CollatzResearch.WordTrace]
  refine ⟨59858770430785208525546105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159623387815427222734789613 59858770430785208525546105)
  ·
    refine ⟨44894077823088906394159579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59858770430785208525546105 44894077823088906394159579)
    ·
      refine ⟨67341116734633359591239369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44894077823088906394159579 67341116734633359591239369)
      ·
        refine ⟨50505837550975019693429527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67341116734633359591239369 50505837550975019693429527)
        ·
          refine ⟨75758756326462529540144291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50505837550975019693429527 75758756326462529540144291)
          ·
            refine ⟨113638134489693794310216437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75758756326462529540144291 113638134489693794310216437)
            ·
              refine ⟨10653575108408793216582791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113638134489693794310216437 10653575108408793216582791)
              ·
                refine ⟨15980362662613189824874187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10653575108408793216582791 15980362662613189824874187)
                ·
                  refine ⟨23970543993919784737311281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15980362662613189824874187 23970543993919784737311281)
                  ·
                    refine ⟨17977907995439838552983461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23970543993919784737311281 17977907995439838552983461)
                    ·
                      refine ⟨3370857749144969728684399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17977907995439838552983461 3370857749144969728684399)
                      ·
                        rfl

theorem cell23_6564722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_6564722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564722 prefixEnd_6564722 := by exact prefixLift 6564722
  have htrace : WordTrace (prefixWord ++ tailWord_6564722) baseStart_6564722 baseEnd_6564722 := by
    simpa [prefixWord, tailWord_6564722, baseEnd_6564722] using wordTrace_append hprefix tailTrace_6564722
  have hstable : (prefixWord ++ tailWord_6564722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564722).length < 2 ^ (prefixWord ++ tailWord_6564722).sum := by decide
  have hdescent : baseEnd_6564722 < baseStart_6564722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564726 : List Nat := [5, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6564726 : Nat := 118140960795 + 6564726 * 2 ^ 59
def prefixEnd_6564726 : Nat := 4983230072969 + 3 ^ 40 * 6564726 * 2
def baseEnd_6564726 : Nat := 3370859803067587713034381

theorem tailTrace_6564726 : CollatzResearch.WordTrace tailWord_6564726 prefixEnd_6564726 3370859803067587713034381 := by
  unfold tailWord_6564726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964701725945396424083127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159623485076750895190220021 14964701725945396424083127)
  ·
    refine ⟨22447052588918094636124691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14964701725945396424083127 22447052588918094636124691)
    ·
      refine ⟨33670578883377141954187037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22447052588918094636124691 33670578883377141954187037)
      ·
        refine ⟨12626467081266428232820139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33670578883377141954187037 12626467081266428232820139)
        ·
          refine ⟨18939700621899642349230209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12626467081266428232820139 18939700621899642349230209)
          ·
            refine ⟨14204775466424731761922657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18939700621899642349230209 14204775466424731761922657)
            ·
              refine ⟨10653581599818548821441993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14204775466424731761922657 10653581599818548821441993)
              ·
                refine ⟨7990186199863911616081495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10653581599818548821441993 7990186199863911616081495)
                ·
                  refine ⟨11985279299795867424122243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7990186199863911616081495 11985279299795867424122243)
                  ·
                    refine ⟨17977918949693801136183365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11985279299795867424122243 17977918949693801136183365)
                    ·
                      refine ⟨3370859803067587713034381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17977918949693801136183365 3370859803067587713034381)
                      ·
                        rfl

theorem cell23_6564726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6564726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564726 prefixEnd_6564726 := by exact prefixLift 6564726
  have htrace : WordTrace (prefixWord ++ tailWord_6564726) baseStart_6564726 baseEnd_6564726 := by
    simpa [prefixWord, tailWord_6564726, baseEnd_6564726] using wordTrace_append hprefix tailTrace_6564726
  have hstable : (prefixWord ++ tailWord_6564726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564726).length < 2 ^ (prefixWord ++ tailWord_6564726).sum := by decide
  have hdescent : baseEnd_6564726 < baseStart_6564726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564729 : List Nat := [1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 3]
def baseStart_6564729 : Nat := 118140960795 + 6564729 * 2 ^ 59
def prefixEnd_6564729 : Nat := 4983230072969 + 3 ^ 40 * 6564729 * 2
def baseEnd_6564729 : Nat := 3370861343509551201296867

theorem tailTrace_6564729 : CollatzResearch.WordTrace tailWord_6564729 prefixEnd_6564729 3370861343509551201296867 := by
  unfold tailWord_6564729
  simp only [CollatzResearch.WordTrace]
  refine ⟨239435337034115474297689241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159623558022743649531792827 239435337034115474297689241)
  ·
    refine ⟨179576502775586605723266931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239435337034115474297689241 179576502775586605723266931)
    ·
      refine ⟨269364754163379908584900397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179576502775586605723266931 269364754163379908584900397)
      ·
        refine ⟨101011782811267465719337649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269364754163379908584900397 101011782811267465719337649)
        ·
          refine ⟨75758837108450599289503237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101011782811267465719337649 75758837108450599289503237)
          ·
            refine ⟨14204781957834487366781857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75758837108450599289503237 14204781957834487366781857)
            ·
              refine ⟨10653586468375865525086393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14204781957834487366781857 10653586468375865525086393)
              ·
                refine ⟨7990189851281899143814795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10653586468375865525086393 7990189851281899143814795)
                ·
                  refine ⟨11985284776922848715722193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7990189851281899143814795 11985284776922848715722193)
                  ·
                    refine ⟨8988963582692136536791645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11985284776922848715722193 8988963582692136536791645)
                    ·
                      refine ⟨3370861343509551201296867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8988963582692136536791645 3370861343509551201296867)
                      ·
                        rfl

theorem cell23_6564729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_6564729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564729 prefixEnd_6564729 := by exact prefixLift 6564729
  have htrace : WordTrace (prefixWord ++ tailWord_6564729) baseStart_6564729 baseEnd_6564729 := by
    simpa [prefixWord, tailWord_6564729, baseEnd_6564729] using wordTrace_append hprefix tailTrace_6564729
  have hstable : (prefixWord ++ tailWord_6564729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564729).length < 2 ^ (prefixWord ++ tailWord_6564729).sum := by decide
  have hdescent : baseEnd_6564729 < baseStart_6564729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564743 : List Nat := [1, 1, 4, 2, 3, 1, 3, 3, 1, 2, 2]
def baseStart_6564743 : Nat := 118140960795 + 6564743 * 2 ^ 59
def prefixEnd_6564743 : Nat := 4983230072969 + 3 ^ 40 * 6564743 * 2
def baseEnd_6564743 : Nat := 3370868532238714146521803

theorem tailTrace_6564743 : CollatzResearch.WordTrace tailWord_6564743 prefixEnd_6564743 3370868532238714146521803 := by
  unfold tailWord_6564743
  simp only [CollatzResearch.WordTrace]
  refine ⟨239435847656064754688698883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159623898437376503125799255 239435847656064754688698883)
  ·
    refine ⟨359153771484097132033048325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239435847656064754688698883 359153771484097132033048325)
    ·
      refine ⟨67341332153268212256196561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359153771484097132033048325 67341332153268212256196561)
      ·
        refine ⟨50505999114951159192147421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67341332153268212256196561 50505999114951159192147421)
        ·
          refine ⟨18939749668106684697055283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50505999114951159192147421 18939749668106684697055283)
          ·
            refine ⟨28409624502160027045582925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18939749668106684697055283 28409624502160027045582925)
            ·
              refine ⟨10653609188310010142093597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28409624502160027045582925 10653609188310010142093597)
              ·
                refine ⟨3995103445616253803285099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10653609188310010142093597 3995103445616253803285099)
                ·
                  refine ⟨5992655168424380704927649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995103445616253803285099 5992655168424380704927649)
                  ·
                    refine ⟨4494491376318285528695737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5992655168424380704927649 4494491376318285528695737)
                    ·
                      refine ⟨3370868532238714146521803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494491376318285528695737 3370868532238714146521803)
                      ·
                        rfl

theorem cell23_6564743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_6564743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564743 prefixEnd_6564743 := by exact prefixLift 6564743
  have htrace : WordTrace (prefixWord ++ tailWord_6564743) baseStart_6564743 baseEnd_6564743 := by
    simpa [prefixWord, tailWord_6564743, baseEnd_6564743] using wordTrace_append hprefix tailTrace_6564743
  have hstable : (prefixWord ++ tailWord_6564743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564743).length < 2 ^ (prefixWord ++ tailWord_6564743).sum := by decide
  have hdescent : baseEnd_6564743 < baseStart_6564743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564759 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 3]
def baseStart_6564759 : Nat := 118140960795 + 6564759 * 2 ^ 59
def prefixEnd_6564759 : Nat := 4983230072969 + 3 ^ 40 * 6564759 * 2
def baseEnd_6564759 : Nat := 3370876747929186083921729

theorem tailTrace_6564759 : CollatzResearch.WordTrace tailWord_6564759 prefixEnd_6564759 3370876747929186083921729 := by
  unfold tailWord_6564759
  simp only [CollatzResearch.WordTrace]
  refine ⟨239436431224006789421281331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159624287482671192947520887 239436431224006789421281331)
  ·
    refine ⟨359154646836010184131921997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239436431224006789421281331 359154646836010184131921997)
    ·
      refine ⟨134682992563503819049470749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359154646836010184131921997 134682992563503819049470749)
      ·
        refine ⟨50506122211313932143551531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134682992563503819049470749 50506122211313932143551531)
        ·
          refine ⟨75759183316970898215327297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50506122211313932143551531 75759183316970898215327297)
          ·
            refine ⟨56819387487728173661495473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75759183316970898215327297 56819387487728173661495473)
            ·
              refine ⟨42614540615796130246121605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56819387487728173661495473 42614540615796130246121605)
              ·
                refine ⟨7990226365461774421147801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42614540615796130246121605 7990226365461774421147801)
                ·
                  refine ⟨5992669774096330815860851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7990226365461774421147801 5992669774096330815860851)
                  ·
                    refine ⟨8989004661144496223791277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5992669774096330815860851 8989004661144496223791277)
                    ·
                      refine ⟨3370876747929186083921729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989004661144496223791277 3370876747929186083921729)
                      ·
                        rfl

theorem cell23_6564759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_6564759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564759 prefixEnd_6564759 := by exact prefixLift 6564759
  have htrace : WordTrace (prefixWord ++ tailWord_6564759) baseStart_6564759 baseEnd_6564759 := by
    simpa [prefixWord, tailWord_6564759, baseEnd_6564759] using wordTrace_append hprefix tailTrace_6564759
  have hstable : (prefixWord ++ tailWord_6564759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564759).length < 2 ^ (prefixWord ++ tailWord_6564759).sum := by decide
  have hdescent : baseEnd_6564759 < baseStart_6564759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564799 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 4, 2, 2]
def baseStart_6564799 : Nat := 118140960795 + 6564799 * 2 ^ 59
def prefixEnd_6564799 : Nat := 4983230072969 + 3 ^ 40 * 6564799 * 2
def baseEnd_6564799 : Nat := 3370897287155365927421545

theorem tailTrace_6564799 : CollatzResearch.WordTrace tailWord_6564799 prefixEnd_6564799 3370897287155365927421545 := by
  unfold tailWord_6564799
  simp only [CollatzResearch.WordTrace]
  refine ⟨239437890143861876252737451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159625260095907917501824967 239437890143861876252737451)
  ·
    refine ⟨359156835215792814379106177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239437890143861876252737451 359156835215792814379106177)
    ·
      refine ⟨269367626411844610784329633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359156835215792814379106177 269367626411844610784329633)
      ·
        refine ⟨202025719808883458088247225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269367626411844610784329633 202025719808883458088247225)
        ·
          refine ⟨151519289856662593566185419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202025719808883458088247225 151519289856662593566185419)
          ·
            refine ⟨227278934784993890349278129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151519289856662593566185419 227278934784993890349278129)
            ·
              refine ⟨170459201088745417761958597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227278934784993890349278129 170459201088745417761958597)
              ·
                refine ⟨31961100204139765830367237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170459201088745417761958597 31961100204139765830367237)
                ·
                  refine ⟨5992706288276206093193857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31961100204139765830367237 5992706288276206093193857)
                  ·
                    refine ⟨4494529716207154569895393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5992706288276206093193857 4494529716207154569895393)
                    ·
                      refine ⟨3370897287155365927421545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494529716207154569895393 3370897287155365927421545)
                      ·
                        rfl

theorem cell23_6564799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_6564799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564799 prefixEnd_6564799 := by exact prefixLift 6564799
  have htrace : WordTrace (prefixWord ++ tailWord_6564799) baseStart_6564799 baseEnd_6564799 := by
    simpa [prefixWord, tailWord_6564799, baseEnd_6564799] using wordTrace_append hprefix tailTrace_6564799
  have hstable : (prefixWord ++ tailWord_6564799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564799).length < 2 ^ (prefixWord ++ tailWord_6564799).sum := by decide
  have hdescent : baseEnd_6564799 < baseStart_6564799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564812 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 2, 2, 4]
def baseStart_6564812 : Nat := 118140960795 + 6564812 * 2 ^ 59
def prefixEnd_6564812 : Nat := 4983230072969 + 3 ^ 40 * 6564812 * 2
def baseEnd_6564812 : Nat := 3370903962403874376558985

theorem tailTrace_6564812 : CollatzResearch.WordTrace tailWord_6564812 prefixEnd_6564812 3370903962403874376558985 := by
  unfold tailWord_6564812
  simp only [CollatzResearch.WordTrace]
  refine ⟨119719182146407389736480345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159625576195209852981973793 119719182146407389736480345)
  ·
    refine ⟨89789386609805542302360259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119719182146407389736480345 89789386609805542302360259)
    ·
      refine ⟨134684079914708313453540389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89789386609805542302360259 134684079914708313453540389)
      ·
        refine ⟨25253264984007808772538823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134684079914708313453540389 25253264984007808772538823)
        ·
          refine ⟨37879897476011713158808235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25253264984007808772538823 37879897476011713158808235)
          ·
            refine ⟨56819846214017569738212353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37879897476011713158808235 56819846214017569738212353)
            ·
              refine ⟨42614884660513177303659265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56819846214017569738212353 42614884660513177303659265)
              ·
                refine ⟨31961163495384882977744449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42614884660513177303659265 31961163495384882977744449)
                ·
                  refine ⟨23970872621538662233308337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31961163495384882977744449 23970872621538662233308337)
                  ·
                    refine ⟨17978154466153996674981253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23970872621538662233308337 17978154466153996674981253)
                    ·
                      refine ⟨3370903962403874376558985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17978154466153996674981253 3370903962403874376558985)
                      ·
                        rfl

theorem cell23_6564812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_6564812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564812 prefixEnd_6564812 := by exact prefixLift 6564812
  have htrace : WordTrace (prefixWord ++ tailWord_6564812) baseStart_6564812 baseEnd_6564812 := by
    simpa [prefixWord, tailWord_6564812, baseEnd_6564812] using wordTrace_append hprefix tailTrace_6564812
  have hstable : (prefixWord ++ tailWord_6564812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564812).length < 2 ^ (prefixWord ++ tailWord_6564812).sum := by decide
  have hdescent : baseEnd_6564812 < baseStart_6564812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564829 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6564829 : Nat := 118140960795 + 6564829 * 2 ^ 59
def prefixEnd_6564829 : Nat := 4983230072969 + 3 ^ 40 * 6564829 * 2
def baseEnd_6564829 : Nat := 3370912691575000810046407

theorem tailTrace_6564829 : CollatzResearch.WordTrace tailWord_6564829 prefixEnd_6564829 3370912691575000810046407 := by
  unfold tailWord_6564829
  simp only [CollatzResearch.WordTrace]
  refine ⟨239438984333753191376329541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159625989555835460917553027 239438984333753191376329541)
  ·
    refine ⟨44894809562578723383061789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239438984333753191376329541 44894809562578723383061789)
    ·
      refine ⟨16835553585967021268648171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44894809562578723383061789 16835553585967021268648171)
      ·
        refine ⟨25253330378950531902972257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16835553585967021268648171 25253330378950531902972257)
        ·
          refine ⟨18939997784212898927229193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25253330378950531902972257 18939997784212898927229193)
          ·
            refine ⟨14204998338159674195421895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18939997784212898927229193 14204998338159674195421895)
            ·
              refine ⟨21307497507239511293132843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14204998338159674195421895 21307497507239511293132843)
              ·
                refine ⟨31961246260859266939699265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21307497507239511293132843 31961246260859266939699265)
                ·
                  refine ⟨23970934695644450204774449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31961246260859266939699265 23970934695644450204774449)
                  ·
                    refine ⟨17978201021733337653580837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23970934695644450204774449 17978201021733337653580837)
                    ·
                      refine ⟨3370912691575000810046407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17978201021733337653580837 3370912691575000810046407)
                      ·
                        rfl

theorem cell23_6564829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6564829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564829 prefixEnd_6564829 := by exact prefixLift 6564829
  have htrace : WordTrace (prefixWord ++ tailWord_6564829) baseStart_6564829 baseEnd_6564829 := by
    simpa [prefixWord, tailWord_6564829, baseEnd_6564829] using wordTrace_append hprefix tailTrace_6564829
  have hstable : (prefixWord ++ tailWord_6564829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564829).length < 2 ^ (prefixWord ++ tailWord_6564829).sum := by decide
  have hdescent : baseEnd_6564829 < baseStart_6564829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564889 : List Nat := [1, 2, 1, 2, 1, 1, 6, 1, 2, 4, 2]
def baseStart_6564889 : Nat := 118140960795 + 6564889 * 2 ^ 59
def prefixEnd_6564889 : Nat := 4983230072969 + 3 ^ 40 * 6564889 * 2
def baseEnd_6564889 : Nat := 3370943500414270575296131

theorem tailTrace_6564889 : CollatzResearch.WordTrace tailWord_6564889 prefixEnd_6564889 3370943500414270575296131 := by
  unfold tailWord_6564889
  simp only [CollatzResearch.WordTrace]
  refine ⟨239441172713535821623513721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159627448475690547749009147 239441172713535821623513721)
  ·
    refine ⟨179580879535151866217635291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239441172713535821623513721 179580879535151866217635291)
    ·
      refine ⟨269371319302727799326452937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179580879535151866217635291 269371319302727799326452937)
      ·
        refine ⟨202028489477045849494839703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269371319302727799326452937 202028489477045849494839703)
        ·
          refine ⟨303042734215568774242259555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202028489477045849494839703 303042734215568774242259555)
          ·
            refine ⟨454564101323353161363389333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303042734215568774242259555 454564101323353161363389333)
            ·
              refine ⟨21307692249532179438908875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 454564101323353161363389333 21307692249532179438908875)
              ·
                refine ⟨31961538374298269158363313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21307692249532179438908875 31961538374298269158363313)
                ·
                  refine ⟨23971153780723701868772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31961538374298269158363313 23971153780723701868772485)
                  ·
                    refine ⟨4494591333885694100394841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23971153780723701868772485 4494591333885694100394841)
                    ·
                      refine ⟨3370943500414270575296131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494591333885694100394841 3370943500414270575296131)
                      ·
                        rfl

theorem cell23_6564889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_6564889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564889 prefixEnd_6564889 := by exact prefixLift 6564889
  have htrace : WordTrace (prefixWord ++ tailWord_6564889) baseStart_6564889 baseEnd_6564889 := by
    simpa [prefixWord, tailWord_6564889, baseEnd_6564889] using wordTrace_append hprefix tailTrace_6564889
  have hstable : (prefixWord ++ tailWord_6564889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564889).length < 2 ^ (prefixWord ++ tailWord_6564889).sum := by decide
  have hdescent : baseEnd_6564889 < baseStart_6564889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564899 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 3, 4]
def baseStart_6564899 : Nat := 118140960795 + 6564899 * 2 ^ 59
def prefixEnd_6564899 : Nat := 4983230072969 + 3 ^ 40 * 6564899 * 2
def baseEnd_6564899 : Nat := 1123649545073605178723695

theorem tailTrace_6564899 : CollatzResearch.WordTrace tailWord_6564899 prefixEnd_6564899 1123649545073605178723695 := by
  unfold tailWord_6564899
  simp only [CollatzResearch.WordTrace]
  refine ⟨239441537443499593331377751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159627691628999728887585167 239441537443499593331377751)
  ·
    refine ⟨359162306165249389997066627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239441537443499593331377751 359162306165249389997066627)
    ·
      refine ⟨538743459247874084995599941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359162306165249389997066627 538743459247874084995599941)
      ·
        refine ⟨101014398608976390936674989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 538743459247874084995599941 101014398608976390936674989)
        ·
          refine ⟨37880399478366146601253121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101014398608976390936674989 37880399478366146601253121)
          ·
            refine ⟨28410299608774609950939841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37880399478366146601253121 28410299608774609950939841)
            ·
              refine ⟨21307724706580957463204881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28410299608774609950939841 21307724706580957463204881)
              ·
                refine ⟨15980793529935718097403661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21307724706580957463204881 15980793529935718097403661)
                ·
                  refine ⟨5992797573725894286526373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15980793529935718097403661 5992797573725894286526373)
                  ·
                    refine ⟨1123649545073605178723695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5992797573725894286526373 1123649545073605178723695)
                    ·
                      rfl

theorem cell23_6564899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 3, 4].length) (baseStart_6564899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564899 prefixEnd_6564899 := by exact prefixLift 6564899
  have htrace : WordTrace (prefixWord ++ tailWord_6564899) baseStart_6564899 baseEnd_6564899 := by
    simpa [prefixWord, tailWord_6564899, baseEnd_6564899] using wordTrace_append hprefix tailTrace_6564899
  have hstable : (prefixWord ++ tailWord_6564899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564899).length < 2 ^ (prefixWord ++ tailWord_6564899).sum := by decide
  have hdescent : baseEnd_6564899 < baseStart_6564899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564926 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 4, 2, 3]
def baseStart_6564926 : Nat := 118140960795 + 6564926 * 2 ^ 59
def prefixEnd_6564926 : Nat := 4983230072969 + 3 ^ 40 * 6564926 * 2
def baseEnd_6564926 : Nat := 3370962499198486930533461

theorem tailTrace_6564926 : CollatzResearch.WordTrace tailWord_6564926 prefixEnd_6564926 3370962499198486930533461 := by
  unfold tailWord_6564926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29930315276800222117826329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159628348142934517961740421 29930315276800222117826329)
  ·
    refine ⟨22447736457600166588369747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29930315276800222117826329 22447736457600166588369747)
    ·
      refine ⟨33671604686400249882554621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22447736457600166588369747 33671604686400249882554621)
      ·
        refine ⟨12626851757400093705957983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33671604686400249882554621 12626851757400093705957983)
        ·
          refine ⟨18940277636100140558936975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12626851757400093705957983 18940277636100140558936975)
          ·
            refine ⟨28410416454150210838405463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18940277636100140558936975 28410416454150210838405463)
            ·
              refine ⟨42615624681225316257608195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28410416454150210838405463 42615624681225316257608195)
              ·
                refine ⟨63923437021837974386412293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42615624681225316257608195 63923437021837974386412293)
                ·
                  refine ⟨11985644441594620197452305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63923437021837974386412293 11985644441594620197452305)
                  ·
                    refine ⟨8989233331195965148089229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11985644441594620197452305 8989233331195965148089229)
                    ·
                      refine ⟨3370962499198486930533461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989233331195965148089229 3370962499198486930533461)
                      ·
                        rfl

theorem cell23_6564926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_6564926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564926 prefixEnd_6564926 := by exact prefixLift 6564926
  have htrace : WordTrace (prefixWord ++ tailWord_6564926) baseStart_6564926 baseEnd_6564926 := by
    simpa [prefixWord, tailWord_6564926, baseEnd_6564926] using wordTrace_append hprefix tailTrace_6564926
  have hstable : (prefixWord ++ tailWord_6564926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564926).length < 2 ^ (prefixWord ++ tailWord_6564926).sum := by decide
  have hdescent : baseEnd_6564926 < baseStart_6564926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564946 : List Nat := [3, 2, 2, 1, 3, 1, 4, 1, 6]
def baseStart_6564946 : Nat := 118140960795 + 6564946 * 2 ^ 59
def prefixEnd_6564946 : Nat := 4983230072969 + 3 ^ 40 * 6564946 * 2
def baseEnd_6564946 : Nat := 374552529867952983587041

theorem tailTrace_6564946 : CollatzResearch.WordTrace tailWord_6564946 prefixEnd_6564946 374552529867952983587041 := by
  unfold tailWord_6564946
  simp only [CollatzResearch.WordTrace]
  refine ⟨59860812918582330089584673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159628834449552880238892461 59860812918582330089584673)
  ·
    refine ⟨44895609688936747567188505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59860812918582330089584673 44895609688936747567188505)
    ·
      refine ⟨33671707266702560675391379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44895609688936747567188505 33671707266702560675391379)
      ·
        refine ⟨50507560900053841013087069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33671707266702560675391379 50507560900053841013087069)
        ·
          refine ⟨18940335337520190379907651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50507560900053841013087069 18940335337520190379907651)
          ·
            refine ⟨28410503006280285569861477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18940335337520190379907651 28410503006280285569861477)
            ·
              refine ⟨5326969313677553544349027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28410503006280285569861477 5326969313677553544349027)
              ·
                refine ⟨7990453970516330316523541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326969313677553544349027 7990453970516330316523541)
                ·
                  refine ⟨374552529867952983587041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7990453970516330316523541 374552529867952983587041)
                  ·
                    rfl

theorem cell23_6564946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 6].length) (baseStart_6564946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564946 prefixEnd_6564946 := by exact prefixLift 6564946
  have htrace : WordTrace (prefixWord ++ tailWord_6564946) baseStart_6564946 baseEnd_6564946 := by
    simpa [prefixWord, tailWord_6564946, baseEnd_6564946] using wordTrace_append hprefix tailTrace_6564946
  have hstable : (prefixWord ++ tailWord_6564946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564946).length < 2 ^ (prefixWord ++ tailWord_6564946).sum := by decide
  have hdescent : baseEnd_6564946 < baseStart_6564946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564956 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_6564956 : Nat := 118140960795 + 6564956 * 2 ^ 59
def prefixEnd_6564956 : Nat := 4983230072969 + 3 ^ 40 * 6564956 * 2
def baseEnd_6564956 : Nat := 3370977903618121813158323

theorem tailTrace_6564956 : CollatzResearch.WordTrace tailWord_6564956 prefixEnd_6564956 3370977903618121813158323 := by
  unfold tailWord_6564956
  simp only [CollatzResearch.WordTrace]
  refine ⟨119721808202146546033101361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159629077602862061377468481 119721808202146546033101361)
  ·
    refine ⟨89791356151609909524826021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119721808202146546033101361 89791356151609909524826021)
    ·
      refine ⟨16835879278426858035904879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89791356151609909524826021 16835879278426858035904879)
      ·
        refine ⟨25253818917640287053857319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16835879278426858035904879 25253818917640287053857319)
        ·
          refine ⟨37880728376460430580785979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25253818917640287053857319 37880728376460430580785979)
          ·
            refine ⟨56821092564690645871178969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37880728376460430580785979 56821092564690645871178969)
            ·
              refine ⟨42615819423517984403384227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56821092564690645871178969 42615819423517984403384227)
              ·
                refine ⟨63923729135276976605076341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42615819423517984403384227 63923729135276976605076341)
                ·
                  refine ⟨5992849606432216556725907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63923729135276976605076341 5992849606432216556725907)
                  ·
                    refine ⟨8989274409648324835088861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5992849606432216556725907 8989274409648324835088861)
                    ·
                      refine ⟨3370977903618121813158323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989274409648324835088861 3370977903618121813158323)
                      ·
                        rfl

theorem cell23_6564956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_6564956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564956 prefixEnd_6564956 := by exact prefixLift 6564956
  have htrace : WordTrace (prefixWord ++ tailWord_6564956) baseStart_6564956 baseEnd_6564956 := by
    simpa [prefixWord, tailWord_6564956, baseEnd_6564956] using wordTrace_append hprefix tailTrace_6564956
  have hstable : (prefixWord ++ tailWord_6564956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564956).length < 2 ^ (prefixWord ++ tailWord_6564956).sum := by decide
  have hdescent : baseEnd_6564956 < baseStart_6564956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564976 : List Nat := [2, 1, 1, 1, 5, 1, 5, 1, 1, 5]
def baseStart_6564976 : Nat := 118140960795 + 6564976 * 2 ^ 59
def prefixEnd_6564976 : Nat := 4983230072969 + 3 ^ 40 * 6564976 * 2
def baseEnd_6564976 : Nat := 1123662724410403911636077

theorem tailTrace_6564976 : CollatzResearch.WordTrace tailWord_6564976 prefixEnd_6564976 1123662724410403911636077 := by
  unfold tailWord_6564976
  simp only [CollatzResearch.WordTrace]
  refine ⟨119722172932110317740965391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159629563909480423654620521 119722172932110317740965391)
  ·
    refine ⟨179583259398165476611448087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119722172932110317740965391 179583259398165476611448087)
    ·
      refine ⟨269374889097248214917172131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179583259398165476611448087 269374889097248214917172131)
      ·
        refine ⟨404062333645872322375758197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269374889097248214917172131 404062333645872322375758197)
        ·
          refine ⟨37880843779300530222727331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404062333645872322375758197 37880843779300530222727331)
          ·
            refine ⟨56821265668950795334090997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37880843779300530222727331 56821265668950795334090997)
            ·
              refine ⟨5326993656464137062571031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56821265668950795334090997 5326993656464137062571031)
              ·
                refine ⟨7990490484696205593856547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5326993656464137062571031 7990490484696205593856547)
                ·
                  refine ⟨11985735727044308390784821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7990490484696205593856547 11985735727044308390784821)
                  ·
                    refine ⟨1123662724410403911636077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11985735727044308390784821 1123662724410403911636077)
                    ·
                      rfl

theorem cell23_6564976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 5, 1, 1, 5].length) (baseStart_6564976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564976 prefixEnd_6564976 := by exact prefixLift 6564976
  have htrace : WordTrace (prefixWord ++ tailWord_6564976) baseStart_6564976 baseEnd_6564976 := by
    simpa [prefixWord, tailWord_6564976, baseEnd_6564976] using wordTrace_append hprefix tailTrace_6564976
  have hstable : (prefixWord ++ tailWord_6564976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564976).length < 2 ^ (prefixWord ++ tailWord_6564976).sum := by decide
  have hdescent : baseEnd_6564976 < baseStart_6564976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6564992 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6]
def baseStart_6564992 : Nat := 118140960795 + 6564992 * 2 ^ 59
def prefixEnd_6564992 : Nat := 4983230072969 + 3 ^ 40 * 6564992 * 2
def baseEnd_6564992 : Nat := 3370996388921683672308157

theorem tailTrace_6564992 : CollatzResearch.WordTrace tailWord_6564992 prefixEnd_6564992 3370996388921683672308157 := by
  unfold tailWord_6564992
  simp only [CollatzResearch.WordTrace]
  refine ⟨119722464716081335107256615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159629952954775113476342153 119722464716081335107256615)
  ·
    refine ⟨179583697074122002660884923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119722464716081335107256615 179583697074122002660884923)
    ·
      refine ⟨269375545611183003991327385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179583697074122002660884923 269375545611183003991327385)
      ·
        refine ⟨202031659208387252993495539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269375545611183003991327385 202031659208387252993495539)
        ·
          refine ⟨303047488812580879490243309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202031659208387252993495539 303047488812580879490243309)
          ·
            refine ⟨113642808304717829808841241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303047488812580879490243309 113642808304717829808841241)
            ·
              refine ⟨85232106228538372356630931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113642808304717829808841241 85232106228538372356630931)
              ·
                refine ⟨127848159342807558534946397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85232106228538372356630931 127848159342807558534946397)
                ·
                  refine ⟨47943059753552834450604899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127848159342807558534946397 47943059753552834450604899)
                  ·
                    refine ⟨71914589630329251675907349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47943059753552834450604899 71914589630329251675907349)
                    ·
                      refine ⟨3370996388921683672308157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71914589630329251675907349 3370996388921683672308157)
                      ·
                        rfl

theorem cell23_6564992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_6564992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6564992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6564992 prefixEnd_6564992 := by exact prefixLift 6564992
  have htrace : WordTrace (prefixWord ++ tailWord_6564992) baseStart_6564992 baseEnd_6564992 := by
    simpa [prefixWord, tailWord_6564992, baseEnd_6564992] using wordTrace_append hprefix tailTrace_6564992
  have hstable : (prefixWord ++ tailWord_6564992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6564992).length < 2 ^ (prefixWord ++ tailWord_6564992).sum := by decide
  have hdescent : baseEnd_6564992 < baseStart_6564992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6564992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565006 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 1, 6]
def baseStart_6565006 : Nat := 118140960795 + 6565006 * 2 ^ 59
def prefixEnd_6565006 : Nat := 4983230072969 + 3 ^ 40 * 6565006 * 2
def baseEnd_6565006 : Nat := 1123667859216948872511031

theorem tailTrace_6565006 : CollatzResearch.WordTrace tailWord_6565006 prefixEnd_6565006 1123667859216948872511031 := by
  unfold tailWord_6565006
  simp only [CollatzResearch.WordTrace]
  refine ⟨29930680006763993825690359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159630293369407967070348581 29930680006763993825690359)
  ·
    refine ⟨44896020010145990738535539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29930680006763993825690359 44896020010145990738535539)
    ·
      refine ⟨67344030015218986107803309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44896020010145990738535539 67344030015218986107803309)
      ·
        refine ⟨25254011255707119790426241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67344030015218986107803309 25254011255707119790426241)
        ·
          refine ⟨18940508441780339842819681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25254011255707119790426241 18940508441780339842819681)
          ·
            refine ⟨14205381331335254882114761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18940508441780339842819681 14205381331335254882114761)
            ·
              refine ⟨10654035998501441161586071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14205381331335254882114761 10654035998501441161586071)
              ·
                refine ⟨15981053997752161742379107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10654035998501441161586071 15981053997752161742379107)
                ·
                  refine ⟨23971580996628242613568661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15981053997752161742379107 23971580996628242613568661)
                  ·
                    refine ⟨1123667859216948872511031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23971580996628242613568661 1123667859216948872511031)
                    ·
                      rfl

theorem cell23_6565006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_6565006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565006 prefixEnd_6565006 := by exact prefixLift 6565006
  have htrace : WordTrace (prefixWord ++ tailWord_6565006) baseStart_6565006 baseEnd_6565006 := by
    simpa [prefixWord, tailWord_6565006, baseEnd_6565006] using wordTrace_append hprefix tailTrace_6565006
  have hstable : (prefixWord ++ tailWord_6565006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565006).length < 2 ^ (prefixWord ++ tailWord_6565006).sum := by decide
  have hdescent : baseEnd_6565006 < baseStart_6565006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565016 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 3, 2, 3]
def baseStart_6565016 : Nat := 118140960795 + 6565016 * 2 ^ 59
def prefixEnd_6565016 : Nat := 4983230072969 + 3 ^ 40 * 6565016 * 2
def baseEnd_6565016 : Nat := 3371008712457391578408047

theorem tailTrace_6565016 : CollatzResearch.WordTrace tailWord_6565016 prefixEnd_6565016 3371008712457391578408047 := by
  unfold tailWord_6565016
  simp only [CollatzResearch.WordTrace]
  refine ⟨119722902392037861156693451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159630536522717148208924601 119722902392037861156693451)
  ·
    refine ⟨179584353588056791735040177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119722902392037861156693451 179584353588056791735040177)
    ·
      refine ⟨134688265191042593801280133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179584353588056791735040177 134688265191042593801280133)
      ·
        refine ⟨25254049723320486337740025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134688265191042593801280133 25254049723320486337740025)
        ·
          refine ⟨18940537292490364753305019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25254049723320486337740025 18940537292490364753305019)
          ·
            refine ⟨28410805938735547129957529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18940537292490364753305019 28410805938735547129957529)
            ·
              refine ⟨21308104454051660347468147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28410805938735547129957529 21308104454051660347468147)
              ·
                refine ⟨31962156681077490521202221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21308104454051660347468147 31962156681077490521202221)
                ·
                  refine ⟨11985808755404058945450833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31962156681077490521202221 11985808755404058945450833)
                  ·
                    refine ⟨8989356566553044209088125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11985808755404058945450833 8989356566553044209088125)
                    ·
                      refine ⟨3371008712457391578408047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989356566553044209088125 3371008712457391578408047)
                      ·
                        rfl

theorem cell23_6565016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_6565016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565016 prefixEnd_6565016 := by exact prefixLift 6565016
  have htrace : WordTrace (prefixWord ++ tailWord_6565016) baseStart_6565016 baseEnd_6565016 := by
    simpa [prefixWord, tailWord_6565016, baseEnd_6565016] using wordTrace_append hprefix tailTrace_6565016
  have hstable : (prefixWord ++ tailWord_6565016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565016).length < 2 ^ (prefixWord ++ tailWord_6565016).sum := by decide
  have hdescent : baseEnd_6565016 < baseStart_6565016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565060 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_6565060 : Nat := 118140960795 + 6565060 * 2 ^ 59
def prefixEnd_6565060 : Nat := 4983230072969 + 3 ^ 40 * 6565060 * 2
def baseEnd_6565060 : Nat := 3371031305606189406257845

theorem tailTrace_6565060 : CollatzResearch.WordTrace tailWord_6565060 prefixEnd_6565060 3371031305606189406257845 := by
  unfold tailWord_6565060
  simp only [CollatzResearch.WordTrace]
  refine ⟨119723704797958158913994317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159631606397277545218659089 119723704797958158913994317)
  ·
    refine ⟨44896389299234309592747869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119723704797958158913994317 44896389299234309592747869)
    ·
      refine ⟨16836145987212866097280451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44896389299234309592747869 16836145987212866097280451)
      ·
        refine ⟨25254218980819299145920677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16836145987212866097280451 25254218980819299145920677)
        ·
          refine ⟨4735166058903618589860127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25254218980819299145920677 4735166058903618589860127)
          ·
            refine ⟨7102749088355427884790191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735166058903618589860127 7102749088355427884790191)
            ·
              refine ⟨10654123632533141827185287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102749088355427884790191 10654123632533141827185287)
              ·
                refine ⟨15981185448799712740777931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10654123632533141827185287 15981185448799712740777931)
                ·
                  refine ⟨23971778173199569111166897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15981185448799712740777931 23971778173199569111166897)
                  ·
                    refine ⟨17978833629899676833375173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23971778173199569111166897 17978833629899676833375173)
                    ·
                      refine ⟨3371031305606189406257845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17978833629899676833375173 3371031305606189406257845)
                      ·
                        rfl

theorem cell23_6565060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_6565060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565060 prefixEnd_6565060 := by exact prefixLift 6565060
  have htrace : WordTrace (prefixWord ++ tailWord_6565060) baseStart_6565060 baseEnd_6565060 := by
    simpa [prefixWord, tailWord_6565060, baseEnd_6565060] using wordTrace_append hprefix tailTrace_6565060
  have hstable : (prefixWord ++ tailWord_6565060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565060).length < 2 ^ (prefixWord ++ tailWord_6565060).sum := by decide
  have hdescent : baseEnd_6565060 < baseStart_6565060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565089 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 5]
def baseStart_6565089 : Nat := 118140960795 + 6565089 * 2 ^ 59
def prefixEnd_6565089 : Nat := 4983230072969 + 3 ^ 40 * 6565089 * 2
def baseEnd_6565089 : Nat := 3371046196545169792795211

theorem tailTrace_6565089 : CollatzResearch.WordTrace tailWord_6565089 prefixEnd_6565089 3371046196545169792795211 := by
  unfold tailWord_6565089
  simp only [CollatzResearch.WordTrace]
  refine ⟨239448467312811255780794321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159632311541874170520529547 239448467312811255780794321)
  ·
    refine ⟨179586350484608441835595741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239448467312811255780794321 179586350484608441835595741)
    ·
      refine ⟨67344881431728165688348403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179586350484608441835595741 67344881431728165688348403)
      ·
        refine ⟨101017322147592248532522605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67344881431728165688348403 101017322147592248532522605)
        ·
          refine ⟨37881495805347093199695977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101017322147592248532522605 37881495805347093199695977)
          ·
            refine ⟨28411121854010319899771983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37881495805347093199695977 28411121854010319899771983)
            ·
              refine ⟨42616682781015479849657975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28411121854010319899771983 42616682781015479849657975)
              ·
                refine ⟨63925024171523219774486963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42616682781015479849657975 63925024171523219774486963)
                ·
                  refine ⟨95887536257284829661730445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63925024171523219774486963 95887536257284829661730445)
                  ·
                    refine ⟨35957826096481811123148917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95887536257284829661730445 35957826096481811123148917)
                    ·
                      refine ⟨3371046196545169792795211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35957826096481811123148917 3371046196545169792795211)
                      ·
                        rfl

theorem cell23_6565089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_6565089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565089 prefixEnd_6565089 := by exact prefixLift 6565089
  have htrace : WordTrace (prefixWord ++ tailWord_6565089) baseStart_6565089 baseEnd_6565089 := by
    simpa [prefixWord, tailWord_6565089, baseEnd_6565089] using wordTrace_append hprefix tailTrace_6565089
  have hstable : (prefixWord ++ tailWord_6565089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565089).length < 2 ^ (prefixWord ++ tailWord_6565089).sum := by decide
  have hdescent : baseEnd_6565089 < baseStart_6565089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565156 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_6565156 : Nat := 118140960795 + 6565156 * 2 ^ 59
def prefixEnd_6565156 : Nat := 4983230072969 + 3 ^ 40 * 6565156 * 2
def baseEnd_6565156 : Nat := 1123693533249673676885801

theorem tailTrace_6565156 : CollatzResearch.WordTrace tailWord_6565156 prefixEnd_6565156 1123693533249673676885801 := by
  unfold tailWord_6565156
  simp only [CollatzResearch.WordTrace]
  refine ⟨119725455501784263111741661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159633940669045684148988881 119725455501784263111741661)
  ·
    refine ⟨44897045813169098666903123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119725455501784263111741661 44897045813169098666903123)
    ·
      refine ⟨67345568719753648000354685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44897045813169098666903123 67345568719753648000354685)
      ·
        refine ⟨25254588269907618000133007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67345568719753648000354685 25254588269907618000133007)
        ·
          refine ⟨37881882404861427000199511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25254588269907618000133007 37881882404861427000199511)
          ·
            refine ⟨56822823607292140500299267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37881882404861427000199511 56822823607292140500299267)
            ·
              refine ⟨85234235410938210750448901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56822823607292140500299267 85234235410938210750448901)
              ·
                refine ⟨15981419139550914515709169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85234235410938210750448901 15981419139550914515709169)
                ·
                  refine ⟨11986064354663185886781877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15981419139550914515709169 11986064354663185886781877)
                  ·
                    refine ⟨1123693533249673676885801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11986064354663185886781877 1123693533249673676885801)
                    ·
                      rfl

theorem cell23_6565156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_6565156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565156 prefixEnd_6565156 := by exact prefixLift 6565156
  have htrace : WordTrace (prefixWord ++ tailWord_6565156) baseStart_6565156 baseEnd_6565156 := by
    simpa [prefixWord, tailWord_6565156, baseEnd_6565156] using wordTrace_append hprefix tailTrace_6565156
  have hstable : (prefixWord ++ tailWord_6565156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565156).length < 2 ^ (prefixWord ++ tailWord_6565156).sum := by decide
  have hdescent : baseEnd_6565156 < baseStart_6565156 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565160 : List Nat := [2, 1, 5, 1, 2, 1, 4, 2, 5]
def baseStart_6565160 : Nat := 118140960795 + 6565160 * 2 ^ 59
def prefixEnd_6565160 : Nat := 4983230072969 + 3 ^ 40 * 6565160 * 2
def baseEnd_6565160 : Nat := 374564739296848779445265

theorem tailTrace_6565160 : CollatzResearch.WordTrace tailWord_6565160 prefixEnd_6565160 374564739296848779445265 := by
  unfold tailWord_6565160
  simp only [CollatzResearch.WordTrace]
  refine ⟨119725528447777017453314467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159634037930369356604419289 119725528447777017453314467)
  ·
    refine ⟨179588292671665526179971701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119725528447777017453314467 179588292671665526179971701)
    ·
      refine ⟨16836402437968643079372347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 179588292671665526179971701 16836402437968643079372347)
      ·
        refine ⟨25254603656952964619058521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16836402437968643079372347 25254603656952964619058521)
        ·
          refine ⟨18940952742714723464293891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25254603656952964619058521 18940952742714723464293891)
          ·
            refine ⟨28411429114072085196440837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18940952742714723464293891 28411429114072085196440837)
            ·
              refine ⟨5327142958888515974332657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28411429114072085196440837 5327142958888515974332657)
              ·
                refine ⟨3995357219166386980749493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5327142958888515974332657 3995357219166386980749493)
                ·
                  refine ⟨374564739296848779445265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995357219166386980749493 374564739296848779445265)
                  ·
                    rfl

theorem cell23_6565160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 2, 5].length) (baseStart_6565160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565160 prefixEnd_6565160 := by exact prefixLift 6565160
  have htrace : WordTrace (prefixWord ++ tailWord_6565160) baseStart_6565160 baseEnd_6565160 := by
    simpa [prefixWord, tailWord_6565160, baseEnd_6565160] using wordTrace_append hprefix tailTrace_6565160
  have hstable : (prefixWord ++ tailWord_6565160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565160).length < 2 ^ (prefixWord ++ tailWord_6565160).sum := by decide
  have hdescent : baseEnd_6565160 < baseStart_6565160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565189 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 6]
def baseStart_6565189 : Nat := 118140960795 + 6565189 * 2 ^ 59
def prefixEnd_6565189 : Nat := 4983230072969 + 3 ^ 40 * 6565189 * 2
def baseEnd_6565189 : Nat := 3371097544610619401544751

theorem tailTrace_6565189 : CollatzResearch.WordTrace tailWord_6565189 prefixEnd_6565189 3371097544610619401544751 := by
  unfold tailWord_6565189
  simp only [CollatzResearch.WordTrace]
  refine ⟨239452114612448972859434621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159634743074965981906289747 239452114612448972859434621)
  ·
    refine ⟨89794542979668364822287983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239452114612448972859434621 89794542979668364822287983)
    ·
      refine ⟨134691814469502547233431975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89794542979668364822287983 134691814469502547233431975)
      ·
        refine ⟨202037721704253820850147963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134691814469502547233431975 202037721704253820850147963)
        ·
          refine ⟨303056582556380731275221945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202037721704253820850147963 303056582556380731275221945)
          ·
            refine ⟨227292436917285548456416459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303056582556380731275221945 227292436917285548456416459)
            ·
              refine ⟨340938655375928322684624689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227292436917285548456416459 340938655375928322684624689)
              ·
                refine ⟨255703991531946242013468517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340938655375928322684624689 255703991531946242013468517)
                ·
                  refine ⟨47944498412239920377525347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255703991531946242013468517 47944498412239920377525347)
                  ·
                    refine ⟨71916747618359880566288021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47944498412239920377525347 71916747618359880566288021)
                    ·
                      refine ⟨3371097544610619401544751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71916747618359880566288021 3371097544610619401544751)
                      ·
                        rfl

theorem cell23_6565189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_6565189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565189 prefixEnd_6565189 := by exact prefixLift 6565189
  have htrace : WordTrace (prefixWord ++ tailWord_6565189) baseStart_6565189 baseEnd_6565189 := by
    simpa [prefixWord, tailWord_6565189, baseEnd_6565189] using wordTrace_append hprefix tailTrace_6565189
  have hstable : (prefixWord ++ tailWord_6565189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565189).length < 2 ^ (prefixWord ++ tailWord_6565189).sum := by decide
  have hdescent : baseEnd_6565189 < baseStart_6565189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565216 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 8]
def baseStart_6565216 : Nat := 118140960795 + 6565216 * 2 ^ 59
def prefixEnd_6565216 : Nat := 4983230072969 + 3 ^ 40 * 6565216 * 2
def baseEnd_6565216 : Nat := 374567934287587866211903

theorem tailTrace_6565216 : CollatzResearch.WordTrace tailWord_6565216 prefixEnd_6565216 374567934287587866211903 := by
  unfold tailWord_6565216
  simp only [CollatzResearch.WordTrace]
  refine ⟨119726549691675578235333751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159635399588900770980445001 119726549691675578235333751)
  ·
    refine ⟨179589824537513367353000627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119726549691675578235333751 179589824537513367353000627)
    ·
      refine ⟨269384736806270051029500941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179589824537513367353000627 269384736806270051029500941)
      ·
        refine ⟨101019276302351269136062853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269384736806270051029500941 101019276302351269136062853)
        ·
          refine ⟨18941114306690862963011785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101019276302351269136062853 18941114306690862963011785)
          ·
            refine ⟨14205835730018147222258839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18941114306690862963011785 14205835730018147222258839)
            ·
              refine ⟨21308753595027220833388259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14205835730018147222258839 21308753595027220833388259)
              ·
                refine ⟨31963130392540831250082389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21308753595027220833388259 31963130392540831250082389)
                ·
                  refine ⟨374567934287587866211903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31963130392540831250082389 374567934287587866211903)
                  ·
                    rfl

theorem cell23_6565216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 8].length) (baseStart_6565216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565216 prefixEnd_6565216 := by exact prefixLift 6565216
  have htrace : WordTrace (prefixWord ++ tailWord_6565216) baseStart_6565216 baseEnd_6565216 := by
    simpa [prefixWord, tailWord_6565216, baseEnd_6565216] using wordTrace_append hprefix tailTrace_6565216
  have hstable : (prefixWord ++ tailWord_6565216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565216).length < 2 ^ (prefixWord ++ tailWord_6565216).sum := by decide
  have hdescent : baseEnd_6565216 < baseStart_6565216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565220 : List Nat := [2, 3, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_6565220 : Nat := 118140960795 + 6565220 * 2 ^ 59
def prefixEnd_6565220 : Nat := 4983230072969 + 3 ^ 40 * 6565220 * 2
def baseEnd_6565220 : Nat := 1123704487503636260085703

theorem tailTrace_6565220 : CollatzResearch.WordTrace tailWord_6565220 prefixEnd_6565220 1123704487503636260085703 := by
  unfold tailWord_6565220
  simp only [CollatzResearch.WordTrace]
  refine ⟨119726622637668332576906557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159635496850224443435875409 119726622637668332576906557)
  ·
    refine ⟨44897483489125624716339959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119726622637668332576906557 44897483489125624716339959)
    ·
      refine ⟨67346225233688437074509939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44897483489125624716339959 67346225233688437074509939)
      ·
        refine ⟨101019337850532655611764909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67346225233688437074509939 101019337850532655611764909)
        ·
          refine ⟨37882251693949745854411841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101019337850532655611764909 37882251693949745854411841)
          ·
            refine ⟨28411688770462309390808881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37882251693949745854411841 28411688770462309390808881)
            ·
              refine ⟨21308766577846732043106661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28411688770462309390808881 21308766577846732043106661)
              ·
                refine ⟨3995393733346262258082499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21308766577846732043106661 3995393733346262258082499)
                ·
                  refine ⟨5993090600019393387123749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995393733346262258082499 5993090600019393387123749)
                  ·
                    refine ⟨1123704487503636260085703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993090600019393387123749 1123704487503636260085703)
                    ·
                      rfl

theorem cell23_6565220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_6565220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565220 prefixEnd_6565220 := by exact prefixLift 6565220
  have htrace : WordTrace (prefixWord ++ tailWord_6565220) baseStart_6565220 baseEnd_6565220 := by
    simpa [prefixWord, tailWord_6565220, baseEnd_6565220] using wordTrace_append hprefix tailTrace_6565220
  have hstable : (prefixWord ++ tailWord_6565220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565220).length < 2 ^ (prefixWord ++ tailWord_6565220).sum := by decide
  have hdescent : baseEnd_6565220 < baseStart_6565220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565243 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 3]
def baseStart_6565243 : Nat := 118140960795 + 6565243 * 2 ^ 59
def prefixEnd_6565243 : Nat := 4983230072969 + 3 ^ 40 * 6565243 * 2
def baseEnd_6565243 : Nat := 3371125272565962190269503

theorem tailTrace_6565243 : CollatzResearch.WordTrace tailWord_6565243 prefixEnd_6565243 3371125272565962190269503 := by
  unfold tailWord_6565243
  simp only [CollatzResearch.WordTrace]
  refine ⟨239454084154253340081900383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159636056102835560054600255 239454084154253340081900383)
  ·
    refine ⟨359181126231380010122850575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239454084154253340081900383 359181126231380010122850575)
    ·
      refine ⟨538771689347070015184275863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359181126231380010122850575 538771689347070015184275863)
      ·
        refine ⟨808157534020605022776413795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538771689347070015184275863 808157534020605022776413795)
        ·
          refine ⟨1212236301030907534164620693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808157534020605022776413795 1212236301030907534164620693)
          ·
            refine ⟨56823576610823790663966595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1212236301030907534164620693 56823576610823790663966595)
            ·
              refine ⟨85235364916235685995949893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56823576610823790663966595 85235364916235685995949893)
              ·
                refine ⟨15981630921794191124240605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85235364916235685995949893 15981630921794191124240605)
                ·
                  refine ⟨5993111595672821671590227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15981630921794191124240605 5993111595672821671590227)
                  ·
                    refine ⟨8989667393509232507385341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5993111595672821671590227 8989667393509232507385341)
                    ·
                      refine ⟨3371125272565962190269503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989667393509232507385341 3371125272565962190269503)
                      ·
                        rfl

theorem cell23_6565243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 3, 1, 3].length) (baseStart_6565243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565243 prefixEnd_6565243 := by exact prefixLift 6565243
  have htrace : WordTrace (prefixWord ++ tailWord_6565243) baseStart_6565243 baseEnd_6565243 := by
    simpa [prefixWord, tailWord_6565243, baseEnd_6565243] using wordTrace_append hprefix tailTrace_6565243
  have hstable : (prefixWord ++ tailWord_6565243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565243).length < 2 ^ (prefixWord ++ tailWord_6565243).sum := by decide
  have hdescent : baseEnd_6565243 < baseStart_6565243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565253 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 1, 5, 2]
def baseStart_6565253 : Nat := 118140960795 + 6565253 * 2 ^ 59
def prefixEnd_6565253 : Nat := 4983230072969 + 3 ^ 40 * 6565253 * 2
def baseEnd_6565253 : Nat := 3371130407372507151144457

theorem tailTrace_6565253 : CollatzResearch.WordTrace tailWord_6565253 prefixEnd_6565253 3371130407372507151144457 := by
  unfold tailWord_6565253
  simp only [CollatzResearch.WordTrace]
  refine ⟨239454448884217111789764413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159636299256144741193176275 239454448884217111789764413)
  ·
    refine ⟨89795418331581416921161655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239454448884217111789764413 89795418331581416921161655)
    ·
      refine ⟨134693127497372125381742483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89795418331581416921161655 134693127497372125381742483)
      ·
        refine ⟨202039691246058188072613725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134693127497372125381742483 202039691246058188072613725)
        ·
          refine ⟨75764884217271820527230147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202039691246058188072613725 75764884217271820527230147)
          ·
            refine ⟨113647326325907730790845221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75764884217271820527230147 113647326325907730790845221)
            ·
              refine ⟨21308873686107699523283479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113647326325907730790845221 21308873686107699523283479)
              ·
                refine ⟨31963310529161549284925219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21308873686107699523283479 31963310529161549284925219)
                ·
                  refine ⟨47944965793742323927387829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31963310529161549284925219 47944965793742323927387829)
                  ·
                    refine ⟨4494840543163342868192609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47944965793742323927387829 4494840543163342868192609)
                    ·
                      refine ⟨3371130407372507151144457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494840543163342868192609 3371130407372507151144457)
                      ·
                        rfl

theorem cell23_6565253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 5, 2].length) (baseStart_6565253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565253 prefixEnd_6565253 := by exact prefixLift 6565253
  have htrace : WordTrace (prefixWord ++ tailWord_6565253) baseStart_6565253 baseEnd_6565253 := by
    simpa [prefixWord, tailWord_6565253, baseEnd_6565253] using wordTrace_append hprefix tailTrace_6565253
  have hstable : (prefixWord ++ tailWord_6565253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565253).length < 2 ^ (prefixWord ++ tailWord_6565253).sum := by decide
  have hdescent : baseEnd_6565253 < baseStart_6565253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565277 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 3]
def baseStart_6565277 : Nat := 118140960795 + 6565277 * 2 ^ 59
def prefixEnd_6565277 : Nat := 4983230072969 + 3 ^ 40 * 6565277 * 2
def baseEnd_6565277 : Nat := 3371142730908215057244347

theorem tailTrace_6565277 : CollatzResearch.WordTrace tailWord_6565277 prefixEnd_6565277 3371142730908215057244347 := by
  unfold tailWord_6565277
  simp only [CollatzResearch.WordTrace]
  refine ⟨239455324236130163888638085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159636882824086775925758723 239455324236130163888638085)
  ·
    refine ⟨44897873294274405729119641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239455324236130163888638085 44897873294274405729119641)
    ·
      refine ⟨33673404970705804296839731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44897873294274405729119641 33673404970705804296839731)
      ·
        refine ⟨50510107456058706445259597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33673404970705804296839731 50510107456058706445259597)
        ·
          refine ⟨18941290296022014916972349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50510107456058706445259597 18941290296022014916972349)
          ·
            refine ⟨7102983861008255593864631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18941290296022014916972349 7102983861008255593864631)
            ·
              refine ⟨10654475791512383390796947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7102983861008255593864631 10654475791512383390796947)
              ·
                refine ⟨15981713687268575086195421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10654475791512383390796947 15981713687268575086195421)
                ·
                  refine ⟨5993142632725715657323283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15981713687268575086195421 5993142632725715657323283)
                  ·
                    refine ⟨8989713949088573485984925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5993142632725715657323283 8989713949088573485984925)
                    ·
                      refine ⟨3371142730908215057244347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989713949088573485984925 3371142730908215057244347)
                      ·
                        rfl

theorem cell23_6565277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_6565277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565277 prefixEnd_6565277 := by exact prefixLift 6565277
  have htrace : WordTrace (prefixWord ++ tailWord_6565277) baseStart_6565277 baseEnd_6565277 := by
    simpa [prefixWord, tailWord_6565277, baseEnd_6565277] using wordTrace_append hprefix tailTrace_6565277
  have hstable : (prefixWord ++ tailWord_6565277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565277).length < 2 ^ (prefixWord ++ tailWord_6565277).sum := by decide
  have hdescent : baseEnd_6565277 < baseStart_6565277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565303 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3]
def baseStart_6565303 : Nat := 118140960795 + 6565303 * 2 ^ 59
def prefixEnd_6565303 : Nat := 4983230072969 + 3 ^ 40 * 6565303 * 2
def baseEnd_6565303 : Nat := 3371156081405231955519227

theorem tailTrace_6565303 : CollatzResearch.WordTrace tailWord_6565303 prefixEnd_6565303 3371156081405231955519227 := by
  unfold tailWord_6565303
  simp only [CollatzResearch.WordTrace]
  refine ⟨239456272534035970329084563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159637515022690646886056375 239456272534035970329084563)
  ·
    refine ⟨359184408801053955493626845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239456272534035970329084563 359184408801053955493626845)
    ·
      refine ⟨134694153300395233310110067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359184408801053955493626845 134694153300395233310110067)
      ·
        refine ⟨202041229950592849965165101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134694153300395233310110067 202041229950592849965165101)
        ·
          refine ⟨75765461231472318736936913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202041229950592849965165101 75765461231472318736936913)
          ·
            refine ⟨56824095923604239052702685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75765461231472318736936913 56824095923604239052702685)
            ·
              refine ⟨21309035971351589644763507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56824095923604239052702685 21309035971351589644763507)
              ·
                refine ⟨31963553957027384467145261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21309035971351589644763507 31963553957027384467145261)
                ·
                  refine ⟨11986332733885269175179473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31963553957027384467145261 11986332733885269175179473)
                  ·
                    refine ⟨8989749550413951881384605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11986332733885269175179473 8989749550413951881384605)
                    ·
                      refine ⟨3371156081405231955519227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989749550413951881384605 3371156081405231955519227)
                      ·
                        rfl

theorem cell23_6565303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 2, 3].length) (baseStart_6565303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565303 prefixEnd_6565303 := by exact prefixLift 6565303
  have htrace : WordTrace (prefixWord ++ tailWord_6565303) baseStart_6565303 baseEnd_6565303 := by
    simpa [prefixWord, tailWord_6565303, baseEnd_6565303] using wordTrace_append hprefix tailTrace_6565303
  have hstable : (prefixWord ++ tailWord_6565303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565303).length < 2 ^ (prefixWord ++ tailWord_6565303).sum := by decide
  have hdescent : baseEnd_6565303 < baseStart_6565303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565333 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_6565333 : Nat := 118140960795 + 6565333 * 2 ^ 59
def prefixEnd_6565333 : Nat := 4983230072969 + 3 ^ 40 * 6565333 * 2
def baseEnd_6565333 : Nat := 3371171485824866838144089

theorem tailTrace_6565333 : CollatzResearch.WordTrace tailWord_6565333 prefixEnd_6565333 3371171485824866838144089 := by
  unfold tailWord_6565333
  simp only [CollatzResearch.WordTrace]
  refine ⟨239457366723927285452676653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159638244482618190301784435 239457366723927285452676653)
  ·
    refine ⟨89796512521472732044753745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239457366723927285452676653 89796512521472732044753745)
    ·
      refine ⟨67347384391104549033565309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89796512521472732044753745 67347384391104549033565309)
      ·
        refine ⟨25255269146664205887586991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67347384391104549033565309 25255269146664205887586991)
        ·
          refine ⟨37882903719996308831380487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25255269146664205887586991 37882903719996308831380487)
          ·
            refine ⟨56824355579994463247070731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37882903719996308831380487 56824355579994463247070731)
            ·
              refine ⟨85236533369991694870606097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56824355579994463247070731 85236533369991694870606097)
              ·
                refine ⟨63927400027493771152954573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85236533369991694870606097 63927400027493771152954573)
                ·
                  refine ⟨23972775010310164182357965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63927400027493771152954573 23972775010310164182357965)
                  ·
                    refine ⟨8989790628866311568384237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23972775010310164182357965 8989790628866311568384237)
                    ·
                      refine ⟨3371171485824866838144089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989790628866311568384237 3371171485824866838144089)
                      ·
                        rfl

theorem cell23_6565333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_6565333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565333 prefixEnd_6565333 := by exact prefixLift 6565333
  have htrace : WordTrace (prefixWord ++ tailWord_6565333) baseStart_6565333 baseEnd_6565333 := by
    simpa [prefixWord, tailWord_6565333, baseEnd_6565333] using wordTrace_append hprefix tailTrace_6565333
  have hstable : (prefixWord ++ tailWord_6565333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565333).length < 2 ^ (prefixWord ++ tailWord_6565333).sum := by decide
  have hdescent : baseEnd_6565333 < baseStart_6565333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565336 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 2, 7]
def baseStart_6565336 : Nat := 118140960795 + 6565336 * 2 ^ 59
def prefixEnd_6565336 : Nat := 4983230072969 + 3 ^ 40 * 6565336 * 2
def baseEnd_6565336 : Nat := 1123724342088943442135525

theorem tailTrace_6565336 : CollatzResearch.WordTrace tailWord_6565336 prefixEnd_6565336 1123724342088943442135525 := by
  unfold tailWord_6565336
  simp only [CollatzResearch.WordTrace]
  refine ⟨119728738071458208482517931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159638317428610944643357241 119728738071458208482517931)
  ·
    refine ⟨179593107107187312723776897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119728738071458208482517931 179593107107187312723776897)
    ·
      refine ⟨134694830330390484542832673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179593107107187312723776897 134694830330390484542832673)
      ·
        refine ⟨101021122747792863407124505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134694830330390484542832673 101021122747792863407124505)
        ·
          refine ⟨75765842060844647555343379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101021122747792863407124505 75765842060844647555343379)
          ·
            refine ⟨113648763091266971333015069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75765842060844647555343379 113648763091266971333015069)
            ·
              refine ⟨42618286159225114249880651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113648763091266971333015069 42618286159225114249880651)
              ·
                refine ⟨63927429238837671374820977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42618286159225114249880651 63927429238837671374820977)
                ·
                  refine ⟨47945571929128253531115733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63927429238837671374820977 47945571929128253531115733)
                  ·
                    refine ⟨1123724342088943442135525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47945571929128253531115733 1123724342088943442135525)
                    ·
                      rfl

theorem cell23_6565336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_6565336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565336 prefixEnd_6565336 := by exact prefixLift 6565336
  have htrace : WordTrace (prefixWord ++ tailWord_6565336) baseStart_6565336 baseEnd_6565336 := by
    simpa [prefixWord, tailWord_6565336, baseEnd_6565336] using wordTrace_append hprefix tailTrace_6565336
  have hstable : (prefixWord ++ tailWord_6565336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565336).length < 2 ^ (prefixWord ++ tailWord_6565336).sum := by decide
  have hdescent : baseEnd_6565336 < baseStart_6565336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565360 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 3, 3, 2]
def baseStart_6565360 : Nat := 118140960795 + 6565360 * 2 ^ 59
def prefixEnd_6565360 : Nat := 4983230072969 + 3 ^ 40 * 6565360 * 2
def baseEnd_6565360 : Nat := 3371185349802538232506465

theorem tailTrace_6565360 : CollatzResearch.WordTrace tailWord_6565360 prefixEnd_6565360 3371185349802538232506465 := by
  unfold tailWord_6565360
  simp only [CollatzResearch.WordTrace]
  refine ⟨119729175747414734531954767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159638900996552979375939689 119729175747414734531954767)
  ·
    refine ⟨179593763621122101797932151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119729175747414734531954767 179593763621122101797932151)
    ·
      refine ⟨269390645431683152696898227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179593763621122101797932151 269390645431683152696898227)
      ·
        refine ⟨404085968147524729045347341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269390645431683152696898227 404085968147524729045347341)
        ·
          refine ⟨151532238055321773392005253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 404085968147524729045347341 151532238055321773392005253)
          ·
            refine ⟨28412294635372832511000985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151532238055321773392005253 28412294635372832511000985)
            ·
              refine ⟨21309220976529624383250739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28412294635372832511000985 21309220976529624383250739)
              ·
                refine ⟨31963831464794436574876109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21309220976529624383250739 31963831464794436574876109)
                ·
                  refine ⟨11986436799297913715578541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31963831464794436574876109 11986436799297913715578541)
                  ·
                    refine ⟨4494913799736717643341953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11986436799297913715578541 4494913799736717643341953)
                    ·
                      refine ⟨3371185349802538232506465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494913799736717643341953 3371185349802538232506465)
                      ·
                        rfl

theorem cell23_6565360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 3, 3, 2].length) (baseStart_6565360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565360 prefixEnd_6565360 := by exact prefixLift 6565360
  have htrace : WordTrace (prefixWord ++ tailWord_6565360) baseStart_6565360 baseEnd_6565360 := by
    simpa [prefixWord, tailWord_6565360, baseEnd_6565360] using wordTrace_append hprefix tailTrace_6565360
  have hstable : (prefixWord ++ tailWord_6565360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565360).length < 2 ^ (prefixWord ++ tailWord_6565360).sum := by decide
  have hdescent : baseEnd_6565360 < baseStart_6565360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565383 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 2, 6]
def baseStart_6565383 : Nat := 118140960795 + 6565383 * 2 ^ 59
def prefixEnd_6565383 : Nat := 4983230072969 + 3 ^ 40 * 6565383 * 2
def baseEnd_6565383 : Nat := 1123732386619197214172953

theorem tailTrace_6565383 : CollatzResearch.WordTrace tailWord_6565383 prefixEnd_6565383 1123732386619197214172953 := by
  unfold tailWord_6565383
  simp only [CollatzResearch.WordTrace]
  refine ⟨239459190373746143991996803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159639460249164095994664535 239459190373746143991996803)
  ·
    refine ⟨359188785560619215987995205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239459190373746143991996803 359188785560619215987995205)
    ·
      refine ⟨67347897292616102997749101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359188785560619215987995205 67347897292616102997749101)
      ·
        refine ⟨25255461484731038624155913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67347897292616102997749101 25255461484731038624155913)
        ·
          refine ⟨18941596113548278968116935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25255461484731038624155913 18941596113548278968116935)
          ·
            refine ⟨28412394170322418452175403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18941596113548278968116935 28412394170322418452175403)
            ·
              refine ⟨42618591255483627678263105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28412394170322418452175403 42618591255483627678263105)
              ·
                refine ⟨31963943441612720758697329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42618591255483627678263105 31963943441612720758697329)
                ·
                  refine ⟨23972957581209540569022997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31963943441612720758697329 23972957581209540569022997)
                  ·
                    refine ⟨1123732386619197214172953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23972957581209540569022997 1123732386619197214172953)
                    ·
                      rfl

theorem cell23_6565383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_6565383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565383 prefixEnd_6565383 := by exact prefixLift 6565383
  have htrace : WordTrace (prefixWord ++ tailWord_6565383) baseStart_6565383 baseEnd_6565383 := by
    simpa [prefixWord, tailWord_6565383, baseEnd_6565383] using wordTrace_append hprefix tailTrace_6565383
  have hstable : (prefixWord ++ tailWord_6565383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565383).length < 2 ^ (prefixWord ++ tailWord_6565383).sum := by decide
  have hdescent : baseEnd_6565383 < baseStart_6565383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565407 : List Nat := [1, 1, 2, 4, 1, 1, 2, 5, 2, 2, 2]
def baseStart_6565407 : Nat := 118140960795 + 6565407 * 2 ^ 59
def prefixEnd_6565407 : Nat := 4983230072969 + 3 ^ 40 * 6565407 * 2
def baseEnd_6565407 : Nat := 3371209483393299548618749

theorem tailTrace_6565407 : CollatzResearch.WordTrace tailWord_6565407 prefixEnd_6565407 3371209483393299548618749 := by
  unfold tailWord_6565407
  simp only [CollatzResearch.WordTrace]
  refine ⟨239460065725659196090870475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159640043817106130727246983 239460065725659196090870475)
  ·
    refine ⟨359190098588488794136305713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239460065725659196090870475 359190098588488794136305713)
    ·
      refine ⟨269392573941366595602229285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359190098588488794136305713 269392573941366595602229285)
      ·
        refine ⟨50511107614006236675417991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269392573941366595602229285 50511107614006236675417991)
        ·
          refine ⟨75766661421009355013126987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50511107614006236675417991 75766661421009355013126987)
          ·
            refine ⟨113649992131514032519690481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75766661421009355013126987 113649992131514032519690481)
            ·
              refine ⟨85237494098635524389767861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113649992131514032519690481 85237494098635524389767861)
              ·
                refine ⟨7991015071747080411540737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85237494098635524389767861 7991015071747080411540737)
                ·
                  refine ⟨5993261303810310308655553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7991015071747080411540737 5993261303810310308655553)
                  ·
                    refine ⟨4494945977857732731491665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5993261303810310308655553 4494945977857732731491665)
                    ·
                      refine ⟨3371209483393299548618749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494945977857732731491665 3371209483393299548618749)
                      ·
                        rfl

theorem cell23_6565407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_6565407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565407 prefixEnd_6565407 := by exact prefixLift 6565407
  have htrace : WordTrace (prefixWord ++ tailWord_6565407) baseStart_6565407 baseEnd_6565407 := by
    simpa [prefixWord, tailWord_6565407, baseEnd_6565407] using wordTrace_append hprefix tailTrace_6565407
  have hstable : (prefixWord ++ tailWord_6565407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565407).length < 2 ^ (prefixWord ++ tailWord_6565407).sum := by decide
  have hdescent : baseEnd_6565407 < baseStart_6565407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565447 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 7]
def baseStart_6565447 : Nat := 118140960795 + 6565447 * 2 ^ 59
def prefixEnd_6565447 : Nat := 4983230072969 + 3 ^ 40 * 6565447 * 2
def baseEnd_6565447 : Nat := 374581113624386599124285

theorem tailTrace_6565447 : CollatzResearch.WordTrace tailWord_6565447 prefixEnd_6565447 374581113624386599124285 := by
  unfold tailWord_6565447
  simp only [CollatzResearch.WordTrace]
  refine ⟨239461524645514282922326595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159641016430342855281551063 239461524645514282922326595)
  ·
    refine ⟨359192286968271424383489893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239461524645514282922326595 359192286968271424383489893)
    ·
      refine ⟨67348553806550892071904355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359192286968271424383489893 67348553806550892071904355)
      ·
        refine ⟨101022830709826338107856533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67348553806550892071904355 101022830709826338107856533)
        ·
          refine ⟨4735445189523109598805775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101022830709826338107856533 4735445189523109598805775)
          ·
            refine ⟨7103167784284664398208663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735445189523109598805775 7103167784284664398208663)
            ·
              refine ⟨10654751676426996597312995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103167784284664398208663 10654751676426996597312995)
              ·
                refine ⟨15982127514640494895969493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10654751676426996597312995 15982127514640494895969493)
                ·
                  refine ⟨374581113624386599124285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15982127514640494895969493 374581113624386599124285)
                  ·
                    rfl

theorem cell23_6565447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 7].length) (baseStart_6565447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565447 prefixEnd_6565447 := by exact prefixLift 6565447
  have htrace : WordTrace (prefixWord ++ tailWord_6565447) baseStart_6565447 baseEnd_6565447 := by
    simpa [prefixWord, tailWord_6565447, baseEnd_6565447] using wordTrace_append hprefix tailTrace_6565447
  have hstable : (prefixWord ++ tailWord_6565447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565447).length < 2 ^ (prefixWord ++ tailWord_6565447).sum := by decide
  have hdescent : baseEnd_6565447 < baseStart_6565447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565450 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_6565450 : Nat := 118140960795 + 6565450 * 2 ^ 59
def prefixEnd_6565450 : Nat := 4983230072969 + 3 ^ 40 * 6565450 * 2
def baseEnd_6565450 : Nat := 3371231563061442880381051

theorem tailTrace_6565450 : CollatzResearch.WordTrace tailWord_6565450 prefixEnd_6565450 3371231563061442880381051 := by
  unfold tailWord_6565450
  simp only [CollatzResearch.WordTrace]
  refine ⟨59865408516125853608671451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159641089376335609623123869 59865408516125853608671451)
  ·
    refine ⟨89798112774188780413007177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59865408516125853608671451 89798112774188780413007177)
    ·
      refine ⟨67348584580641585309755383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89798112774188780413007177 67348584580641585309755383)
      ·
        refine ⟨101022876870962377964633075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67348584580641585309755383 101022876870962377964633075)
        ·
          refine ⟨151534315306443566946949613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101022876870962377964633075 151534315306443566946949613)
          ·
            refine ⟨56825368239916337605106105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151534315306443566946949613 56825368239916337605106105)
            ·
              refine ⟨42619026179937253203829579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56825368239916337605106105 42619026179937253203829579)
              ·
                refine ⟨63928539269905879805744369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42619026179937253203829579 63928539269905879805744369)
                ·
                  refine ⟨47946404452429409854308277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63928539269905879805744369 47946404452429409854308277)
                  ·
                    refine ⟨4494975417415257173841401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47946404452429409854308277 4494975417415257173841401)
                    ·
                      refine ⟨3371231563061442880381051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4494975417415257173841401 3371231563061442880381051)
                      ·
                        rfl

theorem cell23_6565450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_6565450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565450 prefixEnd_6565450 := by exact prefixLift 6565450
  have htrace : WordTrace (prefixWord ++ tailWord_6565450) baseStart_6565450 baseEnd_6565450 := by
    simpa [prefixWord, tailWord_6565450, baseEnd_6565450] using wordTrace_append hprefix tailTrace_6565450
  have hstable : (prefixWord ++ tailWord_6565450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565450).length < 2 ^ (prefixWord ++ tailWord_6565450).sum := by decide
  have hdescent : baseEnd_6565450 < baseStart_6565450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565483 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 3]
def baseStart_6565483 : Nat := 118140960795 + 6565483 * 2 ^ 59
def prefixEnd_6565483 : Nat := 4983230072969 + 3 ^ 40 * 6565483 * 2
def baseEnd_6565483 : Nat := 3371248507923041251268399

theorem tailTrace_6565483 : CollatzResearch.WordTrace tailWord_6565483 prefixEnd_6565483 3371248507923041251268399 := by
  unfold tailWord_6565483
  simp only [CollatzResearch.WordTrace]
  refine ⟨239462837673383861070637103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159641891782255907380424735 239462837673383861070637103)
  ·
    refine ⟨359194256510075791605955655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239462837673383861070637103 359194256510075791605955655)
    ·
      refine ⟨538791384765113687408933483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359194256510075791605955655 538791384765113687408933483)
      ·
        refine ⟨808187077147670531113400225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538791384765113687408933483 808187077147670531113400225)
        ·
          refine ⟨606140307860752898335050169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808187077147670531113400225 606140307860752898335050169)
          ·
            refine ⟨454605230895564673751287627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606140307860752898335050169 454605230895564673751287627)
            ·
              refine ⟨681907846343347010626931441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454605230895564673751287627 681907846343347010626931441)
              ·
                refine ⟨511430884757510257970198581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 681907846343347010626931441 511430884757510257970198581)
                ·
                  refine ⟨47946645446016586684706117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 511430884757510257970198581 47946645446016586684706117)
                  ·
                    refine ⟨8989996021128110003382397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47946645446016586684706117 8989996021128110003382397)
                    ·
                      refine ⟨3371248507923041251268399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8989996021128110003382397 3371248507923041251268399)
                      ·
                        rfl

theorem cell23_6565483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 4, 3].length) (baseStart_6565483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565483 prefixEnd_6565483 := by exact prefixLift 6565483
  have htrace : WordTrace (prefixWord ++ tailWord_6565483) baseStart_6565483 baseEnd_6565483 := by
    simpa [prefixWord, tailWord_6565483, baseEnd_6565483] using wordTrace_append hprefix tailTrace_6565483
  have hstable : (prefixWord ++ tailWord_6565483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565483).length < 2 ^ (prefixWord ++ tailWord_6565483).sum := by decide
  have hdescent : baseEnd_6565483 < baseStart_6565483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565524 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_6565524 : Nat := 118140960795 + 6565524 * 2 ^ 59
def prefixEnd_6565524 : Nat := 4983230072969 + 3 ^ 40 * 6565524 * 2
def baseEnd_6565524 : Nat := 1123756520209958530285237

theorem tailTrace_6565524 : CollatzResearch.WordTrace tailWord_6565524 prefixEnd_6565524 1123756520209958530285237 := by
  unfold tailWord_6565524
  simp only [CollatzResearch.WordTrace]
  refine ⟨119732166533117662536439813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159642888710823550048586417 119732166533117662536439813)
  ·
    refine ⟨22449781224959561725582465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119732166533117662536439813 22449781224959561725582465)
    ·
      refine ⟨16837335918719671294186849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22449781224959561725582465 16837335918719671294186849)
      ·
        refine ⟨12628001939039753470640137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16837335918719671294186849 12628001939039753470640137)
        ·
          refine ⟨9471001454279815102980103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12628001939039753470640137 9471001454279815102980103)
          ·
            refine ⟨14206502181419722654470155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9471001454279815102980103 14206502181419722654470155)
            ·
              refine ⟨21309753272129583981705233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14206502181419722654470155 21309753272129583981705233)
              ·
                refine ⟨15982314954097187986278925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21309753272129583981705233 15982314954097187986278925)
                ·
                  refine ⟨5993368107786445494854597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15982314954097187986278925 5993368107786445494854597)
                  ·
                    refine ⟨1123756520209958530285237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993368107786445494854597 1123756520209958530285237)
                    ·
                      rfl

theorem cell23_6565524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_6565524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565524 prefixEnd_6565524 := by exact prefixLift 6565524
  have htrace : WordTrace (prefixWord ++ tailWord_6565524) baseStart_6565524 baseEnd_6565524 := by
    simpa [prefixWord, tailWord_6565524, baseEnd_6565524] using wordTrace_append hprefix tailTrace_6565524
  have hstable : (prefixWord ++ tailWord_6565524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565524).length < 2 ^ (prefixWord ++ tailWord_6565524).sum := by decide
  have hdescent : baseEnd_6565524 < baseStart_6565524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565534 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_6565534 : Nat := 118140960795 + 6565534 * 2 ^ 59
def prefixEnd_6565534 : Nat := 4983230072969 + 3 ^ 40 * 6565534 * 2
def baseEnd_6565534 : Nat := 3371274695436420551730665

theorem tailTrace_6565534 : CollatzResearch.WordTrace tailWord_6565534 prefixEnd_6565534 3371274695436420551730665 := by
  unfold tailWord_6565534
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933087224524887097592957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159643131864132731187162437 29933087224524887097592957)
  ·
    refine ⟨11224907709196832661597359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29933087224524887097592957 11224907709196832661597359)
    ·
      refine ⟨16837361563795248992396039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11224907709196832661597359 16837361563795248992396039)
      ·
        refine ⟨25256042345692873488594059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16837361563795248992396039 25256042345692873488594059)
        ·
          refine ⟨37884063518539310232891089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25256042345692873488594059 37884063518539310232891089)
          ·
            refine ⟨28413047638904482674668317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37884063518539310232891089 28413047638904482674668317)
            ·
              refine ⟨10654892864589181003000619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28413047638904482674668317 10654892864589181003000619)
              ·
                refine ⟨15982339296883771504500929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10654892864589181003000619 15982339296883771504500929)
                ·
                  refine ⟨11986754472662828628375697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15982339296883771504500929 11986754472662828628375697)
                  ·
                    refine ⟨8990065854497121471281773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11986754472662828628375697 8990065854497121471281773)
                    ·
                      refine ⟨3371274695436420551730665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8990065854497121471281773 3371274695436420551730665)
                      ·
                        rfl

theorem cell23_6565534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_6565534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565534 prefixEnd_6565534 := by exact prefixLift 6565534
  have htrace : WordTrace (prefixWord ++ tailWord_6565534) baseStart_6565534 baseEnd_6565534 := by
    simpa [prefixWord, tailWord_6565534, baseEnd_6565534] using wordTrace_append hprefix tailTrace_6565534
  have hstable : (prefixWord ++ tailWord_6565534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565534).length < 2 ^ (prefixWord ++ tailWord_6565534).sum := by decide
  have hdescent : baseEnd_6565534 < baseStart_6565534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565563 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 3, 6]
def baseStart_6565563 : Nat := 118140960795 + 6565563 * 2 ^ 59
def prefixEnd_6565563 : Nat := 4983230072969 + 3 ^ 40 * 6565563 * 2
def baseEnd_6565563 : Nat := 1123763195458466979422677

theorem tailTrace_6565563 : CollatzResearch.WordTrace tailWord_6565563 prefixEnd_6565563 1123763195458466979422677 := by
  unfold tailWord_6565563
  simp only [CollatzResearch.WordTrace]
  refine ⟨239465755513094034733549343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159643837008729356489032895 239465755513094034733549343)
  ·
    refine ⟨359198633269641052100324015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239465755513094034733549343 359198633269641052100324015)
    ·
      refine ⟨538797949904461578150486023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359198633269641052100324015 538797949904461578150486023)
      ·
        refine ⟨808196924856692367225729035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538797949904461578150486023 808196924856692367225729035)
        ·
          refine ⟨1212295387285038550838593553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808196924856692367225729035 1212295387285038550838593553)
          ·
            refine ⟨909221540463778913128945165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212295387285038550838593553 909221540463778913128945165)
            ·
              refine ⟨340958077673917092423354437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 909221540463778913128945165 340958077673917092423354437)
              ·
                refine ⟨63929639563859454829378957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 340958077673917092423354437 63929639563859454829378957)
                ·
                  refine ⟨23973614836447295561017109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63929639563859454829378957 23973614836447295561017109)
                  ·
                    refine ⟨1123763195458466979422677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23973614836447295561017109 1123763195458466979422677)
                    ·
                      rfl

theorem cell23_6565563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_6565563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565563 prefixEnd_6565563 := by exact prefixLift 6565563
  have htrace : WordTrace (prefixWord ++ tailWord_6565563) baseStart_6565563 baseEnd_6565563 := by
    simpa [prefixWord, tailWord_6565563, baseEnd_6565563] using wordTrace_append hprefix tailTrace_6565563
  have hstable : (prefixWord ++ tailWord_6565563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565563).length < 2 ^ (prefixWord ++ tailWord_6565563).sum := by decide
  have hdescent : baseEnd_6565563 < baseStart_6565563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565564 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 3, 1, 3]
def baseStart_6565564 : Nat := 118140960795 + 6565564 * 2 ^ 59
def prefixEnd_6565564 : Nat := 4983230072969 + 3 ^ 40 * 6565564 * 2
def baseEnd_6565564 : Nat := 3371290099856055434355527

theorem tailTrace_6565564 : CollatzResearch.WordTrace tailWord_6565564 prefixEnd_6565564 3371290099856055434355527 := by
  unfold tailWord_6565564
  simp only [CollatzResearch.WordTrace]
  refine ⟨119732895993045205952167873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159643861324060274602890497 119732895993045205952167873)
  ·
    refine ⟨89799671994783904464125905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119732895993045205952167873 89799671994783904464125905)
    ·
      refine ⟨67349753996087928348094429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89799671994783904464125905 67349753996087928348094429)
      ·
        refine ⟨25256157748532973130535411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67349753996087928348094429 25256157748532973130535411)
        ·
          refine ⟨37884236622799459695803117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25256157748532973130535411 37884236622799459695803117)
          ·
            refine ⟨14206588733549797385926169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37884236622799459695803117 14206588733549797385926169)
            ·
              refine ⟨10654941550162348039444627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14206588733549797385926169 10654941550162348039444627)
              ·
                refine ⟨15982412325243522059166941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10654941550162348039444627 15982412325243522059166941)
                ·
                  refine ⟨5993404621966320772187603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15982412325243522059166941 5993404621966320772187603)
                  ·
                    refine ⟨8990106932949481158281405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5993404621966320772187603 8990106932949481158281405)
                    ·
                      refine ⟨3371290099856055434355527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8990106932949481158281405 3371290099856055434355527)
                      ·
                        rfl

theorem cell23_6565564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_6565564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565564 prefixEnd_6565564 := by exact prefixLift 6565564
  have htrace : WordTrace (prefixWord ++ tailWord_6565564) baseStart_6565564 baseEnd_6565564 := by
    simpa [prefixWord, tailWord_6565564, baseEnd_6565564] using wordTrace_append hprefix tailTrace_6565564
  have hstable : (prefixWord ++ tailWord_6565564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565564).length < 2 ^ (prefixWord ++ tailWord_6565564).sum := by decide
  have hdescent : baseEnd_6565564 < baseStart_6565564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565581 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6565581 : Nat := 118140960795 + 6565581 * 2 ^ 59
def prefixEnd_6565581 : Nat := 4983230072969 + 3 ^ 40 * 6565581 * 2
def baseEnd_6565581 : Nat := 3371298829027181867842949

theorem tailTrace_6565581 : CollatzResearch.WordTrace tailWord_6565581 prefixEnd_6565581 3371298829027181867842949 := by
  unfold tailWord_6565581
  simp only [CollatzResearch.WordTrace]
  refine ⟨239466412027028823807704597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159644274684685882538469731 239466412027028823807704597)
  ·
    refine ⟨11224988063766976115986153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 239466412027028823807704597 11224988063766976115986153)
    ·
      refine ⟨8418741047825232086989615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11224988063766976115986153 8418741047825232086989615)
      ·
        refine ⟨12628111571737848130484423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8418741047825232086989615 12628111571737848130484423)
        ·
          refine ⟨18942167357606772195726635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12628111571737848130484423 18942167357606772195726635)
          ·
            refine ⟨28413251036410158293589953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18942167357606772195726635 28413251036410158293589953)
            ·
              refine ⟨21309938277307618720192465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28413251036410158293589953 21309938277307618720192465)
              ·
                refine ⟨15982453707980714040144349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21309938277307618720192465 15982453707980714040144349)
                ·
                  refine ⟨5993420140492767765054131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15982453707980714040144349 5993420140492767765054131)
                  ·
                    refine ⟨8990130210739151647581197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5993420140492767765054131 8990130210739151647581197)
                    ·
                      refine ⟨3371298829027181867842949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8990130210739151647581197 3371298829027181867842949)
                      ·
                        rfl

theorem cell23_6565581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6565581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565581 prefixEnd_6565581 := by exact prefixLift 6565581
  have htrace : WordTrace (prefixWord ++ tailWord_6565581) baseStart_6565581 baseEnd_6565581 := by
    simpa [prefixWord, tailWord_6565581, baseEnd_6565581] using wordTrace_append hprefix tailTrace_6565581
  have hstable : (prefixWord ++ tailWord_6565581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565581).length < 2 ^ (prefixWord ++ tailWord_6565581).sum := by decide
  have hdescent : baseEnd_6565581 < baseStart_6565581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565587 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 9, 2, 2]
def baseStart_6565587 : Nat := 118140960795 + 6565587 * 2 ^ 59
def prefixEnd_6565587 : Nat := 4983230072969 + 3 ^ 40 * 6565587 * 2
def baseEnd_6565587 : Nat := 3371301909911108844367921

theorem tailTrace_6565587 : CollatzResearch.WordTrace tailWord_6565587 prefixEnd_6565587 3371301909911108844367921 := by
  unfold tailWord_6565587
  simp only [CollatzResearch.WordTrace]
  refine ⟨239466630865007086832423015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159644420576671391221615343 239466630865007086832423015)
  ·
    refine ⟨359199946297510630248634523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239466630865007086832423015 359199946297510630248634523)
    ·
      refine ⟨538799919446265945372951785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359199946297510630248634523 538799919446265945372951785)
      ·
        refine ⟨404099939584699459029713839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538799919446265945372951785 404099939584699459029713839)
        ·
          refine ⟨606149909377049188544570759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404099939584699459029713839 606149909377049188544570759)
          ·
            refine ⟨909224864065573782816856139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606149909377049188544570759 909224864065573782816856139)
            ·
              refine ⟨1363837296098360674225284209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909224864065573782816856139 1363837296098360674225284209)
              ·
                refine ⟨1022877972073770505668963157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363837296098360674225284209 1022877972073770505668963157)
                ·
                  refine ⟨5993425617619749056654081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1022877972073770505668963157 5993425617619749056654081)
                  ·
                    refine ⟨4495069213214811792490561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5993425617619749056654081 4495069213214811792490561)
                    ·
                      refine ⟨3371301909911108844367921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495069213214811792490561 3371301909911108844367921)
                      ·
                        rfl

theorem cell23_6565587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 9, 2, 2].length) (baseStart_6565587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565587 prefixEnd_6565587 := by exact prefixLift 6565587
  have htrace : WordTrace (prefixWord ++ tailWord_6565587) baseStart_6565587 baseEnd_6565587 := by
    simpa [prefixWord, tailWord_6565587, baseEnd_6565587] using wordTrace_append hprefix tailTrace_6565587
  have hstable : (prefixWord ++ tailWord_6565587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565587).length < 2 ^ (prefixWord ++ tailWord_6565587).sum := by decide
  have hdescent : baseEnd_6565587 < baseStart_6565587 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565600 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4]
def baseStart_6565600 : Nat := 118140960795 + 6565600 * 2 ^ 59
def prefixEnd_6565600 : Nat := 4983230072969 + 3 ^ 40 * 6565600 * 2
def baseEnd_6565600 : Nat := 3371308585159617293505361

theorem tailTrace_6565600 : CollatzResearch.WordTrace tailWord_6565600 prefixEnd_6565600 3371308585159617293505361 := by
  unfold tailWord_6565600
  simp only [CollatzResearch.WordTrace]
  refine ⟨119733552506979995026323127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159644736675973326701764169 119733552506979995026323127)
  ·
    refine ⟨179600328760469992539484691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119733552506979995026323127 179600328760469992539484691)
    ·
      refine ⟨269400493140704988809227037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179600328760469992539484691 269400493140704988809227037)
      ·
        refine ⟨101025184927764370803460139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269400493140704988809227037 101025184927764370803460139)
        ·
          refine ⟨151537777391646556205190209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101025184927764370803460139 151537777391646556205190209)
          ·
            refine ⟨113653333043734917153892657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151537777391646556205190209 113653333043734917153892657)
            ·
              refine ⟨85239999782801187865419493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113653333043734917153892657 85239999782801187865419493)
              ·
                refine ⟨15982499959275222724766155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85239999782801187865419493 15982499959275222724766155)
                ·
                  refine ⟨23973749938912834087149233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15982499959275222724766155 23973749938912834087149233)
                  ·
                    refine ⟨17980312454184625565361925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23973749938912834087149233 17980312454184625565361925)
                    ·
                      refine ⟨3371308585159617293505361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17980312454184625565361925 3371308585159617293505361)
                      ·
                        rfl

theorem cell23_6565600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_6565600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565600 prefixEnd_6565600 := by exact prefixLift 6565600
  have htrace : WordTrace (prefixWord ++ tailWord_6565600) baseStart_6565600 baseEnd_6565600 := by
    simpa [prefixWord, tailWord_6565600, baseEnd_6565600] using wordTrace_append hprefix tailTrace_6565600
  have hstable : (prefixWord ++ tailWord_6565600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565600).length < 2 ^ (prefixWord ++ tailWord_6565600).sum := by decide
  have hdescent : baseEnd_6565600 < baseStart_6565600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565710 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6565710 : Nat := 118140960795 + 6565710 * 2 ^ 59
def prefixEnd_6565710 : Nat := 4983230072969 + 3 ^ 40 * 6565710 * 2
def baseEnd_6565710 : Nat := 3371365068031611863129855

theorem tailTrace_6565710 : CollatzResearch.WordTrace tailWord_6565710 prefixEnd_6565710 3371365068031611863129855 := by
  unfold tailWord_6565710
  simp only [CollatzResearch.WordTrace]
  refine ⟨29933889630445184854893823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159647411362374319226100389 29933889630445184854893823)
  ·
    refine ⟨44900834445667777282340735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29933889630445184854893823 44900834445667777282340735)
    ·
      refine ⟨67351251668501665923511103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44900834445667777282340735 67351251668501665923511103)
      ·
        refine ⟨101026877502752498885266655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67351251668501665923511103 101026877502752498885266655)
        ·
          refine ⟨151540316254128748327899983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101026877502752498885266655 151540316254128748327899983)
          ·
            refine ⟨227310474381193122491849975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151540316254128748327899983 227310474381193122491849975)
            ·
              refine ⟨340965711571789683737774963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227310474381193122491849975 340965711571789683737774963)
              ·
                refine ⟨511448567357684525606662445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340965711571789683737774963 511448567357684525606662445)
                ·
                  refine ⟨191793212759131697102498417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 511448567357684525606662445 191793212759131697102498417)
                  ·
                    refine ⟨143844909569348772826873813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191793212759131697102498417 143844909569348772826873813)
                    ·
                      refine ⟨3371365068031611863129855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 143844909569348772826873813 3371365068031611863129855)
                      ·
                        rfl

theorem cell23_6565710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6565710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565710 prefixEnd_6565710 := by exact prefixLift 6565710
  have htrace : WordTrace (prefixWord ++ tailWord_6565710) baseStart_6565710 baseEnd_6565710 := by
    simpa [prefixWord, tailWord_6565710, baseEnd_6565710] using wordTrace_append hprefix tailTrace_6565710
  have hstable : (prefixWord ++ tailWord_6565710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565710).length < 2 ^ (prefixWord ++ tailWord_6565710).sum := by decide
  have hdescent : baseEnd_6565710 < baseStart_6565710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565727 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 3]
def baseStart_6565727 : Nat := 118140960795 + 6565727 * 2 ^ 59
def prefixEnd_6565727 : Nat := 4983230072969 + 3 ^ 40 * 6565727 * 2
def baseEnd_6565727 : Nat := 3371373797202738296617277

theorem tailTrace_6565727 : CollatzResearch.WordTrace tailWord_6565727 prefixEnd_6565727 3371373797202738296617277 := by
  unfold tailWord_6565727
  simp only [CollatzResearch.WordTrace]
  refine ⟨239471737084499890742519435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159647824722999927161679623 239471737084499890742519435)
  ·
    refine ⟨359207605626749836113779153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239471737084499890742519435 359207605626749836113779153)
    ·
      refine ⟨269405704220062377085334365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359207605626749836113779153 269405704220062377085334365)
      ·
        refine ⟨101027139082523391407000387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269405704220062377085334365 101027139082523391407000387)
        ·
          refine ⟨151540708623785087110500581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101027139082523391407000387 151540708623785087110500581)
          ·
            refine ⟨28413882866959703833218859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151540708623785087110500581 28413882866959703833218859)
            ·
              refine ⟨42620824300439555749828289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28413882866959703833218859 42620824300439555749828289)
              ·
                refine ⟨31965618225329666812371217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42620824300439555749828289 31965618225329666812371217)
                ·
                  refine ⟨23974213668997250109278413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31965618225329666812371217 23974213668997250109278413)
                  ·
                    refine ⟨8990330125873968790979405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23974213668997250109278413 8990330125873968790979405)
                    ·
                      refine ⟨3371373797202738296617277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8990330125873968790979405 3371373797202738296617277)
                      ·
                        rfl

theorem cell23_6565727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_6565727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565727 prefixEnd_6565727 := by exact prefixLift 6565727
  have htrace : WordTrace (prefixWord ++ tailWord_6565727) baseStart_6565727 baseEnd_6565727 := by
    simpa [prefixWord, tailWord_6565727, baseEnd_6565727] using wordTrace_append hprefix tailTrace_6565727
  have hstable : (prefixWord ++ tailWord_6565727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565727).length < 2 ^ (prefixWord ++ tailWord_6565727).sum := by decide
  have hdescent : baseEnd_6565727 < baseStart_6565727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565728 : List Nat := [2, 1, 1, 3, 3, 4, 1, 2, 2, 2, 2]
def baseStart_6565728 : Nat := 118140960795 + 6565728 * 2 ^ 59
def prefixEnd_6565728 : Nat := 4983230072969 + 3 ^ 40 * 6565728 * 2
def baseEnd_6565728 : Nat := 3371374310683392792704773

theorem tailTrace_6565728 : CollatzResearch.WordTrace tailWord_6565728 prefixEnd_6565728 3371374310683392792704773 := by
  unfold tailWord_6565728
  simp only [CollatzResearch.WordTrace]
  refine ⟨119735886778748133956652919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159647849038330845275537225 119735886778748133956652919)
  ·
    refine ⟨179603830168122200934979379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119735886778748133956652919 179603830168122200934979379)
    ·
      refine ⟨269405745252183301402469069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179603830168122200934979379 269405745252183301402469069)
      ·
        refine ⟨101027154469568738025925901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269405745252183301402469069 101027154469568738025925901)
        ·
          refine ⟨37885182926088276759722213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101027154469568738025925901 37885182926088276759722213)
          ·
            refine ⟨7103471798641551892447915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37885182926088276759722213 7103471798641551892447915)
            ·
              refine ⟨10655207697962327838671873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103471798641551892447915 10655207697962327838671873)
              ·
                refine ⟨7991405773471745879003905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10655207697962327838671873 7991405773471745879003905)
                ·
                  refine ⟨5993554330103809409252929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7991405773471745879003905 5993554330103809409252929)
                  ·
                    refine ⟨4495165747577857056939697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5993554330103809409252929 4495165747577857056939697)
                    ·
                      refine ⟨3371374310683392792704773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495165747577857056939697 3371374310683392792704773)
                      ·
                        rfl

theorem cell23_6565728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_6565728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565728 prefixEnd_6565728 := by exact prefixLift 6565728
  have htrace : WordTrace (prefixWord ++ tailWord_6565728) baseStart_6565728 baseEnd_6565728 := by
    simpa [prefixWord, tailWord_6565728, baseEnd_6565728] using wordTrace_append hprefix tailTrace_6565728
  have hstable : (prefixWord ++ tailWord_6565728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565728).length < 2 ^ (prefixWord ++ tailWord_6565728).sum := by decide
  have hdescent : baseEnd_6565728 < baseStart_6565728 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565737 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 1, 7, 2]
def baseStart_6565737 : Nat := 118140960795 + 6565737 * 2 ^ 59
def prefixEnd_6565737 : Nat := 4983230072969 + 3 ^ 40 * 6565737 * 2
def baseEnd_6565737 : Nat := 3371378932009283257492231

theorem tailTrace_6565737 : CollatzResearch.WordTrace tailWord_6565737 prefixEnd_6565737 3371378932009283257492231 := by
  unfold tailWord_6565737
  simp only [CollatzResearch.WordTrace]
  refine ⟨239472101814463662450383465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159648067876309108300255643 239472101814463662450383465)
  ·
    refine ⟨179604076360847746837787599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239472101814463662450383465 179604076360847746837787599)
    ·
      refine ⟨269406114541271620256681399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179604076360847746837787599 269406114541271620256681399)
      ·
        refine ⟨404109171811907430385022099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269406114541271620256681399 404109171811907430385022099)
        ·
          refine ⟨606163757717861145577533149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404109171811907430385022099 606163757717861145577533149)
          ·
            refine ⟨227311409144197929591574931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 606163757717861145577533149 227311409144197929591574931)
            ·
              refine ⟨340967113716296894387362397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227311409144197929591574931 340967113716296894387362397)
              ·
                refine ⟨127862667643611335395260899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340967113716296894387362397 127862667643611335395260899)
                ·
                  refine ⟨191794001465417003092891349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127862667643611335395260899 191794001465417003092891349)
                  ·
                    refine ⟨4495171909345711009989641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 191794001465417003092891349 4495171909345711009989641)
                    ·
                      refine ⟨3371378932009283257492231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495171909345711009989641 3371378932009283257492231)
                      ·
                        rfl

theorem cell23_6565737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 1, 7, 2].length) (baseStart_6565737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565737 prefixEnd_6565737 := by exact prefixLift 6565737
  have htrace : WordTrace (prefixWord ++ tailWord_6565737) baseStart_6565737 baseEnd_6565737 := by
    simpa [prefixWord, tailWord_6565737, baseEnd_6565737] using wordTrace_append hprefix tailTrace_6565737
  have hstable : (prefixWord ++ tailWord_6565737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565737).length < 2 ^ (prefixWord ++ tailWord_6565737).sum := by decide
  have hdescent : baseEnd_6565737 < baseStart_6565737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565760 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 8]
def baseStart_6565760 : Nat := 118140960795 + 6565760 * 2 ^ 59
def prefixEnd_6565760 : Nat := 4983230072969 + 3 ^ 40 * 6565760 * 2
def baseEnd_6565760 : Nat := 1123796914021445555834875

theorem tailTrace_6565760 : CollatzResearch.WordTrace tailWord_6565760 prefixEnd_6565760 1123796914021445555834875 := by
  unfold tailWord_6565760
  simp only [CollatzResearch.WordTrace]
  refine ⟨119736470346690168689235367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159648627128920224918980489 119736470346690168689235367)
  ·
    refine ⟨179604705520035253033853051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119736470346690168689235367 179604705520035253033853051)
    ·
      refine ⟨269407058280052879550779577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179604705520035253033853051 269407058280052879550779577)
      ·
        refine ⟨202055293710039659663084683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269407058280052879550779577 202055293710039659663084683)
        ·
          refine ⟨303082940565059489494627025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202055293710039659663084683 303082940565059489494627025)
          ·
            refine ⟨227312205423794617120970269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303082940565059489494627025 227312205423794617120970269)
            ·
              refine ⟨85242077033922981420363851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227312205423794617120970269 85242077033922981420363851)
              ·
                refine ⟨127863115550884472130545777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85242077033922981420363851 127863115550884472130545777)
                ·
                  refine ⟨95897336663163354097909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127863115550884472130545777 95897336663163354097909333)
                  ·
                    refine ⟨1123796914021445555834875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95897336663163354097909333 1123796914021445555834875)
                    ·
                      rfl

theorem cell23_6565760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_6565760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565760 prefixEnd_6565760 := by exact prefixLift 6565760
  have htrace : WordTrace (prefixWord ++ tailWord_6565760) baseStart_6565760 baseEnd_6565760 := by
    simpa [prefixWord, tailWord_6565760, baseEnd_6565760] using wordTrace_append hprefix tailTrace_6565760
  have hstable : (prefixWord ++ tailWord_6565760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565760).length < 2 ^ (prefixWord ++ tailWord_6565760).sum := by decide
  have hdescent : baseEnd_6565760 < baseStart_6565760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565768 : List Nat := [2, 1, 3, 3, 4, 1, 1, 3, 5]
def baseStart_6565768 : Nat := 118140960795 + 6565768 * 2 ^ 59
def prefixEnd_6565768 : Nat := 4983230072969 + 3 ^ 40 * 6565768 * 2
def baseEnd_6565768 : Nat := 374599427767730292911621

theorem tailTrace_6565768 : CollatzResearch.WordTrace tailWord_6565768 prefixEnd_6565768 374599427767730292911621 := by
  unfold tailWord_6565768
  simp only [CollatzResearch.WordTrace]
  refine ⟨119736616238675677372380979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159648821651567569829841305 119736616238675677372380979)
  ·
    refine ⟨179604924358013516058571469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119736616238675677372380979 179604924358013516058571469)
    ·
      refine ⟨67351846634255068521964301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179604924358013516058571469 67351846634255068521964301)
      ·
        refine ⟨25256942487845650695736613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67351846634255068521964301 25256942487845650695736613)
        ·
          refine ⟨4735676716471059505450615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25256942487845650695736613 4735676716471059505450615)
          ·
            refine ⟨7103515074706589258175923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4735676716471059505450615 7103515074706589258175923)
            ·
              refine ⟨10655272612059883887263885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7103515074706589258175923 10655272612059883887263885)
              ·
                refine ⟨3995727229522456457723957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10655272612059883887263885 3995727229522456457723957)
                ·
                  refine ⟨374599427767730292911621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995727229522456457723957 374599427767730292911621)
                  ·
                    rfl

theorem cell23_6565768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 3, 5].length) (baseStart_6565768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565768 prefixEnd_6565768 := by exact prefixLift 6565768
  have htrace : WordTrace (prefixWord ++ tailWord_6565768) baseStart_6565768 baseEnd_6565768 := by
    simpa [prefixWord, tailWord_6565768, baseEnd_6565768] using wordTrace_append hprefix tailTrace_6565768
  have hstable : (prefixWord ++ tailWord_6565768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565768).length < 2 ^ (prefixWord ++ tailWord_6565768).sum := by decide
  have hdescent : baseEnd_6565768 < baseStart_6565768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565777 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 5, 4]
def baseStart_6565777 : Nat := 118140960795 + 6565777 * 2 ^ 59
def prefixEnd_6565777 : Nat := 4983230072969 + 3 ^ 40 * 6565777 * 2
def baseEnd_6565777 : Nat := 1123799823745154366997349

theorem tailTrace_6565777 : CollatzResearch.WordTrace tailWord_6565777 prefixEnd_6565777 1123799823745154366997349 := by
  unfold tailWord_6565777
  simp only [CollatzResearch.WordTrace]
  refine ⟨239473560734318749281839585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159649040489545832854559723 239473560734318749281839585)
  ·
    refine ⟨179605170550739061961379689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239473560734318749281839585 179605170550739061961379689)
    ·
      refine ⟨134703877913054296471034767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179605170550739061961379689 134703877913054296471034767)
      ·
        refine ⟨202055816869581444706552151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134703877913054296471034767 202055816869581444706552151)
        ·
          refine ⟨303083725304372167059828227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202055816869581444706552151 303083725304372167059828227)
          ·
            refine ⟨454625587956558250589742341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303083725304372167059828227 454625587956558250589742341)
            ·
              refine ⟨85242297741854671985576689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 454625587956558250589742341 85242297741854671985576689)
              ·
                refine ⟨63931723306391003989182517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85242297741854671985576689 63931723306391003989182517)
                ·
                  refine ⟨5993599059974156623985861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63931723306391003989182517 5993599059974156623985861)
                  ·
                    refine ⟨1123799823745154366997349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993599059974156623985861 1123799823745154366997349)
                    ·
                      rfl

theorem cell23_6565777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 5, 4].length) (baseStart_6565777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565777 prefixEnd_6565777 := by exact prefixLift 6565777
  have htrace : WordTrace (prefixWord ++ tailWord_6565777) baseStart_6565777 baseEnd_6565777 := by
    simpa [prefixWord, tailWord_6565777, baseEnd_6565777] using wordTrace_append hprefix tailTrace_6565777
  have hstable : (prefixWord ++ tailWord_6565777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565777).length < 2 ^ (prefixWord ++ tailWord_6565777).sum := by decide
  have hdescent : baseEnd_6565777 < baseStart_6565777 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565807 : List Nat := [1, 1, 2, 1, 2, 2, 5, 3, 6]
def baseStart_6565807 : Nat := 118140960795 + 6565807 * 2 ^ 59
def prefixEnd_6565807 : Nat := 4983230072969 + 3 ^ 40 * 6565807 * 2
def baseEnd_6565807 : Nat := 374601652850566442624101

theorem tailTrace_6565807 : CollatzResearch.WordTrace tailWord_6565807 prefixEnd_6565807 374601652850566442624101 := by
  unfold tailWord_6565807
  simp only [CollatzResearch.WordTrace]
  refine ⟨239474654924210064405431675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159649769949473376270287783 239474654924210064405431675)
  ·
    refine ⟨359211982386315096608147513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239474654924210064405431675 359211982386315096608147513)
    ·
      refine ⟨269408986789736322456110635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359211982386315096608147513 269408986789736322456110635)
      ·
        refine ⟨404113480184604483684165953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269408986789736322456110635 404113480184604483684165953)
        ·
          refine ⟨303085110138453362763124465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404113480184604483684165953 303085110138453362763124465)
          ·
            refine ⟨227313832603840022072343349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303085110138453362763124465 227313832603840022072343349)
            ·
              refine ⟨21310671806610002069282189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 227313832603840022072343349 21310671806610002069282189)
              ·
                refine ⟨7991501927478750775980821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21310671806610002069282189 7991501927478750775980821)
                ·
                  refine ⟨374601652850566442624101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7991501927478750775980821 374601652850566442624101)
                  ·
                    rfl

theorem cell23_6565807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 3, 6].length) (baseStart_6565807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565807 prefixEnd_6565807 := by exact prefixLift 6565807
  have htrace : WordTrace (prefixWord ++ tailWord_6565807) baseStart_6565807 baseEnd_6565807 := by
    simpa [prefixWord, tailWord_6565807, baseEnd_6565807] using wordTrace_append hprefix tailTrace_6565807
  have hstable : (prefixWord ++ tailWord_6565807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565807).length < 2 ^ (prefixWord ++ tailWord_6565807).sum := by decide
  have hdescent : baseEnd_6565807 < baseStart_6565807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565821 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 3]
def baseStart_6565821 : Nat := 118140960795 + 6565821 * 2 ^ 59
def prefixEnd_6565821 : Nat := 4983230072969 + 3 ^ 40 * 6565821 * 2
def baseEnd_6565821 : Nat := 3371422064384260928841845

theorem tailTrace_6565821 : CollatzResearch.WordTrace tailWord_6565821 prefixEnd_6565821 3371422064384260928841845 := by
  unfold tailWord_6565821
  simp only [CollatzResearch.WordTrace]
  refine ⟨239475165546159344796441317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159650110364106229864294211 239475165546159344796441317)
  ·
    refine ⟨44901593539904877149332747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239475165546159344796441317 44901593539904877149332747)
    ·
      refine ⟨67352390309857315723999121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44901593539904877149332747 67352390309857315723999121)
      ·
        refine ⟨50514292732392986792999341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67352390309857315723999121 50514292732392986792999341)
        ·
          refine ⟨18942859774647370047374753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50514292732392986792999341 18942859774647370047374753)
          ·
            refine ⟨14207144830985527535531065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18942859774647370047374753 14207144830985527535531065)
            ·
              refine ⟨10655358623239145651648299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14207144830985527535531065 10655358623239145651648299)
              ·
                refine ⟨15983037934858718477472449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10655358623239145651648299 15983037934858718477472449)
                ·
                  refine ⟨11987278451144038858104337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15983037934858718477472449 11987278451144038858104337)
                  ·
                    refine ⟨8990458838358029143578253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11987278451144038858104337 8990458838358029143578253)
                    ·
                      refine ⟨3371422064384260928841845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8990458838358029143578253 3371422064384260928841845)
                      ·
                        rfl

theorem cell23_6565821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_6565821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565821 prefixEnd_6565821 := by exact prefixLift 6565821
  have htrace : WordTrace (prefixWord ++ tailWord_6565821) baseStart_6565821 baseEnd_6565821 := by
    simpa [prefixWord, tailWord_6565821, baseEnd_6565821] using wordTrace_append hprefix tailTrace_6565821
  have hstable : (prefixWord ++ tailWord_6565821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565821).length < 2 ^ (prefixWord ++ tailWord_6565821).sum := by decide
  have hdescent : baseEnd_6565821 < baseStart_6565821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565845 : List Nat := [1, 3, 2, 3, 2, 3, 2, 2, 1, 4]
def baseStart_6565845 : Nat := 118140960795 + 6565845 * 2 ^ 59
def prefixEnd_6565845 : Nat := 4983230072969 + 3 ^ 40 * 6565845 * 2
def baseEnd_6565845 : Nat := 1123811462639989611647245

theorem tailTrace_6565845 : CollatzResearch.WordTrace tailWord_6565845 prefixEnd_6565845 1123811462639989611647245 := by
  unfold tailWord_6565845
  simp only [CollatzResearch.WordTrace]
  refine ⟨239476040898072396895314989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159650693932048264596876659 239476040898072396895314989)
  ·
    refine ⟨89803515336777148835743121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239476040898072396895314989 89803515336777148835743121)
    ·
      refine ⟨67352636502582861626807341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89803515336777148835743121 67352636502582861626807341)
      ·
        refine ⟨25257238688468573110052753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67352636502582861626807341 25257238688468573110052753)
        ·
          refine ⟨18942929016351429832539565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25257238688468573110052753 18942929016351429832539565)
          ·
            refine ⟨7103598381131786187202337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18942929016351429832539565 7103598381131786187202337)
            ·
              refine ⟨5327698785848839640401753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7103598381131786187202337 5327698785848839640401753)
              ·
                refine ⟨3995774089386629730301315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5327698785848839640401753 3995774089386629730301315)
                ·
                  refine ⟨5993661134079944595451973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995774089386629730301315 5993661134079944595451973)
                  ·
                    refine ⟨1123811462639989611647245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993661134079944595451973 1123811462639989611647245)
                    ·
                      rfl

theorem cell23_6565845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_6565845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565845 prefixEnd_6565845 := by exact prefixLift 6565845
  have htrace : WordTrace (prefixWord ++ tailWord_6565845) baseStart_6565845 baseEnd_6565845 := by
    simpa [prefixWord, tailWord_6565845, baseEnd_6565845] using wordTrace_append hprefix tailTrace_6565845
  have hstable : (prefixWord ++ tailWord_6565845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565845).length < 2 ^ (prefixWord ++ tailWord_6565845).sum := by decide
  have hdescent : baseEnd_6565845 < baseStart_6565845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565878 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6565878 : Nat := 118140960795 + 6565878 * 2 ^ 59
def prefixEnd_6565878 : Nat := 4983230072969 + 3 ^ 40 * 6565878 * 2
def baseEnd_6565878 : Nat := 3371451332781567205829083

theorem tailTrace_6565878 : CollatzResearch.WordTrace tailWord_6565878 prefixEnd_6565878 3371451332781567205829083 := by
  unfold tailWord_6565878
  simp only [CollatzResearch.WordTrace]
  refine ⟨14967327781684552720704143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159651496337968562354177525 14967327781684552720704143)
  ·
    refine ⟨22450991672526829081056215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14967327781684552720704143 22450991672526829081056215)
    ·
      refine ⟨33676487508790243621584323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22450991672526829081056215 33676487508790243621584323)
      ·
        refine ⟨50514731263185365432376485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33676487508790243621584323 50514731263185365432376485)
        ·
          refine ⟨9471512111847256018570591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50514731263185365432376485 9471512111847256018570591)
          ·
            refine ⟨14207268167770884027855887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9471512111847256018570591 14207268167770884027855887)
            ·
              refine ⟨21310902251656326041783831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14207268167770884027855887 21310902251656326041783831)
              ·
                refine ⟨31966353377484489062675747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21310902251656326041783831 31966353377484489062675747)
                ·
                  refine ⟨47949530066226733594013621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31966353377484489062675747 47949530066226733594013621)
                  ·
                    refine ⟨4495268443708756274438777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 47949530066226733594013621 4495268443708756274438777)
                    ·
                      refine ⟨3371451332781567205829083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495268443708756274438777 3371451332781567205829083)
                      ·
                        rfl

theorem cell23_6565878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6565878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565878 prefixEnd_6565878 := by exact prefixLift 6565878
  have htrace : WordTrace (prefixWord ++ tailWord_6565878) baseStart_6565878 baseEnd_6565878 := by
    simpa [prefixWord, tailWord_6565878, baseEnd_6565878] using wordTrace_append hprefix tailTrace_6565878
  have hstable : (prefixWord ++ tailWord_6565878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565878).length < 2 ^ (prefixWord ++ tailWord_6565878).sum := by decide
  have hdescent : baseEnd_6565878 < baseStart_6565878 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565884 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_6565884 : Nat := 118140960795 + 6565884 * 2 ^ 59
def prefixEnd_6565884 : Nat := 4983230072969 + 3 ^ 40 * 6565884 * 2
def baseEnd_6565884 : Nat := 1123818137888498060784685

theorem tailTrace_6565884 : CollatzResearch.WordTrace tailWord_6565884 prefixEnd_6565884 1123818137888498060784685 := by
  unfold tailWord_6565884
  simp only [CollatzResearch.WordTrace]
  refine ⟨119738731672465553277992353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159651642229954071037323137 119738731672465553277992353)
  ·
    refine ⟨89804048754349164958494265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119738731672465553277992353 89804048754349164958494265)
    ·
      refine ⟨67353036565761873718870699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89804048754349164958494265 67353036565761873718870699)
      ·
        refine ⟨101029554848642810578306049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67353036565761873718870699 101029554848642810578306049)
        ·
          refine ⟨75772166136482107933729537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101029554848642810578306049 75772166136482107933729537)
          ·
            refine ⟨56829124602361580950297153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75772166136482107933729537 56829124602361580950297153)
            ·
              refine ⟨42621843451771185712722865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56829124602361580950297153 42621843451771185712722865)
              ·
                refine ⟨31966382588828389284542149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42621843451771185712722865 31966382588828389284542149)
                ·
                  refine ⟨5993696735405322990851653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31966382588828389284542149 5993696735405322990851653)
                  ·
                    refine ⟨1123818137888498060784685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993696735405322990851653 1123818137888498060784685)
                    ·
                      rfl

theorem cell23_6565884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_6565884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565884 prefixEnd_6565884 := by exact prefixLift 6565884
  have htrace : WordTrace (prefixWord ++ tailWord_6565884) baseStart_6565884 baseEnd_6565884 := by
    simpa [prefixWord, tailWord_6565884, baseEnd_6565884] using wordTrace_append hprefix tailTrace_6565884
  have hstable : (prefixWord ++ tailWord_6565884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565884).length < 2 ^ (prefixWord ++ tailWord_6565884).sum := by decide
  have hdescent : baseEnd_6565884 < baseStart_6565884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565911 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 5]
def baseStart_6565911 : Nat := 118140960795 + 6565911 * 2 ^ 59
def prefixEnd_6565911 : Nat := 4983230072969 + 3 ^ 40 * 6565911 * 2
def baseEnd_6565911 : Nat := 3371468277643165576716431

theorem tailTrace_6565911 : CollatzResearch.WordTrace tailWord_6565911 prefixEnd_6565911 3371468277643165576716431 := by
  unfold tailWord_6565911
  simp only [CollatzResearch.WordTrace]
  refine ⟨239478448115833290167217587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159652298743888860111478391 239478448115833290167217587)
  ·
    refine ⟨359217672173749935250826381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239478448115833290167217587 359217672173749935250826381)
    ·
      refine ⟨134706627065156225719059893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359217672173749935250826381 134706627065156225719059893)
      ·
        refine ⟨12628746287358396161161865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134706627065156225719059893 12628746287358396161161865)
        ·
          refine ⟨9471559715518797120871399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12628746287358396161161865 9471559715518797120871399)
          ·
            refine ⟨14207339573278195681307099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9471559715518797120871399 14207339573278195681307099)
            ·
              refine ⟨21311009359917293521960649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14207339573278195681307099 21311009359917293521960649)
              ·
                refine ⟨15983257019937970141470487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21311009359917293521960649 15983257019937970141470487)
                ·
                  refine ⟨23974885529906955212205731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15983257019937970141470487 23974885529906955212205731)
                  ·
                    refine ⟨35962328294860432818308597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23974885529906955212205731 35962328294860432818308597)
                    ·
                      refine ⟨3371468277643165576716431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35962328294860432818308597 3371468277643165576716431)
                      ·
                        rfl

theorem cell23_6565911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_6565911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565911 prefixEnd_6565911 := by exact prefixLift 6565911
  have htrace : WordTrace (prefixWord ++ tailWord_6565911) baseStart_6565911 baseEnd_6565911 := by
    simpa [prefixWord, tailWord_6565911, baseEnd_6565911] using wordTrace_append hprefix tailTrace_6565911
  have hstable : (prefixWord ++ tailWord_6565911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565911).length < 2 ^ (prefixWord ++ tailWord_6565911).sum := by decide
  have hdescent : baseEnd_6565911 < baseStart_6565911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565941 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 3]
def baseStart_6565941 : Nat := 118140960795 + 6565941 * 2 ^ 59
def prefixEnd_6565941 : Nat := 4983230072969 + 3 ^ 40 * 6565941 * 2
def baseEnd_6565941 : Nat := 3371483682062800459341293

theorem tailTrace_6565941 : CollatzResearch.WordTrace tailWord_6565941 prefixEnd_6565941 3371483682062800459341293 := by
  unfold tailWord_6565941
  simp only [CollatzResearch.WordTrace]
  refine ⟨239479542305724605290809677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159653028203816403527206451 239479542305724605290809677)
  ·
    refine ⟨89804828364646726984053629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239479542305724605290809677 89804828364646726984053629)
    ·
      refine ⟨33676810636742522619020111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89804828364646726984053629 33676810636742522619020111)
      ·
        refine ⟨50515215955113783928530167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33676810636742522619020111 50515215955113783928530167)
        ·
          refine ⟨75772823932670675892795251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50515215955113783928530167 75772823932670675892795251)
          ·
            refine ⟨113659235899006013839192877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75772823932670675892795251 113659235899006013839192877)
            ·
              refine ⟨42622213462127255189697329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113659235899006013839192877 42622213462127255189697329)
              ·
                refine ⟨31966660096595441392272997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42622213462127255189697329 31966660096595441392272997)
                ·
                  refine ⟨5993748768111645261051187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31966660096595441392272997 5993748768111645261051187)
                  ·
                    refine ⟨8990623152167467891576781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5993748768111645261051187 8990623152167467891576781)
                    ·
                      refine ⟨3371483682062800459341293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8990623152167467891576781 3371483682062800459341293)
                      ·
                        rfl

theorem cell23_6565941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_6565941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565941 prefixEnd_6565941 := by exact prefixLift 6565941
  have htrace : WordTrace (prefixWord ++ tailWord_6565941) baseStart_6565941 baseEnd_6565941 := by
    simpa [prefixWord, tailWord_6565941, baseEnd_6565941] using wordTrace_append hprefix tailTrace_6565941
  have hstable : (prefixWord ++ tailWord_6565941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565941).length < 2 ^ (prefixWord ++ tailWord_6565941).sum := by decide
  have hdescent : baseEnd_6565941 < baseStart_6565941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565984 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_6565984 : Nat := 118140960795 + 6565984 * 2 ^ 59
def prefixEnd_6565984 : Nat := 4983230072969 + 3 ^ 40 * 6565984 * 2
def baseEnd_6565984 : Nat := 3371505761730943791103595

theorem tailTrace_6565984 : CollatzResearch.WordTrace tailWord_6565984 prefixEnd_6565984 3371505761730943791103595 := by
  unfold tailWord_6565984
  simp only [CollatzResearch.WordTrace]
  refine ⟨119740555322284411817312503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159654073763045882423083337 119740555322284411817312503)
  ·
    refine ⟨179610832983426617725968755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119740555322284411817312503 179610832983426617725968755)
    ·
      refine ⟨269416249475139926588953133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179610832983426617725968755 269416249475139926588953133)
      ·
        refine ⟨101031093553177472470857425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269416249475139926588953133 101031093553177472470857425)
        ·
          refine ⟨75773320164883104353143069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101031093553177472470857425 75773320164883104353143069)
          ·
            refine ⟨28414995061831164132428651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75773320164883104353143069 28414995061831164132428651)
            ·
              refine ⟨42622492592746746198642977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28414995061831164132428651 42622492592746746198642977)
              ·
                refine ⟨31966869444560059648982233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42622492592746746198642977 31966869444560059648982233)
                ·
                  refine ⟨23975152083420044736736675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31966869444560059648982233 23975152083420044736736675)
                  ·
                    refine ⟨35962728125130067105105013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23975152083420044736736675 35962728125130067105105013)
                    ·
                      refine ⟨3371505761730943791103595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35962728125130067105105013 3371505761730943791103595)
                      ·
                        rfl

theorem cell23_6565984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_6565984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565984 prefixEnd_6565984 := by exact prefixLift 6565984
  have htrace : WordTrace (prefixWord ++ tailWord_6565984) baseStart_6565984 baseEnd_6565984 := by
    simpa [prefixWord, tailWord_6565984, baseEnd_6565984] using wordTrace_append hprefix tailTrace_6565984
  have hstable : (prefixWord ++ tailWord_6565984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565984).length < 2 ^ (prefixWord ++ tailWord_6565984).sum := by decide
  have hdescent : baseEnd_6565984 < baseStart_6565984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6565998 : List Nat := [4, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_6565998 : Nat := 118140960795 + 6565998 * 2 ^ 59
def prefixEnd_6565998 : Nat := 4983230072969 + 3 ^ 40 * 6565998 * 2
def baseEnd_6565998 : Nat := 3371512950460106736328531

theorem tailTrace_6565998 : CollatzResearch.WordTrace tailWord_6565998 prefixEnd_6565998 3371512950460106736328531 := by
  unfold tailWord_6565998
  simp only [CollatzResearch.WordTrace]
  refine ⟨29935202658314763003204331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159654414177678736017089765 29935202658314763003204331)
  ·
    refine ⟨44902803987472144504806497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29935202658314763003204331 44902803987472144504806497)
    ·
      refine ⟨33677102990604108378604873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44902803987472144504806497 33677102990604108378604873)
      ·
        refine ⟨25257827242953081283953655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33677102990604108378604873 25257827242953081283953655)
        ·
          refine ⟨37886740864429621925930483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25257827242953081283953655 37886740864429621925930483)
          ·
            refine ⟨56830111296644432888895725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37886740864429621925930483 56830111296644432888895725)
            ·
              refine ⟨21311291736241662333335897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56830111296644432888895725 21311291736241662333335897)
              ·
                refine ⟨15983468802181246750001923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21311291736241662333335897 15983468802181246750001923)
                ·
                  refine ⟨23975203203271870125002885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15983468802181246750001923 23975203203271870125002885)
                  ·
                    refine ⟨4495350600613475648438041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23975203203271870125002885 4495350600613475648438041)
                    ·
                      refine ⟨3371512950460106736328531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495350600613475648438041 3371512950460106736328531)
                      ·
                        rfl

theorem cell23_6565998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_6565998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6565998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6565998 prefixEnd_6565998 := by exact prefixLift 6565998
  have htrace : WordTrace (prefixWord ++ tailWord_6565998) baseStart_6565998 baseEnd_6565998 := by
    simpa [prefixWord, tailWord_6565998, baseEnd_6565998] using wordTrace_append hprefix tailTrace_6565998
  have hstable : (prefixWord ++ tailWord_6565998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6565998).length < 2 ^ (prefixWord ++ tailWord_6565998).sum := by decide
  have hdescent : baseEnd_6565998 < baseStart_6565998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6565998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566055 : List Nat := [1, 1, 6, 2, 2, 1, 2, 3, 5]
def baseStart_6566055 : Nat := 118140960795 + 6566055 * 2 ^ 59
def prefixEnd_6566055 : Nat := 4983230072969 + 3 ^ 40 * 6566055 * 2
def baseEnd_6566055 : Nat := 374615802095268112590641

theorem tailTrace_6566055 : CollatzResearch.WordTrace tailWord_6566055 prefixEnd_6566055 374615802095268112590641 := by
  unfold tailWord_6566055
  simp only [CollatzResearch.WordTrace]
  refine ⟨239483700227311602760459619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159655800151541068506973079 239483700227311602760459619)
  ·
    refine ⟨359225550340967404140689429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239483700227311602760459619 359225550340967404140689429)
    ·
      refine ⟨16838697672232847069094817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 359225550340967404140689429 16838697672232847069094817)
      ·
        refine ⟨12629023254174635301821113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16838697672232847069094817 12629023254174635301821113)
        ·
          refine ⟨9471767440630976476365835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12629023254174635301821113 9471767440630976476365835)
          ·
            refine ⟨14207651160946464714548753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9471767440630976476365835 14207651160946464714548753)
            ·
              refine ⟨10655738370709848535911565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14207651160946464714548753 10655738370709848535911565)
              ·
                refine ⟨3995901889016193200966837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10655738370709848535911565 3995901889016193200966837)
                ·
                  refine ⟨374615802095268112590641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3995901889016193200966837 374615802095268112590641)
                  ·
                    rfl

theorem cell23_6566055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 5].length) (baseStart_6566055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566055 prefixEnd_6566055 := by exact prefixLift 6566055
  have htrace : WordTrace (prefixWord ++ tailWord_6566055) baseStart_6566055 baseEnd_6566055 := by
    simpa [prefixWord, tailWord_6566055, baseEnd_6566055] using wordTrace_append hprefix tailTrace_6566055
  have hstable : (prefixWord ++ tailWord_6566055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566055).length < 2 ^ (prefixWord ++ tailWord_6566055).sum := by decide
  have hdescent : baseEnd_6566055 < baseStart_6566055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566074 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_6566074 : Nat := 118140960795 + 6566074 * 2 ^ 59
def prefixEnd_6566074 : Nat := 4983230072969 + 3 ^ 40 * 6566074 * 2
def baseEnd_6566074 : Nat := 3371551974989848438978181

theorem tailTrace_6566074 : CollatzResearch.WordTrace tailWord_6566074 prefixEnd_6566074 3371551974989848438978181 := by
  unfold tailWord_6566074
  simp only [CollatzResearch.WordTrace]
  refine ⟨59871098303560692251350319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159656262142828512670267517 59871098303560692251350319)
  ·
    refine ⟨89806647455341038377025479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59871098303560692251350319 89806647455341038377025479)
    ·
      refine ⟨134709971183011557565538219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89806647455341038377025479 134709971183011557565538219)
      ·
        refine ⟨202064956774517336348307329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134709971183011557565538219 202064956774517336348307329)
        ·
          refine ⟨151548717580888002261230497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202064956774517336348307329 151548717580888002261230497)
          ·
            refine ⟨113661538185666001695922873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151548717580888002261230497 113661538185666001695922873)
            ·
              refine ⟨85246153639249501271942155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113661538185666001695922873 85246153639249501271942155)
              ·
                refine ⟨127869230458874251907913233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85246153639249501271942155 127869230458874251907913233)
                ·
                  refine ⟨95901922844155688930934925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127869230458874251907913233 95901922844155688930934925)
                  ·
                    refine ⟨35963221066558383349100597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95901922844155688930934925 35963221066558383349100597)
                    ·
                      refine ⟨3371551974989848438978181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35963221066558383349100597 3371551974989848438978181)
                      ·
                        rfl

theorem cell23_6566074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_6566074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566074 prefixEnd_6566074 := by exact prefixLift 6566074
  have htrace : WordTrace (prefixWord ++ tailWord_6566074) baseStart_6566074 baseEnd_6566074 := by
    simpa [prefixWord, tailWord_6566074, baseEnd_6566074] using wordTrace_append hprefix tailTrace_6566074
  have hstable : (prefixWord ++ tailWord_6566074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566074).length < 2 ^ (prefixWord ++ tailWord_6566074).sum := by decide
  have hdescent : baseEnd_6566074 < baseStart_6566074 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566098 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 3, 4]
def baseStart_6566098 : Nat := 118140960795 + 6566098 * 2 ^ 59
def prefixEnd_6566098 : Nat := 4983230072969 + 3 ^ 40 * 6566098 * 2
def baseEnd_6566098 : Nat := 1123854766175185448359357

theorem tailTrace_6566098 : CollatzResearch.WordTrace tailWord_6566098 prefixEnd_6566098 1123854766175185448359357 := by
  unfold tailWord_6566098
  simp only [CollatzResearch.WordTrace]
  refine ⟨59871317141538955276068737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159656845710770547402849965 59871317141538955276068737)
  ·
    refine ⟨44903487856154216457051553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59871317141538955276068737 44903487856154216457051553)
    ·
      refine ⟨33677615892115662342788665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44903487856154216457051553 33677615892115662342788665)
      ·
        refine ⟨25258211919086746757091499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33677615892115662342788665 25258211919086746757091499)
        ·
          refine ⟨37887317878630120135637249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25258211919086746757091499 37887317878630120135637249)
          ·
            refine ⟨28415488408972590101727937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37887317878630120135637249 28415488408972590101727937)
            ·
              refine ⟨21311616306729442576295953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28415488408972590101727937 21311616306729442576295953)
              ·
                refine ⟨15983712230047081932221965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21311616306729442576295953 15983712230047081932221965)
                ·
                  refine ⟨5993892086267655724583237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15983712230047081932221965 5993892086267655724583237)
                  ·
                    refine ⟨1123854766175185448359357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993892086267655724583237 1123854766175185448359357)
                    ·
                      rfl

theorem cell23_6566098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_6566098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566098 prefixEnd_6566098 := by exact prefixLift 6566098
  have htrace : WordTrace (prefixWord ++ tailWord_6566098) baseStart_6566098 baseEnd_6566098 := by
    simpa [prefixWord, tailWord_6566098, baseEnd_6566098] using wordTrace_append hprefix tailTrace_6566098
  have hstable : (prefixWord ++ tailWord_6566098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566098).length < 2 ^ (prefixWord ++ tailWord_6566098).sum := by decide
  have hdescent : baseEnd_6566098 < baseStart_6566098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566125 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_6566125 : Nat := 118140960795 + 6566125 * 2 ^ 59
def prefixEnd_6566125 : Nat := 4983230072969 + 3 ^ 40 * 6566125 * 2
def baseEnd_6566125 : Nat := 3371578162503227739440447

theorem tailTrace_6566125 : CollatzResearch.WordTrace tailWord_6566125 prefixEnd_6566125 3371578162503227739440447 := by
  unfold tailWord_6566125
  simp only [CollatzResearch.WordTrace]
  refine ⟨239486253337058004715507829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159657502224705336477005219 239486253337058004715507829)
  ·
    refine ⟨22451836250349187942078859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239486253337058004715507829 22451836250349187942078859)
    ·
      refine ⟨33677754375523781913118289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22451836250349187942078859 33677754375523781913118289)
      ·
        refine ⟨25258315781642836434838717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33677754375523781913118289 25258315781642836434838717)
        ·
          refine ⟨9471868418116063663064519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25258315781642836434838717 9471868418116063663064519)
          ·
            refine ⟨14207802627174095494596779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9471868418116063663064519 14207802627174095494596779)
            ·
              refine ⟨21311703940761143241895169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14207802627174095494596779 21311703940761143241895169)
              ·
                refine ⟨15983777955570857431421377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21311703940761143241895169 15983777955570857431421377)
                ·
                  refine ⟨11987833466678143073566033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15983777955570857431421377 11987833466678143073566033)
                  ·
                    refine ⟨8990875100008607305174525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11987833466678143073566033 8990875100008607305174525)
                    ·
                      refine ⟨3371578162503227739440447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8990875100008607305174525 3371578162503227739440447)
                      ·
                        rfl

theorem cell23_6566125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_6566125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566125 prefixEnd_6566125 := by exact prefixLift 6566125
  have htrace : WordTrace (prefixWord ++ tailWord_6566125) baseStart_6566125 baseEnd_6566125 := by
    simpa [prefixWord, tailWord_6566125, baseEnd_6566125] using wordTrace_append hprefix tailTrace_6566125
  have hstable : (prefixWord ++ tailWord_6566125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566125).length < 2 ^ (prefixWord ++ tailWord_6566125).sum := by decide
  have hdescent : baseEnd_6566125 < baseStart_6566125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566171 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 6, 4]
def baseStart_6566171 : Nat := 118140960795 + 6566171 * 2 ^ 59
def prefixEnd_6566171 : Nat := 4983230072969 + 3 ^ 40 * 6566171 * 2
def baseEnd_6566171 : Nat := 1123867260871111519821745

theorem tailTrace_6566171 : CollatzResearch.WordTrace tailWord_6566171 prefixEnd_6566171 1123867260871111519821745 := by
  unfold tailWord_6566171
  simp only [CollatzResearch.WordTrace]
  refine ⟨239487931094891354571682367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159658620729927569714454911 239487931094891354571682367)
  ·
    refine ⟨359231896642337031857523551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239487931094891354571682367 359231896642337031857523551)
    ·
      refine ⟨538847844963505547786285327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359231896642337031857523551 538847844963505547786285327)
      ·
        refine ⟨808271767445258321679427991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538847844963505547786285327 808271767445258321679427991)
        ·
          refine ⟨1212407651167887482519141987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808271767445258321679427991 1212407651167887482519141987)
          ·
            refine ⟨1818611476751831223778712981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212407651167887482519141987 1818611476751831223778712981)
            ·
              refine ⟨85247412972742088614627171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1818611476751831223778712981 85247412972742088614627171)
              ·
                refine ⟨127871119459113132921940757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85247412972742088614627171 127871119459113132921940757)
                ·
                  refine ⟨5993958724645928105715973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127871119459113132921940757 5993958724645928105715973)
                  ·
                    refine ⟨1123867260871111519821745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993958724645928105715973 1123867260871111519821745)
                    ·
                      rfl

theorem cell23_6566171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 6, 4].length) (baseStart_6566171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566171 prefixEnd_6566171 := by exact prefixLift 6566171
  have htrace : WordTrace (prefixWord ++ tailWord_6566171) baseStart_6566171 baseEnd_6566171 := by
    simpa [prefixWord, tailWord_6566171, baseEnd_6566171] using wordTrace_append hprefix tailTrace_6566171
  have hstable : (prefixWord ++ tailWord_6566171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566171).length < 2 ^ (prefixWord ++ tailWord_6566171).sum := by decide
  have hdescent : baseEnd_6566171 < baseStart_6566171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566175 : List Nat := [1, 1, 2, 4, 3, 2, 3, 1, 1, 5]
def baseStart_6566175 : Nat := 118140960795 + 6566175 * 2 ^ 59
def prefixEnd_6566175 : Nat := 4983230072969 + 3 ^ 40 * 6566175 * 2
def baseEnd_6566175 : Nat := 1123867945511984181271739

theorem tailTrace_6566175 : CollatzResearch.WordTrace tailWord_6566175 prefixEnd_6566175 1123867945511984181271739 := by
  unfold tailWord_6566175
  simp only [CollatzResearch.WordTrace]
  refine ⟨239488076986876863254827979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159658717991251242169885319 239488076986876863254827979)
  ·
    refine ⟨359232115480315294882241969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239488076986876863254827979 359232115480315294882241969)
    ·
      refine ⟨269424086610236471161681477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359232115480315294882241969 269424086610236471161681477)
      ·
        refine ⟨50517016239419338342815277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269424086610236471161681477 50517016239419338342815277)
        ·
          refine ⟨18943881089782251878555729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50517016239419338342815277 18943881089782251878555729)
          ·
            refine ⟨14207910817336688908916797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18943881089782251878555729 14207910817336688908916797)
            ·
              refine ⟨5327966556501258340843799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14207910817336688908916797 5327966556501258340843799)
              ·
                refine ⟨7991949834751887511265699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5327966556501258340843799 7991949834751887511265699)
                ·
                  refine ⟨11987924752127831266898549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7991949834751887511265699 11987924752127831266898549)
                  ·
                    refine ⟨1123867945511984181271739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11987924752127831266898549 1123867945511984181271739)
                    ·
                      rfl

theorem cell23_6566175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 1, 5].length) (baseStart_6566175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566175 prefixEnd_6566175 := by exact prefixLift 6566175
  have htrace : WordTrace (prefixWord ++ tailWord_6566175) baseStart_6566175 baseEnd_6566175 := by
    simpa [prefixWord, tailWord_6566175, baseEnd_6566175] using wordTrace_append hprefix tailTrace_6566175
  have hstable : (prefixWord ++ tailWord_6566175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566175).length < 2 ^ (prefixWord ++ tailWord_6566175).sum := by decide
  have hdescent : baseEnd_6566175 < baseStart_6566175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566183 : List Nat := [1, 1, 8, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6566183 : Nat := 118140960795 + 6566183 * 2 ^ 59
def prefixEnd_6566183 : Nat := 4983230072969 + 3 ^ 40 * 6566183 * 2
def baseEnd_6566183 : Nat := 1123869314793729504171727

theorem tailTrace_6566183 : CollatzResearch.WordTrace tailWord_6566183 prefixEnd_6566183 1123869314793729504171727 := by
  unfold tailWord_6566183
  simp only [CollatzResearch.WordTrace]
  refine ⟨239488368770847880621119203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159658912513898587080746135 239488368770847880621119203)
  ·
    refine ⟨359232553156271820931678805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239488368770847880621119203 359232553156271820931678805)
    ·
      refine ⟨4209756482300060401543111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 359232553156271820931678805 4209756482300060401543111)
      ·
        refine ⟨6314634723450090602314667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4209756482300060401543111 6314634723450090602314667)
        ·
          refine ⟨9471952085175135903472001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6314634723450090602314667 9471952085175135903472001)
          ·
            refine ⟨7103964063881351927604001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9471952085175135903472001 7103964063881351927604001)
            ·
              refine ⟨5327973047911013945703001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7103964063881351927604001 5327973047911013945703001)
              ·
                refine ⟨3995979785933260459277251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5327973047911013945703001 3995979785933260459277251)
                ·
                  refine ⟨5993969678899890688915877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3995979785933260459277251 5993969678899890688915877)
                  ·
                    refine ⟨1123869314793729504171727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993969678899890688915877 1123869314793729504171727)
                    ·
                      rfl

theorem cell23_6566183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6566183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566183 prefixEnd_6566183 := by exact prefixLift 6566183
  have htrace : WordTrace (prefixWord ++ tailWord_6566183) baseStart_6566183 baseEnd_6566183 := by
    simpa [prefixWord, tailWord_6566183, baseEnd_6566183] using wordTrace_append hprefix tailTrace_6566183
  have hstable : (prefixWord ++ tailWord_6566183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566183).length < 2 ^ (prefixWord ++ tailWord_6566183).sum := by decide
  have hdescent : baseEnd_6566183 < baseStart_6566183 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566188 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_6566188 : Nat := 118140960795 + 6566188 * 2 ^ 59
def prefixEnd_6566188 : Nat := 4983230072969 + 3 ^ 40 * 6566188 * 2
def baseEnd_6566188 : Nat := 1123870170594820330984219

theorem tailTrace_6566188 : CollatzResearch.WordTrace tailWord_6566188 prefixEnd_6566188 1123870170594820330984219 := by
  unfold tailWord_6566188
  simp only [CollatzResearch.WordTrace]
  refine ⟨119744275567914883237525609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159659034090553177650034145 119744275567914883237525609)
  ·
    refine ⟨89808206675936162428144207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119744275567914883237525609 89808206675936162428144207)
    ·
      refine ⟨134712310013904243642216311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89808206675936162428144207 134712310013904243642216311)
      ·
        refine ⟨202068465020856365463324467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134712310013904243642216311 202068465020856365463324467)
        ·
          refine ⟨303102697531284548194986701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202068465020856365463324467 303102697531284548194986701)
          ·
            refine ⟨113663511574231705573120013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 303102697531284548194986701 113663511574231705573120013)
            ·
              refine ⟨42623816840336889589920005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113663511574231705573120013 42623816840336889589920005)
              ·
                refine ⟨7991965657563166798110001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42623816840336889589920005 7991965657563166798110001)
                ·
                  refine ⟨5993974243172375098582501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7991965657563166798110001 5993974243172375098582501)
                  ·
                    refine ⟨1123870170594820330984219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5993974243172375098582501 1123870170594820330984219)
                    ·
                      rfl

theorem cell23_6566188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_6566188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566188 prefixEnd_6566188 := by exact prefixLift 6566188
  have htrace : WordTrace (prefixWord ++ tailWord_6566188) baseStart_6566188 baseEnd_6566188 := by
    simpa [prefixWord, tailWord_6566188, baseEnd_6566188] using wordTrace_append hprefix tailTrace_6566188
  have hstable : (prefixWord ++ tailWord_6566188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566188).length < 2 ^ (prefixWord ++ tailWord_6566188).sum := by decide
  have hdescent : baseEnd_6566188 < baseStart_6566188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566195 : List Nat := [1, 1, 1, 2, 5, 1, 2, 3, 3, 2, 2]
def baseStart_6566195 : Nat := 118140960795 + 6566195 * 2 ^ 59
def prefixEnd_6566195 : Nat := 4983230072969 + 3 ^ 40 * 6566195 * 2
def baseEnd_6566195 : Nat := 3371614106149042465565125

theorem tailTrace_6566195 : CollatzResearch.WordTrace tailWord_6566195 prefixEnd_6566195 3371614106149042465565125 := by
  unfold tailWord_6566195
  simp only [CollatzResearch.WordTrace]
  refine ⟨239488806446804406670556039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159659204297869604447037359 239488806446804406670556039)
  ·
    refine ⟨359233209670206610005834059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239488806446804406670556039 359233209670206610005834059)
    ·
      refine ⟨538849814505309915008751089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359233209670206610005834059 538849814505309915008751089)
      ·
        refine ⟨404137360878982436256563317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538849814505309915008751089 404137360878982436256563317)
        ·
          refine ⟨37887877582404603399052811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 404137360878982436256563317 37887877582404603399052811)
          ·
            refine ⟨56831816373606905098579217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37887877582404603399052811 56831816373606905098579217)
            ·
              refine ⟨42623862280205178823934413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56831816373606905098579217 42623862280205178823934413)
              ·
                refine ⟨15983948355076942058975405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42623862280205178823934413 15983948355076942058975405)
                ·
                  refine ⟨5993980633153853272115777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15983948355076942058975405 5993980633153853272115777)
                  ·
                    refine ⟨4495485474865389954086833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5993980633153853272115777 4495485474865389954086833)
                    ·
                      refine ⟨3371614106149042465565125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495485474865389954086833 3371614106149042465565125)
                      ·
                        rfl

theorem cell23_6566195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 3, 3, 2, 2].length) (baseStart_6566195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566195 prefixEnd_6566195 := by exact prefixLift 6566195
  have htrace : WordTrace (prefixWord ++ tailWord_6566195) baseStart_6566195 baseEnd_6566195 := by
    simpa [prefixWord, tailWord_6566195, baseEnd_6566195] using wordTrace_append hprefix tailTrace_6566195
  have hstable : (prefixWord ++ tailWord_6566195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566195).length < 2 ^ (prefixWord ++ tailWord_6566195).sum := by decide
  have hdescent : baseEnd_6566195 < baseStart_6566195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566229 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 1, 1, 4]
def baseStart_6566229 : Nat := 118140960795 + 6566229 * 2 ^ 59
def prefixEnd_6566229 : Nat := 4983230072969 + 3 ^ 40 * 6566229 * 2
def baseEnd_6566229 : Nat := 3371631564491295332539969

theorem tailTrace_6566229 : CollatzResearch.WordTrace tailWord_6566229 prefixEnd_6566229 3371631564491295332539969 := by
  unfold tailWord_6566229
  simp only [CollatzResearch.WordTrace]
  refine ⟨239490046528681230477293741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159660031019120820318195827 239490046528681230477293741)
  ·
    refine ⟨89808767448255461428985153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239490046528681230477293741 89808767448255461428985153)
    ·
      refine ⟨67356575586191596071738865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89808767448255461428985153 67356575586191596071738865)
      ·
        refine ⟨50517431689643697053804149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67356575586191596071738865 50517431689643697053804149)
        ·
          refine ⟨4736009220904096598794139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50517431689643697053804149 4736009220904096598794139)
          ·
            refine ⟨7104013831356144898191209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736009220904096598794139 7104013831356144898191209)
            ·
              refine ⟨5328010373517108673643407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104013831356144898191209 5328010373517108673643407)
              ·
                refine ⟨7992015560275663010465111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328010373517108673643407 7992015560275663010465111)
                ·
                  refine ⟨11988023340413494515697667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7992015560275663010465111 11988023340413494515697667)
                  ·
                    refine ⟨17982035010620241773546501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11988023340413494515697667 17982035010620241773546501)
                    ·
                      refine ⟨3371631564491295332539969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17982035010620241773546501 3371631564491295332539969)
                      ·
                        rfl

theorem cell23_6566229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_6566229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566229 prefixEnd_6566229 := by exact prefixLift 6566229
  have htrace : WordTrace (prefixWord ++ tailWord_6566229) baseStart_6566229 baseEnd_6566229 := by
    simpa [prefixWord, tailWord_6566229, baseEnd_6566229] using wordTrace_append hprefix tailTrace_6566229
  have hstable : (prefixWord ++ tailWord_6566229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566229).length < 2 ^ (prefixWord ++ tailWord_6566229).sum := by decide
  have hdescent : baseEnd_6566229 < baseStart_6566229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566245 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 3]
def baseStart_6566245 : Nat := 118140960795 + 6566245 * 2 ^ 59
def prefixEnd_6566245 : Nat := 4983230072969 + 3 ^ 40 * 6566245 * 2
def baseEnd_6566245 : Nat := 3371639780181767269939895

theorem tailTrace_6566245 : CollatzResearch.WordTrace tailWord_6566245 prefixEnd_6566245 3371639780181767269939895 := by
  unfold tailWord_6566245
  simp only [CollatzResearch.WordTrace]
  refine ⟨239490630096623265209876189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159660420064415510139917459 239490630096623265209876189)
  ·
    refine ⟨89808986286233724453703571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239490630096623265209876189 89808986286233724453703571)
    ·
      refine ⟨134713479429350586680555357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89808986286233724453703571 134713479429350586680555357)
      ·
        refine ⟨50517554786006470005208259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134713479429350586680555357 50517554786006470005208259)
        ·
          refine ⟨75776332179009705007812389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50517554786006470005208259 75776332179009705007812389)
          ·
            refine ⟨14208062283564319688964823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75776332179009705007812389 14208062283564319688964823)
            ·
              refine ⟨21312093425346479533447235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208062283564319688964823 21312093425346479533447235)
              ·
                refine ⟨31968140138019719300170853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21312093425346479533447235 31968140138019719300170853)
                ·
                  refine ⟨5994026275878697368782035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31968140138019719300170853 5994026275878697368782035)
                  ·
                    refine ⟨8991039413818046053173053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994026275878697368782035 8991039413818046053173053)
                    ·
                      refine ⟨3371639780181767269939895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991039413818046053173053 3371639780181767269939895)
                      ·
                        rfl

theorem cell23_6566245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_6566245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566245 prefixEnd_6566245 := by exact prefixLift 6566245
  have htrace : WordTrace (prefixWord ++ tailWord_6566245) baseStart_6566245 baseEnd_6566245 := by
    simpa [prefixWord, tailWord_6566245, baseEnd_6566245] using wordTrace_append hprefix tailTrace_6566245
  have hstable : (prefixWord ++ tailWord_6566245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566245).length < 2 ^ (prefixWord ++ tailWord_6566245).sum := by decide
  have hdescent : baseEnd_6566245 < baseStart_6566245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566271 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_6566271 : Nat := 118140960795 + 6566271 * 2 ^ 59
def prefixEnd_6566271 : Nat := 4983230072969 + 3 ^ 40 * 6566271 * 2
def baseEnd_6566271 : Nat := 3371653130678784168214775

theorem tailTrace_6566271 : CollatzResearch.WordTrace tailWord_6566271 prefixEnd_6566271 3371653130678784168214775 := by
  unfold tailWord_6566271
  simp only [CollatzResearch.WordTrace]
  refine ⟨239491578394529071650322667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159661052263019381100215111 239491578394529071650322667)
  ·
    refine ⟨359237367591793607475484001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239491578394529071650322667 359237367591793607475484001)
    ·
      refine ⟨269428025693845205606613001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359237367591793607475484001 269428025693845205606613001)
      ·
        refine ⟨202071019270383904204959751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269428025693845205606613001 202071019270383904204959751)
        ·
          refine ⟨303106528905575856307439627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202071019270383904204959751 303106528905575856307439627)
          ·
            refine ⟨454659793358363784461159441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303106528905575856307439627 454659793358363784461159441)
            ·
              refine ⟨340994845018772838345869581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454659793358363784461159441 340994845018772838345869581)
              ·
                refine ⟨127873066882039814379701093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 340994845018772838345869581 127873066882039814379701093)
                ·
                  refine ⟨23976200040382465196193955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127873066882039814379701093 23976200040382465196193955)
                  ·
                    refine ⟨35964300060573697794290933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23976200040382465196193955 35964300060573697794290933)
                    ·
                      refine ⟨3371653130678784168214775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35964300060573697794290933 3371653130678784168214775)
                      ·
                        rfl

theorem cell23_6566271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_6566271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566271 prefixEnd_6566271 := by exact prefixLift 6566271
  have htrace : WordTrace (prefixWord ++ tailWord_6566271) baseStart_6566271 baseEnd_6566271 := by
    simpa [prefixWord, tailWord_6566271, baseEnd_6566271] using wordTrace_append hprefix tailTrace_6566271
  have hstable : (prefixWord ++ tailWord_6566271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566271).length < 2 ^ (prefixWord ++ tailWord_6566271).sum := by decide
  have hdescent : baseEnd_6566271 < baseStart_6566271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566308 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 7]
def baseStart_6566308 : Nat := 118140960795 + 6566308 * 2 ^ 59
def prefixEnd_6566308 : Nat := 4983230072969 + 3 ^ 40 * 6566308 * 2
def baseEnd_6566308 : Nat := 374630236607000058161345

theorem tailTrace_6566308 : CollatzResearch.WordTrace tailWord_6566308 prefixEnd_6566308 374630236607000058161345 := by
  unfold tailWord_6566308
  simp only [CollatzResearch.WordTrace]
  refine ⟨119746463947697513484709789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159661951930263351312946385 119746463947697513484709789)
  ·
    refine ⟨44904923980386567556766171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119746463947697513484709789 44904923980386567556766171)
    ·
      refine ⟨67357385970579851335149257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44904923980386567556766171 67357385970579851335149257)
      ·
        refine ⟨50518039477934888501361943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67357385970579851335149257 50518039477934888501361943)
        ·
          refine ⟨75777059216902332752042915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50518039477934888501361943 75777059216902332752042915)
          ·
            refine ⟨113665588825353499128064373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75777059216902332752042915 113665588825353499128064373)
            ·
              refine ⟨10656148952376890543256035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113665588825353499128064373 10656148952376890543256035)
              ·
                refine ⟨15984223428565335814884053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10656148952376890543256035 15984223428565335814884053)
                ·
                  refine ⟨374630236607000058161345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15984223428565335814884053 374630236607000058161345)
                  ·
                    rfl

theorem cell23_6566308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_6566308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566308 prefixEnd_6566308 := by exact prefixLift 6566308
  have htrace : WordTrace (prefixWord ++ tailWord_6566308) baseStart_6566308 baseEnd_6566308 := by
    simpa [prefixWord, tailWord_6566308, baseEnd_6566308] using wordTrace_append hprefix tailTrace_6566308
  have hstable : (prefixWord ++ tailWord_6566308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566308).length < 2 ^ (prefixWord ++ tailWord_6566308).sum := by decide
  have hdescent : baseEnd_6566308 < baseStart_6566308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566331 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_6566331 : Nat := 118140960795 + 6566331 * 2 ^ 59
def prefixEnd_6566331 : Nat := 4983230072969 + 3 ^ 40 * 6566331 * 2
def baseEnd_6566331 : Nat := 3371683939518053933464499

theorem tailTrace_6566331 : CollatzResearch.WordTrace tailWord_6566331 prefixEnd_6566331 3371683939518053933464499 := by
  unfold tailWord_6566331
  simp only [CollatzResearch.WordTrace]
  refine ⟨239493766774311701897506847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159662511182874467931671231 239493766774311701897506847)
  ·
    refine ⟨359240650161467552846260271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239493766774311701897506847 359240650161467552846260271)
    ·
      refine ⟨538860975242201329269390407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359240650161467552846260271 538860975242201329269390407)
      ·
        refine ⟨808291462863301993904085611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538860975242201329269390407 808291462863301993904085611)
        ·
          refine ⟨1212437194294952990856128417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808291462863301993904085611 1212437194294952990856128417)
          ·
            refine ⟨909327895721214743142096313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212437194294952990856128417 909327895721214743142096313)
            ·
              refine ⟨681995921790911057356572235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909327895721214743142096313 681995921790911057356572235)
              ·
                refine ⟨1022993882686366586034858353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 681995921790911057356572235 1022993882686366586034858353)
                ·
                  refine ⟨767245412014774939526143765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022993882686366586034858353 767245412014774939526143765)
                  ·
                    refine ⟨35964628688192575290287989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 767245412014774939526143765 35964628688192575290287989)
                    ·
                      refine ⟨3371683939518053933464499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35964628688192575290287989 3371683939518053933464499)
                      ·
                        rfl

theorem cell23_6566331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_6566331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566331 prefixEnd_6566331 := by exact prefixLift 6566331
  have htrace : WordTrace (prefixWord ++ tailWord_6566331) baseStart_6566331 baseEnd_6566331 := by
    simpa [prefixWord, tailWord_6566331, baseEnd_6566331] using wordTrace_append hprefix tailTrace_6566331
  have hstable : (prefixWord ++ tailWord_6566331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566331).length < 2 ^ (prefixWord ++ tailWord_6566331).sum := by decide
  have hdescent : baseEnd_6566331 < baseStart_6566331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566385 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 3, 4]
def baseStart_6566385 : Nat := 118140960795 + 6566385 * 2 ^ 59
def prefixEnd_6566385 : Nat := 4983230072969 + 3 ^ 40 * 6566385 * 2
def baseEnd_6566385 : Nat := 1123903889157798907396417

theorem tailTrace_6566385 : CollatzResearch.WordTrace tailWord_6566385 prefixEnd_6566385 1123903889157798907396417 := by
  unfold tailWord_6566385
  simp only [CollatzResearch.WordTrace]
  refine ⟨239495736316116069119972609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159663824210744046079981739 239495736316116069119972609)
  ·
    refine ⟨179621802237087051839979457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239495736316116069119972609 179621802237087051839979457)
    ·
      refine ⟨134716351677815288879984593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179621802237087051839979457 134716351677815288879984593)
      ·
        refine ⟨101037263758361466659988445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134716351677815288879984593 101037263758361466659988445)
        ·
          refine ⟨37888973909385549997495667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101037263758361466659988445 37888973909385549997495667)
          ·
            refine ⟨56833460864078324996243501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37888973909385549997495667 56833460864078324996243501)
            ·
              refine ⟨21312547824029371873591313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56833460864078324996243501 21312547824029371873591313)
              ·
                refine ⟨15984410868022028905193485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312547824029371873591313 15984410868022028905193485)
                ·
                  refine ⟨5994154075508260839447557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15984410868022028905193485 5994154075508260839447557)
                  ·
                    refine ⟨1123903889157798907396417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994154075508260839447557 1123903889157798907396417)
                    ·
                      rfl

theorem cell23_6566385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 3, 4].length) (baseStart_6566385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566385 prefixEnd_6566385 := by exact prefixLift 6566385
  have htrace : WordTrace (prefixWord ++ tailWord_6566385) baseStart_6566385 baseEnd_6566385 := by
    simpa [prefixWord, tailWord_6566385, baseEnd_6566385] using wordTrace_append hprefix tailTrace_6566385
  have hstable : (prefixWord ++ tailWord_6566385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566385).length < 2 ^ (prefixWord ++ tailWord_6566385).sum := by decide
  have hdescent : baseEnd_6566385 < baseStart_6566385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566389 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 2, 5]
def baseStart_6566389 : Nat := 118140960795 + 6566389 * 2 ^ 59
def prefixEnd_6566389 : Nat := 4983230072969 + 3 ^ 40 * 6566389 * 2
def baseEnd_6566389 : Nat := 1123904573798671568846411

theorem tailTrace_6566389 : CollatzResearch.WordTrace tailWord_6566389 prefixEnd_6566389 1123904573798671568846411 := by
  unfold tailWord_6566389
  simp only [CollatzResearch.WordTrace]
  refine ⟨239495882208101577803118221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159663921472067718535412147 239495882208101577803118221)
  ·
    refine ⟨89810955828038091676169333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239495882208101577803118221 89810955828038091676169333)
    ·
      refine ⟨8419777108878571094640875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89810955828038091676169333 8419777108878571094640875)
      ·
        refine ⟨12629665663317856641961313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8419777108878571094640875 12629665663317856641961313)
        ·
          refine ⟨9472249247488392481470985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12629665663317856641961313 9472249247488392481470985)
          ·
            refine ⟨7104186935616294361103239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9472249247488392481470985 7104186935616294361103239)
            ·
              refine ⟨10656280403424441541654859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104186935616294361103239 10656280403424441541654859)
              ·
                refine ⟨15984420605136662312482289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10656280403424441541654859 15984420605136662312482289)
                ·
                  refine ⟨11988315453852496734361717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15984420605136662312482289 11988315453852496734361717)
                  ·
                    refine ⟨1123904573798671568846411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11988315453852496734361717 1123904573798671568846411)
                    ·
                      rfl

theorem cell23_6566389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_6566389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566389 prefixEnd_6566389 := by exact prefixLift 6566389
  have htrace : WordTrace (prefixWord ++ tailWord_6566389) baseStart_6566389 baseEnd_6566389 := by
    simpa [prefixWord, tailWord_6566389, baseEnd_6566389] using wordTrace_append hprefix tailTrace_6566389
  have hstable : (prefixWord ++ tailWord_6566389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566389).length < 2 ^ (prefixWord ++ tailWord_6566389).sum := by decide
  have hdescent : baseEnd_6566389 < baseStart_6566389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566425 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 3]
def baseStart_6566425 : Nat := 118140960795 + 6566425 * 2 ^ 59
def prefixEnd_6566425 : Nat := 4983230072969 + 3 ^ 40 * 6566425 * 2
def baseEnd_6566425 : Nat := 3371732206699576565689067

theorem tailTrace_6566425 : CollatzResearch.WordTrace tailWord_6566425 prefixEnd_6566425 3371732206699576565689067 := by
  unfold tailWord_6566425
  simp only [CollatzResearch.WordTrace]
  refine ⟨239497195235971155951428729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159664796823980770634285819 239497195235971155951428729)
  ·
    refine ⟨179622896426978366963571547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239497195235971155951428729 179622896426978366963571547)
    ·
      refine ⟨269434344640467550445357321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179622896426978366963571547 269434344640467550445357321)
      ·
        refine ⟨202075758480350662834017991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269434344640467550445357321 202075758480350662834017991)
        ·
          refine ⟨303113637720525994251026987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202075758480350662834017991 303113637720525994251026987)
          ·
            refine ⟨454670456580788991376540481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303113637720525994251026987 454670456580788991376540481)
            ·
              refine ⟨341002842435591743532405361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454670456580788991376540481 341002842435591743532405361)
              ·
                refine ⟨255752131826693807649304021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 341002842435591743532405361 255752131826693807649304021)
                ·
                  refine ⟨5994190589688136116780563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 255752131826693807649304021 5994190589688136116780563)
                  ·
                    refine ⟨8991285884532204175170845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994190589688136116780563 8991285884532204175170845)
                    ·
                      refine ⟨3371732206699576565689067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991285884532204175170845 3371732206699576565689067)
                      ·
                        rfl

theorem cell23_6566425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 7, 1, 3].length) (baseStart_6566425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566425 prefixEnd_6566425 := by exact prefixLift 6566425
  have htrace : WordTrace (prefixWord ++ tailWord_6566425) baseStart_6566425 baseEnd_6566425 := by
    simpa [prefixWord, tailWord_6566425, baseEnd_6566425] using wordTrace_append hprefix tailTrace_6566425
  have hstable : (prefixWord ++ tailWord_6566425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566425).length < 2 ^ (prefixWord ++ tailWord_6566425).sum := by decide
  have hdescent : baseEnd_6566425 < baseStart_6566425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566475 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 4, 4]
def baseStart_6566475 : Nat := 118140960795 + 6566475 * 2 ^ 59
def prefixEnd_6566475 : Nat := 4983230072969 + 3 ^ 40 * 6566475 * 2
def baseEnd_6566475 : Nat := 1123919293577433790021279

theorem tailTrace_6566475 : CollatzResearch.WordTrace tailWord_6566475 prefixEnd_6566475 1123919293577433790021279 := by
  unfold tailWord_6566475
  simp only [CollatzResearch.WordTrace]
  refine ⟨239499018885790014490748879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159666012590526676327165919 239499018885790014490748879)
  ·
    refine ⟨359248528328685021736123319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239499018885790014490748879 359248528328685021736123319)
    ·
      refine ⟨538872792493027532604184979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359248528328685021736123319 538872792493027532604184979)
      ·
        refine ⟨808309188739541298906277469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538872792493027532604184979 808309188739541298906277469)
        ·
          refine ⟨303115945777327987089854051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 808309188739541298906277469 303115945777327987089854051)
          ·
            refine ⟨454673918665991980634781077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303115945777327987089854051 454673918665991980634781077)
            ·
              refine ⟨21312839937468374092255363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 454673918665991980634781077 21312839937468374092255363)
              ·
                refine ⟨31969259906202561138383045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21312839937468374092255363 31969259906202561138383045)
                ·
                  refine ⟨5994236232412980213446821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31969259906202561138383045 5994236232412980213446821)
                  ·
                    refine ⟨1123919293577433790021279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994236232412980213446821 1123919293577433790021279)
                    ·
                      rfl

theorem cell23_6566475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 4, 4].length) (baseStart_6566475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566475 prefixEnd_6566475 := by exact prefixLift 6566475
  have htrace : WordTrace (prefixWord ++ tailWord_6566475) baseStart_6566475 baseEnd_6566475 := by
    simpa [prefixWord, tailWord_6566475, baseEnd_6566475] using wordTrace_append hprefix tailTrace_6566475
  have hstable : (prefixWord ++ tailWord_6566475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566475).length < 2 ^ (prefixWord ++ tailWord_6566475).sum := by decide
  have hdescent : baseEnd_6566475 < baseStart_6566475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566476 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 1, 1, 3]
def baseStart_6566476 : Nat := 118140960795 + 6566476 * 2 ^ 59
def prefixEnd_6566476 : Nat := 4983230072969 + 3 ^ 40 * 6566476 * 2
def baseEnd_6566476 : Nat := 3371758394212955866151333

theorem tailTrace_6566476 : CollatzResearch.WordTrace tailWord_6566476 prefixEnd_6566476 3371758394212955866151333 := by
  unfold tailWord_6566476
  simp only [CollatzResearch.WordTrace]
  refine ⟨119749527679393195830767641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159666036905857594441023521 119749527679393195830767641)
  ·
    refine ⟨89812145759544896873075731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119749527679393195830767641 89812145759544896873075731)
    ·
      refine ⟨134718218639317345309613597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89812145759544896873075731 134718218639317345309613597)
      ·
        refine ⟨50519331989744004491105099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134718218639317345309613597 50519331989744004491105099)
        ·
          refine ⟨75778997984616006736657649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50519331989744004491105099 75778997984616006736657649)
          ·
            refine ⟨56834248488462005052493237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75778997984616006736657649 56834248488462005052493237)
            ·
              refine ⟨5328210795793312973671241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56834248488462005052493237 5328210795793312973671241)
              ·
                refine ⟨3996158096844984730253431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328210795793312973671241 3996158096844984730253431)
                ·
                  refine ⟨5994237145267477095380147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996158096844984730253431 5994237145267477095380147)
                  ·
                    refine ⟨8991355717901215643070221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994237145267477095380147 8991355717901215643070221)
                    ·
                      refine ⟨3371758394212955866151333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991355717901215643070221 3371758394212955866151333)
                      ·
                        rfl

theorem cell23_6566476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 1, 1, 3].length) (baseStart_6566476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566476 prefixEnd_6566476 := by exact prefixLift 6566476
  have htrace : WordTrace (prefixWord ++ tailWord_6566476) baseStart_6566476 baseEnd_6566476 := by
    simpa [prefixWord, tailWord_6566476, baseEnd_6566476] using wordTrace_append hprefix tailTrace_6566476
  have hstable : (prefixWord ++ tailWord_6566476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566476).length < 2 ^ (prefixWord ++ tailWord_6566476).sum := by decide
  have hdescent : baseEnd_6566476 < baseStart_6566476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566485 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 5]
def baseStart_6566485 : Nat := 118140960795 + 6566485 * 2 ^ 59
def prefixEnd_6566485 : Nat := 4983230072969 + 3 ^ 40 * 6566485 * 2
def baseEnd_6566485 : Nat := 3371763015538846330938791

theorem tailTrace_6566485 : CollatzResearch.WordTrace tailWord_6566485 prefixEnd_6566485 3371763015538846330938791 := by
  unfold tailWord_6566485
  simp only [CollatzResearch.WordTrace]
  refine ⟨239499383615753786198612909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159666255743835857465741939 239499383615753786198612909)
  ·
    refine ⟨89812268855907669824479841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239499383615753786198612909 89812268855907669824479841)
    ·
      refine ⟨67359201641930752368359881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89812268855907669824479841 67359201641930752368359881)
      ·
        refine ⟨50519401231448064276269911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67359201641930752368359881 50519401231448064276269911)
        ·
          refine ⟨75779101847172096414404867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50519401231448064276269911 75779101847172096414404867)
          ·
            refine ⟨113668652770758144621607301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75779101847172096414404867 113668652770758144621607301)
            ·
              refine ⟨21312872394517152116551369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 113668652770758144621607301 21312872394517152116551369)
              ·
                refine ⟨15984654295887864087413527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312872394517152116551369 15984654295887864087413527)
                ·
                  refine ⟨23976981443831796131120291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15984654295887864087413527 23976981443831796131120291)
                  ·
                    refine ⟨35965472165747694196680437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23976981443831796131120291 35965472165747694196680437)
                    ·
                      refine ⟨3371763015538846330938791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35965472165747694196680437 3371763015538846330938791)
                      ·
                        rfl

theorem cell23_6566485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_6566485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566485 prefixEnd_6566485 := by exact prefixLift 6566485
  have htrace : WordTrace (prefixWord ++ tailWord_6566485) baseStart_6566485 baseEnd_6566485 := by
    simpa [prefixWord, tailWord_6566485, baseEnd_6566485] using wordTrace_append hprefix tailTrace_6566485
  have hstable : (prefixWord ++ tailWord_6566485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566485).length < 2 ^ (prefixWord ++ tailWord_6566485).sum := by decide
  have hdescent : baseEnd_6566485 < baseStart_6566485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566488 : List Nat := [2, 1, 2, 2, 1, 2, 3, 10]
def baseStart_6566488 : Nat := 118140960795 + 6566488 * 2 ^ 59
def prefixEnd_6566488 : Nat := 4983230072969 + 3 ^ 40 * 6566488 * 2
def baseEnd_6566488 : Nat := 124880168740029993303751

theorem tailTrace_6566488 : CollatzResearch.WordTrace tailWord_6566488 prefixEnd_6566488 124880168740029993303751 := by
  unfold tailWord_6566488
  simp only [CollatzResearch.WordTrace]
  refine ⟨119749746517371458855486059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159666328689828611807314745 119749746517371458855486059)
  ·
    refine ⟨179624619776057188283229089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119749746517371458855486059 179624619776057188283229089)
    ·
      refine ⟨134718464832042891212421817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179624619776057188283229089 134718464832042891212421817)
      ·
        refine ⟨101038848624032168409316363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134718464832042891212421817 101038848624032168409316363)
        ·
          refine ⟨151558272936048252613974545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101038848624032168409316363 151558272936048252613974545)
          ·
            refine ⟨113668704702036189460480909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151558272936048252613974545 113668704702036189460480909)
            ·
              refine ⟨42625764263263571047680341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113668704702036189460480909 42625764263263571047680341)
              ·
                refine ⟨124880168740029993303751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42625764263263571047680341 124880168740029993303751)
                ·
                  rfl

theorem cell23_6566488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 10].length) (baseStart_6566488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566488 prefixEnd_6566488 := by exact prefixLift 6566488
  have htrace : WordTrace (prefixWord ++ tailWord_6566488) baseStart_6566488 baseEnd_6566488 := by
    simpa [prefixWord, tailWord_6566488, baseEnd_6566488] using wordTrace_append hprefix tailTrace_6566488
  have hstable : (prefixWord ++ tailWord_6566488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566488).length < 2 ^ (prefixWord ++ tailWord_6566488).sum := by decide
  have hdescent : baseEnd_6566488 < baseStart_6566488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566512 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4]
def baseStart_6566512 : Nat := 118140960795 + 6566512 * 2 ^ 59
def prefixEnd_6566512 : Nat := 4983230072969 + 3 ^ 40 * 6566512 * 2
def baseEnd_6566512 : Nat := 3371776879516517725301167

theorem tailTrace_6566512 : CollatzResearch.WordTrace tailWord_6566512 prefixEnd_6566512 3371776879516517725301167 := by
  unfold tailWord_6566512
  simp only [CollatzResearch.WordTrace]
  refine ⟨119750184193327984904922895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159666912257770646539897193 119750184193327984904922895)
  ·
    refine ⟨179625276289991977357384343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119750184193327984904922895 179625276289991977357384343)
    ·
      refine ⟨269437914434987966036076515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179625276289991977357384343 269437914434987966036076515)
      ·
        refine ⟨404156871652481949054114773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269437914434987966036076515 404156871652481949054114773)
        ·
          refine ⟨9472426679355045680955815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 404156871652481949054114773 9472426679355045680955815)
          ·
            refine ⟨14208640019032568521433723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9472426679355045680955815 14208640019032568521433723)
            ·
              refine ⟨21312960028548852782150585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208640019032568521433723 21312960028548852782150585)
              ·
                refine ⟨15984720021411639586612939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21312960028548852782150585 15984720021411639586612939)
                ·
                  refine ⟨23977080032117459379919409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15984720021411639586612939 23977080032117459379919409)
                  ·
                    refine ⟨17982810024088094534939557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23977080032117459379919409 17982810024088094534939557)
                    ·
                      refine ⟨3371776879516517725301167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17982810024088094534939557 3371776879516517725301167)
                      ·
                        rfl

theorem cell23_6566512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 4].length) (baseStart_6566512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566512 prefixEnd_6566512 := by exact prefixLift 6566512
  have htrace : WordTrace (prefixWord ++ tailWord_6566512) baseStart_6566512 baseEnd_6566512 := by
    simpa [prefixWord, tailWord_6566512, baseEnd_6566512] using wordTrace_append hprefix tailTrace_6566512
  have hstable : (prefixWord ++ tailWord_6566512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566512).length < 2 ^ (prefixWord ++ tailWord_6566512).sum := by decide
  have hdescent : baseEnd_6566512 < baseStart_6566512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566533 : List Nat := [1, 3, 1, 1, 4, 2, 4, 2, 1, 2, 2]
def baseStart_6566533 : Nat := 118140960795 + 6566533 * 2 ^ 59
def prefixEnd_6566533 : Nat := 4983230072969 + 3 ^ 40 * 6566533 * 2
def baseEnd_6566533 : Nat := 3371787662610262143138571

theorem tailTrace_6566533 : CollatzResearch.WordTrace tailWord_6566533 prefixEnd_6566533 3371787662610262143138571 := by
  unfold tailWord_6566533
  simp only [CollatzResearch.WordTrace]
  refine ⟨239501134319579890396360253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159667422879719926930906835 239501134319579890396360253)
  ·
    refine ⟨89812925369842458898635095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239501134319579890396360253 89812925369842458898635095)
    ·
      refine ⟨134719388054763688347952643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89812925369842458898635095 134719388054763688347952643)
      ·
        refine ⟨202079082082145532521928965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134719388054763688347952643 202079082082145532521928965)
        ·
          refine ⟨37889827890402287347861681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202079082082145532521928965 37889827890402287347861681)
          ·
            refine ⟨28417370917801715510896261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37889827890402287347861681 28417370917801715510896261)
            ·
              refine ⟨5328257047087821658293049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28417370917801715510896261 5328257047087821658293049)
              ·
                refine ⟨3996192785315866243719787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328257047087821658293049 3996192785315866243719787)
                ·
                  refine ⟨5994289177973799365579681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996192785315866243719787 5994289177973799365579681)
                  ·
                    refine ⟨4495716883480349524184761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994289177973799365579681 4495716883480349524184761)
                    ·
                      refine ⟨3371787662610262143138571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495716883480349524184761 3371787662610262143138571)
                      ·
                        rfl

theorem cell23_6566533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 4, 2, 1, 2, 2].length) (baseStart_6566533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566533 prefixEnd_6566533 := by exact prefixLift 6566533
  have htrace : WordTrace (prefixWord ++ tailWord_6566533) baseStart_6566533 baseEnd_6566533 := by
    simpa [prefixWord, tailWord_6566533, baseEnd_6566533] using wordTrace_append hprefix tailTrace_6566533
  have hstable : (prefixWord ++ tailWord_6566533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566533).length < 2 ^ (prefixWord ++ tailWord_6566533).sum := by decide
  have hdescent : baseEnd_6566533 < baseStart_6566533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566570 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_6566570 : Nat := 118140960795 + 6566570 * 2 ^ 59
def prefixEnd_6566570 : Nat := 4983230072969 + 3 ^ 40 * 6566570 * 2
def baseEnd_6566570 : Nat := 3371806661394478498375901

theorem tailTrace_6566570 : CollatzResearch.WordTrace tailWord_6566570 prefixEnd_6566570 3371806661394478498375901 := by
  unfold tailWord_6566570
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875620955111461428864291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159668322546963897143638109 59875620955111461428864291)
  ·
    refine ⟨89813431432667192143296437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59875620955111461428864291 89813431432667192143296437)
    ·
      refine ⟨8420009196812549263434041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89813431432667192143296437 8420009196812549263434041)
      ·
        refine ⟨6315006897609411947575531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8420009196812549263434041 6315006897609411947575531)
        ·
          refine ⟨9472510346414117921363297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315006897609411947575531 9472510346414117921363297)
          ·
            refine ⟨7104382759810588441022473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9472510346414117921363297 7104382759810588441022473)
            ·
              refine ⟨5328287069857941330766855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7104382759810588441022473 5328287069857941330766855)
              ·
                refine ⟨7992430604786911996150283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328287069857941330766855 7992430604786911996150283)
                ·
                  refine ⟨11988645907180367994225425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7992430604786911996150283 11988645907180367994225425)
                  ·
                    refine ⟨8991484430385275995669069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11988645907180367994225425 8991484430385275995669069)
                    ·
                      refine ⟨3371806661394478498375901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991484430385275995669069 3371806661394478498375901)
                      ·
                        rfl

theorem cell23_6566570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_6566570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566570 prefixEnd_6566570 := by exact prefixLift 6566570
  have htrace : WordTrace (prefixWord ++ tailWord_6566570) baseStart_6566570 baseEnd_6566570 := by
    simpa [prefixWord, tailWord_6566570, baseEnd_6566570] using wordTrace_append hprefix tailTrace_6566570
  have hstable : (prefixWord ++ tailWord_6566570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566570).length < 2 ^ (prefixWord ++ tailWord_6566570).sum := by decide
  have hdescent : baseEnd_6566570 < baseStart_6566570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566583 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 2, 1, 3]
def baseStart_6566583 : Nat := 118140960795 + 6566583 * 2 ^ 59
def prefixEnd_6566583 : Nat := 4983230072969 + 3 ^ 40 * 6566583 * 2
def baseEnd_6566583 : Nat := 3371813336642986947513341

theorem tailTrace_6566583 : CollatzResearch.WordTrace tailWord_6566583 prefixEnd_6566583 3371813336642986947513341 := by
  unfold tailWord_6566583
  simp only [CollatzResearch.WordTrace]
  refine ⟨239502957969398748935680403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159668638646265832623786935 239502957969398748935680403)
  ·
    refine ⟨359254436954098123403520605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239502957969398748935680403 359254436954098123403520605)
    ·
      refine ⟨134720413857786796276320227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 359254436954098123403520605 134720413857786796276320227)
      ·
        refine ⟨202080620786680194414480341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134720413857786796276320227 202080620786680194414480341)
        ·
          refine ⟨4736264549687817056589383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 202080620786680194414480341 4736264549687817056589383)
          ·
            refine ⟨7104396824531725584884075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736264549687817056589383 7104396824531725584884075)
            ·
              refine ⟨10656595236797588377326113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104396824531725584884075 10656595236797588377326113)
              ·
                refine ⟨7992446427598191282994585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10656595236797588377326113 7992446427598191282994585)
                ·
                  refine ⟨5994334820698643462245939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992446427598191282994585 5994334820698643462245939)
                  ·
                    refine ⟨8991502231047965193368909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994334820698643462245939 8991502231047965193368909)
                    ·
                      refine ⟨3371813336642986947513341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991502231047965193368909 3371813336642986947513341)
                      ·
                        rfl

theorem cell23_6566583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 2, 1, 3].length) (baseStart_6566583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566583 prefixEnd_6566583 := by exact prefixLift 6566583
  have htrace : WordTrace (prefixWord ++ tailWord_6566583) baseStart_6566583 baseEnd_6566583 := by
    simpa [prefixWord, tailWord_6566583, baseEnd_6566583] using wordTrace_append hprefix tailTrace_6566583
  have hstable : (prefixWord ++ tailWord_6566583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566583).length < 2 ^ (prefixWord ++ tailWord_6566583).sum := by decide
  have hdescent : baseEnd_6566583 < baseStart_6566583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566602 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_6566602 : Nat := 118140960795 + 6566602 * 2 ^ 59
def prefixEnd_6566602 : Nat := 4983230072969 + 3 ^ 40 * 6566602 * 2
def baseEnd_6566602 : Nat := 3371823092775422373175753

theorem tailTrace_6566602 : CollatzResearch.WordTrace tailWord_6566602 prefixEnd_6566602 3371823092775422373175753 := by
  unfold tailWord_6566602
  simp only [CollatzResearch.WordTrace]
  refine ⟨59875912739082478795155515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159669100637553276787081373 59875912739082478795155515)
  ·
    refine ⟨89813869108623718192733273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59875912739082478795155515 89813869108623718192733273)
    ·
      refine ⟨67360401831467788644549955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89813869108623718192733273 67360401831467788644549955)
      ·
        refine ⟨101040602747201682966824933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67360401831467788644549955 101040602747201682966824933)
        ·
          refine ⟨18945113015100315556279675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101040602747201682966824933 18945113015100315556279675)
          ·
            refine ⟨28417669522650473334419513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18945113015100315556279675 28417669522650473334419513)
            ·
              refine ⟨21313252141987855000814635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28417669522650473334419513 21313252141987855000814635)
              ·
                refine ⟨31969878212981782501221953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21313252141987855000814635 31969878212981782501221953)
                ·
                  refine ⟨23977408659736336875916465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31969878212981782501221953 23977408659736336875916465)
                  ·
                    refine ⟨17983056494802252656937349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23977408659736336875916465 17983056494802252656937349)
                    ·
                      refine ⟨3371823092775422373175753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17983056494802252656937349 3371823092775422373175753)
                      ·
                        rfl

theorem cell23_6566602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_6566602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566602 prefixEnd_6566602 := by exact prefixLift 6566602
  have htrace : WordTrace (prefixWord ++ tailWord_6566602) baseStart_6566602 baseEnd_6566602 := by
    simpa [prefixWord, tailWord_6566602, baseEnd_6566602] using wordTrace_append hprefix tailTrace_6566602
  have hstable : (prefixWord ++ tailWord_6566602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566602).length < 2 ^ (prefixWord ++ tailWord_6566602).sum := by decide
  have hdescent : baseEnd_6566602 < baseStart_6566602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566606 : List Nat := [4, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_6566606 : Nat := 118140960795 + 6566606 * 2 ^ 59
def prefixEnd_6566606 : Nat := 4983230072969 + 3 ^ 40 * 6566606 * 2
def baseEnd_6566606 : Nat := 3371825146698040357525735

theorem tailTrace_6566606 : CollatzResearch.WordTrace tailWord_6566606 prefixEnd_6566606 3371825146698040357525735 := by
  unfold tailWord_6566606
  simp only [CollatzResearch.WordTrace]
  refine ⟨29937974606039427982970959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159669197898876949242511781 29937974606039427982970959)
  ·
    refine ⟨44906961909059141974456439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29937974606039427982970959 44906961909059141974456439)
    ·
      refine ⟨67360442863588712961684659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44906961909059141974456439 67360442863588712961684659)
      ·
        refine ⟨101040664295383069442526989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67360442863588712961684659 101040664295383069442526989)
        ·
          refine ⟨37890249110768651040947621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101040664295383069442526989 37890249110768651040947621)
          ·
            refine ⟨7104421708269122070177679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37890249110768651040947621 7104421708269122070177679)
            ·
              refine ⟨10656632562403683105266519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7104421708269122070177679 10656632562403683105266519)
              ·
                refine ⟨15984948843605524657899779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10656632562403683105266519 15984948843605524657899779)
                ·
                  refine ⟨23977423265408286986849669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15984948843605524657899779 23977423265408286986849669)
                  ·
                    refine ⟨4495766862264053810034313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23977423265408286986849669 4495766862264053810034313)
                    ·
                      refine ⟨3371825146698040357525735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495766862264053810034313 3371825146698040357525735)
                      ·
                        rfl

theorem cell23_6566606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_6566606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566606 prefixEnd_6566606 := by exact prefixLift 6566606
  have htrace : WordTrace (prefixWord ++ tailWord_6566606) baseStart_6566606 baseEnd_6566606 := by
    simpa [prefixWord, tailWord_6566606, baseEnd_6566606] using wordTrace_append hprefix tailTrace_6566606
  have hstable : (prefixWord ++ tailWord_6566606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566606).length < 2 ^ (prefixWord ++ tailWord_6566606).sum := by decide
  have hdescent : baseEnd_6566606 < baseStart_6566606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566629 : List Nat := [1, 3, 1, 4, 1, 2, 3, 3, 5]
def baseStart_6566629 : Nat := 118140960795 + 6566629 * 2 ^ 59
def prefixEnd_6566629 : Nat := 4983230072969 + 3 ^ 40 * 6566629 * 2
def baseEnd_6566629 : Nat := 374648550750343751948681

theorem tailTrace_6566629 : CollatzResearch.WordTrace tailWord_6566629 prefixEnd_6566629 374648550750343751948681 := by
  unfold tailWord_6566629
  simp only [CollatzResearch.WordTrace]
  refine ⟨239504635727232098791854941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159669757151488065861236627 239504635727232098791854941)
  ·
    refine ⟨89814238397712037046945603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239504635727232098791854941 89814238397712037046945603)
    ·
      refine ⟨134721357596568055570418405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89814238397712037046945603 134721357596568055570418405)
      ·
        refine ⟨25260254549356510419453451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134721357596568055570418405 25260254549356510419453451)
        ·
          refine ⟨37890381824034765629180177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25260254549356510419453451 37890381824034765629180177)
          ·
            refine ⟨28417786368026074221885133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37890381824034765629180177 28417786368026074221885133)
            ·
              refine ⟨10656669888009777833206925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28417786368026074221885133 10656669888009777833206925)
              ·
                refine ⟨3996251208003666687452597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10656669888009777833206925 3996251208003666687452597)
                ·
                  refine ⟨374648550750343751948681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3996251208003666687452597 374648550750343751948681)
                  ·
                    rfl

theorem cell23_6566629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 3, 5].length) (baseStart_6566629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566629 prefixEnd_6566629 := by exact prefixLift 6566629
  have htrace : WordTrace (prefixWord ++ tailWord_6566629) baseStart_6566629 baseEnd_6566629 := by
    simpa [prefixWord, tailWord_6566629, baseEnd_6566629] using wordTrace_append hprefix tailTrace_6566629
  have hstable : (prefixWord ++ tailWord_6566629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566629).length < 2 ^ (prefixWord ++ tailWord_6566629).sum := by decide
  have hdescent : baseEnd_6566629 < baseStart_6566629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566635 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5]
def baseStart_6566635 : Nat := 118140960795 + 6566635 * 2 ^ 59
def prefixEnd_6566635 : Nat := 4983230072969 + 3 ^ 40 * 6566635 * 2
def baseEnd_6566635 : Nat := 3371840037637020744063101

theorem tailTrace_6566635 : CollatzResearch.WordTrace tailWord_6566635 prefixEnd_6566635 3371840037637020744063101 := by
  unfold tailWord_6566635
  simp only [CollatzResearch.WordTrace]
  refine ⟨239504854565210361816573359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159669903043473574544382239 239504854565210361816573359)
  ·
    refine ⟨359257281847815542724860039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239504854565210361816573359 359257281847815542724860039)
    ·
      refine ⟨538885922771723314087290059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359257281847815542724860039 538885922771723314087290059)
      ·
        refine ⟨808328884157584971130935089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538885922771723314087290059 808328884157584971130935089)
        ·
          refine ⟨606246663118188728348201317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808328884157584971130935089 606246663118188728348201317)
          ·
            refine ⟨113671249334660386565287747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 606246663118188728348201317 113671249334660386565287747)
            ·
              refine ⟨170506874001990579847931621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113671249334660386565287747 170506874001990579847931621)
              ·
                refine ⟨31970038875373233721487179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 170506874001990579847931621 31970038875373233721487179)
                ·
                  refine ⟨47955058313059850582230769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31970038875373233721487179 47955058313059850582230769)
                  ·
                    refine ⟨35966293734794887936673077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47955058313059850582230769 35966293734794887936673077)
                    ·
                      refine ⟨3371840037637020744063101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35966293734794887936673077 3371840037637020744063101)
                      ·
                        rfl

theorem cell23_6566635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_6566635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566635 prefixEnd_6566635 := by exact prefixLift 6566635
  have htrace : WordTrace (prefixWord ++ tailWord_6566635) baseStart_6566635 baseEnd_6566635 := by
    simpa [prefixWord, tailWord_6566635, baseEnd_6566635] using wordTrace_append hprefix tailTrace_6566635
  have hstable : (prefixWord ++ tailWord_6566635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566635).length < 2 ^ (prefixWord ++ tailWord_6566635).sum := by decide
  have hdescent : baseEnd_6566635 < baseStart_6566635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566642 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_6566642 : Nat := 118140960795 + 6566642 * 2 ^ 59
def prefixEnd_6566642 : Nat := 4983230072969 + 3 ^ 40 * 6566642 * 2
def baseEnd_6566642 : Nat := 1123947877333867405558523

theorem tailTrace_6566642 : CollatzResearch.WordTrace tailWord_6566642 prefixEnd_6566642 1123947877333867405558523 := by
  unfold tailWord_6566642
  simp only [CollatzResearch.WordTrace]
  refine ⟨59876277469046250503019545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159670073250790001341385453 59876277469046250503019545)
  ·
    refine ⟨44907208101784687877264659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59876277469046250503019545 44907208101784687877264659)
    ·
      refine ⟨67360812152677031815896989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44907208101784687877264659 67360812152677031815896989)
      ·
        refine ⟨25260304557253886930961371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67360812152677031815896989 25260304557253886930961371)
        ·
          refine ⟨37890456835880830396442057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25260304557253886930961371 37890456835880830396442057)
          ·
            refine ⟨28417842626910622797331543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37890456835880830396442057 28417842626910622797331543)
            ·
              refine ⟨42626763940365934195997315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28417842626910622797331543 42626763940365934195997315)
              ·
                refine ⟨63940145910548901293995973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42626763940365934195997315 63940145910548901293995973)
                ·
                  refine ⟨11988777358227918992624245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63940145910548901293995973 11988777358227918992624245)
                  ·
                    refine ⟨1123947877333867405558523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11988777358227918992624245 1123947877333867405558523)
                    ·
                      rfl

theorem cell23_6566642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_6566642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566642 prefixEnd_6566642 := by exact prefixLift 6566642
  have htrace : WordTrace (prefixWord ++ tailWord_6566642) baseStart_6566642 baseEnd_6566642 := by
    simpa [prefixWord, tailWord_6566642, baseEnd_6566642] using wordTrace_append hprefix tailTrace_6566642
  have hstable : (prefixWord ++ tailWord_6566642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566642).length < 2 ^ (prefixWord ++ tailWord_6566642).sum := by decide
  have hdescent : baseEnd_6566642 < baseStart_6566642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566646 : List Nat := [5, 1, 1, 1, 1, 2, 5, 2, 5]
def baseStart_6566646 : Nat := 118140960795 + 6566646 * 2 ^ 59
def prefixEnd_6566646 : Nat := 4983230072969 + 3 ^ 40 * 6566646 * 2
def baseEnd_6566646 : Nat := 374649520658246689002839

theorem tailTrace_6566646 : CollatzResearch.WordTrace tailWord_6566646 prefixEnd_6566646 374649520658246689002839 := by
  unfold tailWord_6566646
  simp only [CollatzResearch.WordTrace]
  refine ⟨14969078485510656918451487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159670170512113673796815861 14969078485510656918451487)
  ·
    refine ⟨22453617728265985377677231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14969078485510656918451487 22453617728265985377677231)
    ·
      refine ⟨33680426592398978066515847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22453617728265985377677231 33680426592398978066515847)
      ·
        refine ⟨50520639888598467099773771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33680426592398978066515847 50520639888598467099773771)
        ·
          refine ⟨75780959832897700649660657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50520639888598467099773771 75780959832897700649660657)
          ·
            refine ⟨56835719874673275487245493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75780959832897700649660657 56835719874673275487245493)
            ·
              refine ⟨5328348738250619576929265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56835719874673275487245493 5328348738250619576929265)
              ·
                refine ⟨3996261553687964682696949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5328348738250619576929265 3996261553687964682696949)
                ·
                  refine ⟨374649520658246689002839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3996261553687964682696949 374649520658246689002839)
                  ·
                    rfl

theorem cell23_6566646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_6566646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566646 prefixEnd_6566646 := by exact prefixLift 6566646
  have htrace : WordTrace (prefixWord ++ tailWord_6566646) baseStart_6566646 baseEnd_6566646 := by
    simpa [prefixWord, tailWord_6566646, baseEnd_6566646] using wordTrace_append hprefix tailTrace_6566646
  have hstable : (prefixWord ++ tailWord_6566646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566646).length < 2 ^ (prefixWord ++ tailWord_6566646).sum := by decide
  have hdescent : baseEnd_6566646 < baseStart_6566646 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566652 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 1, 2, 5]
def baseStart_6566652 : Nat := 118140960795 + 6566652 * 2 ^ 59
def prefixEnd_6566652 : Nat := 4983230072969 + 3 ^ 40 * 6566652 * 2
def baseEnd_6566652 : Nat := 3371848766808147177550523

theorem tailTrace_6566652 : CollatzResearch.WordTrace tailWord_6566652 prefixEnd_6566652 3371848766808147177550523 := by
  unfold tailWord_6566652
  simp only [CollatzResearch.WordTrace]
  refine ⟨119752737303074386859971105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159670316404099182479961473 119752737303074386859971105)
  ·
    refine ⟨89814552977305790144978329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119752737303074386859971105 89814552977305790144978329)
    ·
      refine ⟨67360914732979342608733747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89814552977305790144978329 67360914732979342608733747)
      ·
        refine ⟨101041372099469013913100621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67360914732979342608733747 101041372099469013913100621)
        ·
          refine ⟨37890514537300880217412733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101041372099469013913100621 37890514537300880217412733)
          ·
            refine ⟨14208942951487830081529775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37890514537300880217412733 14208942951487830081529775)
            ·
              refine ⟨21313414427231745122294663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14208942951487830081529775 21313414427231745122294663)
              ·
                refine ⟨31970121640847617683441995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21313414427231745122294663 31970121640847617683441995)
                ·
                  refine ⟨47955182461271426525162993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31970121640847617683441995 47955182461271426525162993)
                  ·
                    refine ⟨35966386845953569893872245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47955182461271426525162993 35966386845953569893872245)
                    ·
                      refine ⟨3371848766808147177550523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35966386845953569893872245 3371848766808147177550523)
                      ·
                        rfl

theorem cell23_6566652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_6566652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566652 prefixEnd_6566652 := by exact prefixLift 6566652
  have htrace : WordTrace (prefixWord ++ tailWord_6566652) baseStart_6566652 baseEnd_6566652 := by
    simpa [prefixWord, tailWord_6566652, baseEnd_6566652] using wordTrace_append hprefix tailTrace_6566652
  have hstable : (prefixWord ++ tailWord_6566652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566652).length < 2 ^ (prefixWord ++ tailWord_6566652).sum := by decide
  have hdescent : baseEnd_6566652 < baseStart_6566652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566706 : List Nat := [3, 2, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_6566706 : Nat := 118140960795 + 6566706 * 2 ^ 59
def prefixEnd_6566706 : Nat := 4983230072969 + 3 ^ 40 * 6566706 * 2
def baseEnd_6566706 : Nat := 1123958831587829988758425

theorem tailTrace_6566706 : CollatzResearch.WordTrace tailWord_6566706 prefixEnd_6566706 1123958831587829988758425 := by
  unfold tailWord_6566706
  simp only [CollatzResearch.WordTrace]
  refine ⟨59876861036988285235601993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159671629431968760628271981 59876861036988285235601993)
  ·
    refine ⟨44907645777741213926701495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59876861036988285235601993 44907645777741213926701495)
    ·
      refine ⟨67361468666611820890052243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44907645777741213926701495 67361468666611820890052243)
      ·
        refine ⟨101042202999917731335078365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67361468666611820890052243 101042202999917731335078365)
        ·
          refine ⟨37890826124969149250654387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101042202999917731335078365 37890826124969149250654387)
          ·
            refine ⟨56836239187453723875981581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37890826124969149250654387 56836239187453723875981581)
            ·
              refine ⟨21313589695295146453493093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56836239187453723875981581 21313589695295146453493093)
              ·
                refine ⟨3996298067867839960029955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21313589695295146453493093 3996298067867839960029955)
                ·
                  refine ⟨5994447101801759940044933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996298067867839960029955 5994447101801759940044933)
                  ·
                    refine ⟨1123958831587829988758425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994447101801759940044933 1123958831587829988758425)
                    ·
                      rfl

theorem cell23_6566706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_6566706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566706 prefixEnd_6566706 := by exact prefixLift 6566706
  have htrace : WordTrace (prefixWord ++ tailWord_6566706) baseStart_6566706 baseEnd_6566706 := by
    simpa [prefixWord, tailWord_6566706, baseEnd_6566706] using wordTrace_append hprefix tailTrace_6566706
  have hstable : (prefixWord ++ tailWord_6566706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566706).length < 2 ^ (prefixWord ++ tailWord_6566706).sum := by decide
  have hdescent : baseEnd_6566706 < baseStart_6566706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566729 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 3]
def baseStart_6566729 : Nat := 118140960795 + 6566729 * 2 ^ 59
def prefixEnd_6566729 : Nat := 4983230072969 + 3 ^ 40 * 6566729 * 2
def baseEnd_6566729 : Nat := 3371888304818543376287669

theorem tailTrace_6566729 : CollatzResearch.WordTrace tailWord_6566729 prefixEnd_6566729 3371888304818543376287669 := by
  unfold tailWord_6566729
  simp only [CollatzResearch.WordTrace]
  refine ⟨239508283026869815870495241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159672188684579877246996827 239508283026869815870495241)
  ·
    refine ⟨179631212270152361902871431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239508283026869815870495241 179631212270152361902871431)
    ·
      refine ⟨269446818405228542854307147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179631212270152361902871431 269446818405228542854307147)
      ·
        refine ⟨404170227607842814281460721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269446818405228542854307147 404170227607842814281460721)
        ·
          refine ⟨303127670705882110711095541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 404170227607842814281460721 303127670705882110711095541)
          ·
            refine ⟨28418219128676447879165207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 303127670705882110711095541 28418219128676447879165207)
            ·
              refine ⟨42627328693014671818747811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28418219128676447879165207 42627328693014671818747811)
              ·
                refine ⟨63940993039522007728121717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42627328693014671818747811 63940993039522007728121717)
                ·
                  refine ⟨5994468097455188224511411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63940993039522007728121717 5994468097455188224511411)
                  ·
                    refine ⟨8991702146182782336767117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994468097455188224511411 8991702146182782336767117)
                    ·
                      refine ⟨3371888304818543376287669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991702146182782336767117 3371888304818543376287669)
                      ·
                        rfl

theorem cell23_6566729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 5, 1, 3].length) (baseStart_6566729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566729 prefixEnd_6566729 := by exact prefixLift 6566729
  have htrace : WordTrace (prefixWord ++ tailWord_6566729) baseStart_6566729 baseEnd_6566729 := by
    simpa [prefixWord, tailWord_6566729, baseEnd_6566729] using wordTrace_append hprefix tailTrace_6566729
  have hstable : (prefixWord ++ tailWord_6566729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566729).length < 2 ^ (prefixWord ++ tailWord_6566729).sum := by decide
  have hdescent : baseEnd_6566729 < baseStart_6566729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566779 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 2, 4]
def baseStart_6566779 : Nat := 118140960795 + 6566779 * 2 ^ 59
def prefixEnd_6566779 : Nat := 4983230072969 + 3 ^ 40 * 6566779 * 2
def baseEnd_6566779 : Nat := 1123971326283756060220813

theorem tailTrace_6566779 : CollatzResearch.WordTrace tailWord_6566779 prefixEnd_6566779 1123971326283756060220813 := by
  unfold tailWord_6566779
  simp only [CollatzResearch.WordTrace]
  refine ⟨239510106676688674409815391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159673404451125782939876927 239510106676688674409815391)
  ·
    refine ⟨359265160015033011614723087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239510106676688674409815391 359265160015033011614723087)
    ·
      refine ⟨538897740022549517422084631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359265160015033011614723087 538897740022549517422084631)
      ·
        refine ⟨808346610033824276133126947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538897740022549517422084631 808346610033824276133126947)
        ·
          refine ⟨1212519915050736414199690421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808346610033824276133126947 1212519915050736414199690421)
          ·
            refine ⟨113673742036006538831220977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1212519915050736414199690421 113673742036006538831220977)
            ·
              refine ⟨85255306527004904123415733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113673742036006538831220977 85255306527004904123415733)
              ·
                refine ⟨7992684986906709761570225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85255306527004904123415733 7992684986906709761570225)
                ·
                  refine ⟨5994513740180032321177669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992684986906709761570225 5994513740180032321177669)
                  ·
                    refine ⟨1123971326283756060220813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994513740180032321177669 1123971326283756060220813)
                    ·
                      rfl

theorem cell23_6566779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2, 4].length) (baseStart_6566779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566779 prefixEnd_6566779 := by exact prefixLift 6566779
  have htrace : WordTrace (prefixWord ++ tailWord_6566779) baseStart_6566779 baseEnd_6566779 := by
    simpa [prefixWord, tailWord_6566779, baseEnd_6566779] using wordTrace_append hprefix tailTrace_6566779
  have hstable : (prefixWord ++ tailWord_6566779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566779).length < 2 ^ (prefixWord ++ tailWord_6566779).sum := by decide
  have hdescent : baseEnd_6566779 < baseStart_6566779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566803 : List Nat := [1, 1, 1, 2, 1, 2, 1, 9, 1, 2, 2]
def baseStart_6566803 : Nat := 118140960795 + 6566803 * 2 ^ 59
def prefixEnd_6566803 : Nat := 4983230072969 + 3 ^ 40 * 6566803 * 2
def baseEnd_6566803 : Nat := 3371926302386976086762329

theorem tailTrace_6566803 : CollatzResearch.WordTrace tailWord_6566803 prefixEnd_6566803 3371926302386976086762329 := by
  unfold tailWord_6566803
  simp only [CollatzResearch.WordTrace]
  refine ⟨239510982028601726508689063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159673988019067817672459375 239510982028601726508689063)
  ·
    refine ⟨359266473042902589763033595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239510982028601726508689063 359266473042902589763033595)
    ·
      refine ⟨538899709564353884644550393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359266473042902589763033595 538899709564353884644550393)
      ·
        refine ⟨404174782173265413483412795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 538899709564353884644550393 404174782173265413483412795)
        ·
          refine ⟨606262173259898120225119193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404174782173265413483412795 606262173259898120225119193)
          ·
            refine ⟨454696629944923590168839395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606262173259898120225119193 454696629944923590168839395)
            ·
              refine ⟨682044944917385385253259093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454696629944923590168839395 682044944917385385253259093)
              ·
                refine ⟨3996357099125304991718315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 682044944917385385253259093 3996357099125304991718315)
                ·
                  refine ⟨5994535648687957487577473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996357099125304991718315 5994535648687957487577473)
                  ·
                    refine ⟨4495901736515968115683105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994535648687957487577473 4495901736515968115683105)
                    ·
                      refine ⟨3371926302386976086762329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495901736515968115683105 3371926302386976086762329)
                      ·
                        rfl

theorem cell23_6566803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 9, 1, 2, 2].length) (baseStart_6566803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566803 prefixEnd_6566803 := by exact prefixLift 6566803
  have htrace : WordTrace (prefixWord ++ tailWord_6566803) baseStart_6566803 baseEnd_6566803 := by
    simpa [prefixWord, tailWord_6566803, baseEnd_6566803] using wordTrace_append hprefix tailTrace_6566803
  have hstable : (prefixWord ++ tailWord_6566803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566803).length < 2 ^ (prefixWord ++ tailWord_6566803).sum := by decide
  have hdescent : baseEnd_6566803 < baseStart_6566803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566870 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3]
def baseStart_6566870 : Nat := 118140960795 + 6566870 * 2 ^ 59
def prefixEnd_6566870 : Nat := 4983230072969 + 3 ^ 40 * 6566870 * 2
def baseEnd_6566870 : Nat := 3371960705590827324624521

theorem tailTrace_6566870 : CollatzResearch.WordTrace tailWord_6566870 prefixEnd_6566870 3371960705590827324624521 := by
  unfold tailWord_6566870
  simp only [CollatzResearch.WordTrace]
  refine ⟨14969589107459937309461129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 159675617146239331300918709 14969589107459937309461129)
  ·
    refine ⟨11227191830594952982095847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14969589107459937309461129 11227191830594952982095847)
    ·
      refine ⟨16840787745892429473143771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11227191830594952982095847 16840787745892429473143771)
      ·
        refine ⟨25261181618838644209715657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16840787745892429473143771 25261181618838644209715657)
        ·
          refine ⟨18945886214128983157286743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25261181618838644209715657 18945886214128983157286743)
          ·
            refine ⟨28418829321193474735930115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18945886214128983157286743 28418829321193474735930115)
            ·
              refine ⟨42628243981790212103895173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28418829321193474735930115 42628243981790212103895173)
              ·
                refine ⟨7992795746585664769480345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42628243981790212103895173 7992795746585664769480345)
                ·
                  refine ⟨5994596809939248577110259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992795746585664769480345 5994596809939248577110259)
                  ·
                    refine ⟨8991895214908872865665389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5994596809939248577110259 8991895214908872865665389)
                    ·
                      refine ⟨3371960705590827324624521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991895214908872865665389 3371960705590827324624521)
                      ·
                        rfl

theorem cell23_6566870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_6566870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566870 prefixEnd_6566870 := by exact prefixLift 6566870
  have htrace : WordTrace (prefixWord ++ tailWord_6566870) baseStart_6566870 baseEnd_6566870 := by
    simpa [prefixWord, tailWord_6566870, baseEnd_6566870] using wordTrace_append hprefix tailTrace_6566870
  have hstable : (prefixWord ++ tailWord_6566870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566870).length < 2 ^ (prefixWord ++ tailWord_6566870).sum := by decide
  have hdescent : baseEnd_6566870 < baseStart_6566870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566909 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 3]
def baseStart_6566909 : Nat := 118140960795 + 6566909 * 2 ^ 59
def prefixEnd_6566909 : Nat := 4983230072969 + 3 ^ 40 * 6566909 * 2
def baseEnd_6566909 : Nat := 3371980731336352672036841

theorem tailTrace_6566909 : CollatzResearch.WordTrace tailWord_6566909 prefixEnd_6566909 3371980731336352672036841 := by
  unfold tailWord_6566909
  simp only [CollatzResearch.WordTrace]
  refine ⟨239514848166217706612047781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159676565444145137741365187 239514848166217706612047781)
  ·
    refine ⟨44909034031165819989758959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239514848166217706612047781 44909034031165819989758959)
    ·
      refine ⟨67363551046748729984638439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44909034031165819989758959 67363551046748729984638439)
      ·
        refine ⟨101045326570123094976957659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67363551046748729984638439 101045326570123094976957659)
        ·
          refine ⟨151567989855184642465436489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101045326570123094976957659 151567989855184642465436489)
          ·
            refine ⟨113675992391388481849077367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151567989855184642465436489 113675992391388481849077367)
            ·
              refine ⟨170513988587082722773616051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113675992391388481849077367 170513988587082722773616051)
              ·
                refine ⟨255770982880624084160424077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170513988587082722773616051 255770982880624084160424077)
                ·
                  refine ⟨95914118580234031560159029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 255770982880624084160424077 95914118580234031560159029)
                  ·
                    refine ⟨8991948616896940458764909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95914118580234031560159029 8991948616896940458764909)
                    ·
                      refine ⟨3371980731336352672036841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991948616896940458764909 3371980731336352672036841)
                      ·
                        rfl

theorem cell23_6566909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_6566909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566909 prefixEnd_6566909 := by exact prefixLift 6566909
  have htrace : WordTrace (prefixWord ++ tailWord_6566909) baseStart_6566909 baseEnd_6566909 := by
    simpa [prefixWord, tailWord_6566909, baseEnd_6566909] using wordTrace_append hprefix tailTrace_6566909
  have hstable : (prefixWord ++ tailWord_6566909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566909).length < 2 ^ (prefixWord ++ tailWord_6566909).sum := by decide
  have hdescent : baseEnd_6566909 < baseStart_6566909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566926 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_6566926 : Nat := 118140960795 + 6566926 * 2 ^ 59
def prefixEnd_6566926 : Nat := 4983230072969 + 3 ^ 40 * 6566926 * 2
def baseEnd_6566926 : Nat := 3371989460507479105524263

theorem tailTrace_6566926 : CollatzResearch.WordTrace tailWord_6566926 prefixEnd_6566926 3371989460507479105524263 := by
  unfold tailWord_6566926
  simp only [CollatzResearch.WordTrace]
  refine ⟨29939433525894514814427079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159676978804770745676944421 29939433525894514814427079)
  ·
    refine ⟨44909150288841772221640619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29939433525894514814427079 44909150288841772221640619)
    ·
      refine ⟨67363725433262658332460929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44909150288841772221640619 67363725433262658332460929)
      ·
        refine ⟨50522794074946993749345697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67363725433262658332460929 50522794074946993749345697)
        ·
          refine ⟨37892095556210245312009273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50522794074946993749345697 37892095556210245312009273)
          ·
            refine ⟨28419071667157683984006955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37892095556210245312009273 28419071667157683984006955)
            ·
              refine ⟨42628607500736525976010433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28419071667157683984006955 42628607500736525976010433)
              ·
                refine ⟨31971455625552394482007825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42628607500736525976010433 31971455625552394482007825)
                ·
                  refine ⟨23978591719164295861505869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31971455625552394482007825 23978591719164295861505869)
                  ·
                    refine ⟨8991971894686610948064701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23978591719164295861505869 8991971894686610948064701)
                    ·
                      refine ⟨3371989460507479105524263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8991971894686610948064701 3371989460507479105524263)
                      ·
                        rfl

theorem cell23_6566926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_6566926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566926 prefixEnd_6566926 := by exact prefixLift 6566926
  have htrace : WordTrace (prefixWord ++ tailWord_6566926) baseStart_6566926 baseEnd_6566926 := by
    simpa [prefixWord, tailWord_6566926, baseEnd_6566926] using wordTrace_append hprefix tailTrace_6566926
  have hstable : (prefixWord ++ tailWord_6566926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566926).length < 2 ^ (prefixWord ++ tailWord_6566926).sum := by decide
  have hdescent : baseEnd_6566926 < baseStart_6566926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566929 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 2, 5]
def baseStart_6566929 : Nat := 118140960795 + 6566929 * 2 ^ 59
def prefixEnd_6566929 : Nat := 4983230072969 + 3 ^ 40 * 6566929 * 2
def baseEnd_6566929 : Nat := 1123997000316480864595583

theorem tailTrace_6566929 : CollatzResearch.WordTrace tailWord_6566929 prefixEnd_6566929 1123997000316480864595583 := by
  unfold tailWord_6566929
  simp only [CollatzResearch.WordTrace]
  refine ⟨239515577626145250027775841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159677051750763500018517227 239515577626145250027775841)
  ·
    refine ⟨179636683219608937520831881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239515577626145250027775841 179636683219608937520831881)
    ·
      refine ⟨134727512414706703140623911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179636683219608937520831881 134727512414706703140623911)
      ·
        refine ⟨202091268622060054710935867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134727512414706703140623911 202091268622060054710935867)
        ·
          refine ⟨303136902933090082066403801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202091268622060054710935867 303136902933090082066403801)
          ·
            refine ⟨227352677199817561549802851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303136902933090082066403801 227352677199817561549802851)
            ·
              refine ⟨341029015799726342324704277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 227352677199817561549802851 341029015799726342324704277)
              ·
                refine ⟨15985735115612172296470513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 341029015799726342324704277 15985735115612172296470513)
                ·
                  refine ⟨11989301336709129222352885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15985735115612172296470513 11989301336709129222352885)
                  ·
                    refine ⟨1123997000316480864595583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11989301336709129222352885 1123997000316480864595583)
                    ·
                      rfl

theorem cell23_6566929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_6566929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566929 prefixEnd_6566929 := by exact prefixLift 6566929
  have htrace : WordTrace (prefixWord ++ tailWord_6566929) baseStart_6566929 baseEnd_6566929 := by
    simpa [prefixWord, tailWord_6566929, baseEnd_6566929] using wordTrace_append hprefix tailTrace_6566929
  have hstable : (prefixWord ++ tailWord_6566929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566929).length < 2 ^ (prefixWord ++ tailWord_6566929).sum := by decide
  have hdescent : baseEnd_6566929 < baseStart_6566929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566944 : List Nat := [2, 1, 1, 7, 1, 1, 3, 1, 2, 2, 2]
def baseStart_6566944 : Nat := 118140960795 + 6566944 * 2 ^ 59
def prefixEnd_6566944 : Nat := 4983230072969 + 3 ^ 40 * 6566944 * 2
def baseEnd_6566944 : Nat := 3371998703159260035099181

theorem tailTrace_6566944 : CollatzResearch.WordTrace tailWord_6566944 prefixEnd_6566944 3371998703159260035099181 := by
  unfold tailWord_6566944
  simp only [CollatzResearch.WordTrace]
  refine ⟨119758062360545453794785943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159677416480727271726381257 119758062360545453794785943)
  ·
    refine ⟨179637093540818180692178915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119758062360545453794785943 179637093540818180692178915)
    ·
      refine ⟨269455640311227271038268373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179637093540818180692178915 269455640311227271038268373)
      ·
        refine ⟨6315366569794389164959415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 269455640311227271038268373 6315366569794389164959415)
        ·
          refine ⟨9473049854691583747439123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315366569794389164959415 9473049854691583747439123)
          ·
            refine ⟨14209574782037375621158685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9473049854691583747439123 14209574782037375621158685)
            ·
              refine ⟨5328590543264015857934507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14209574782037375621158685 5328590543264015857934507)
              ·
                refine ⟨7992885814896023786901761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328590543264015857934507 7992885814896023786901761)
                ·
                  refine ⟨5994664361172017840176321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7992885814896023786901761 5994664361172017840176321)
                  ·
                    refine ⟨4495998270879013380132241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994664361172017840176321 4495998270879013380132241)
                    ·
                      refine ⟨3371998703159260035099181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4495998270879013380132241 3371998703159260035099181)
                      ·
                        rfl

theorem cell23_6566944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_6566944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566944 prefixEnd_6566944 := by exact prefixLift 6566944
  have htrace : WordTrace (prefixWord ++ tailWord_6566944) baseStart_6566944 baseEnd_6566944 := by
    simpa [prefixWord, tailWord_6566944, baseEnd_6566944] using wordTrace_append hprefix tailTrace_6566944
  have hstable : (prefixWord ++ tailWord_6566944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566944).length < 2 ^ (prefixWord ++ tailWord_6566944).sum := by decide
  have hdescent : baseEnd_6566944 < baseStart_6566944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566949 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 4]
def baseStart_6566949 : Nat := 118140960795 + 6566949 * 2 ^ 59
def prefixEnd_6566949 : Nat := 4983230072969 + 3 ^ 40 * 6566949 * 2
def baseEnd_6566949 : Nat := 3372001270562532515536657

theorem tailTrace_6566949 : CollatzResearch.WordTrace tailWord_6566949 prefixEnd_6566949 3372001270562532515536657 := by
  unfold tailWord_6566949
  simp only [CollatzResearch.WordTrace]
  refine ⟨239516307086072793443503901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159677538057381862295669267 239516307086072793443503901)
  ·
    refine ⟨89818615157277297541313963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239516307086072793443503901 89818615157277297541313963)
    ·
      refine ⟨134727922735915946311970945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89818615157277297541313963 134727922735915946311970945)
      ·
        refine ⟨101045942051936959733978209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134727922735915946311970945 101045942051936959733978209)
        ·
          refine ⟨75784456538952719800483657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101045942051936959733978209 75784456538952719800483657)
          ·
            refine ⟨56838342404214539850362743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75784456538952719800483657 56838342404214539850362743)
            ·
              refine ⟨85257513606321809775544115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56838342404214539850362743 85257513606321809775544115)
              ·
                refine ⟨127886270409482714663316173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85257513606321809775544115 127886270409482714663316173)
                ·
                  refine ⟨47957351403556017998743565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127886270409482714663316173 47957351403556017998743565)
                  ·
                    refine ⟨17984006776333506749528837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47957351403556017998743565 17984006776333506749528837)
                    ·
                      refine ⟨3372001270562532515536657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17984006776333506749528837 3372001270562532515536657)
                      ·
                        rfl

theorem cell23_6566949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_6566949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566949 prefixEnd_6566949 := by exact prefixLift 6566949
  have htrace : WordTrace (prefixWord ++ tailWord_6566949) baseStart_6566949 baseEnd_6566949 := by
    simpa [prefixWord, tailWord_6566949, baseEnd_6566949] using wordTrace_append hprefix tailTrace_6566949
  have hstable : (prefixWord ++ tailWord_6566949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566949).length < 2 ^ (prefixWord ++ tailWord_6566949).sum := by decide
  have hdescent : baseEnd_6566949 < baseStart_6566949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566986 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3]
def baseStart_6566986 : Nat := 118140960795 + 6566986 * 2 ^ 59
def prefixEnd_6566986 : Nat := 4983230072969 + 3 ^ 40 * 6566986 * 2
def baseEnd_6566986 : Nat := 3372020269346748870773987

theorem tailTrace_6566986 : CollatzResearch.WordTrace tailWord_6566986 prefixEnd_6566986 3372020269346748870773987 := by
  unfold tailWord_6566986
  simp only [CollatzResearch.WordTrace]
  refine ⟨59879414146734687190650203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159678437724625832508400541 59879414146734687190650203)
  ·
    refine ⟨89819121220102030785975305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59879414146734687190650203 89819121220102030785975305)
    ·
      refine ⟨67364340915076523089481479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89819121220102030785975305 67364340915076523089481479)
      ·
        refine ⟨101046511372614784634222219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67364340915076523089481479 101046511372614784634222219)
        ·
          refine ⟨151569767058922176951333329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101046511372614784634222219 151569767058922176951333329)
          ·
            refine ⟨113677325294191632713499997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151569767058922176951333329 113677325294191632713499997)
            ·
              refine ⟨42628996985321862267562499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113677325294191632713499997 42628996985321862267562499)
              ·
                refine ⟨63943495477982793401343749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42628996985321862267562499 63943495477982793401343749)
                ·
                  refine ⟨11989405402121773762751953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63943495477982793401343749 11989405402121773762751953)
                  ·
                    refine ⟨8992054051591330322063965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11989405402121773762751953 8992054051591330322063965)
                    ·
                      refine ⟨3372020269346748870773987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8992054051591330322063965 3372020269346748870773987)
                      ·
                        rfl

theorem cell23_6566986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_6566986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566986 prefixEnd_6566986 := by exact prefixLift 6566986
  have htrace : WordTrace (prefixWord ++ tailWord_6566986) baseStart_6566986 baseEnd_6566986 := by
    simpa [prefixWord, tailWord_6566986, baseEnd_6566986] using wordTrace_append hprefix tailTrace_6566986
  have hstable : (prefixWord ++ tailWord_6566986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566986).length < 2 ^ (prefixWord ++ tailWord_6566986).sum := by decide
  have hdescent : baseEnd_6566986 < baseStart_6566986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6566993 : List Nat := [1, 2, 2, 1, 3, 1, 2, 6, 1, 4]
def baseStart_6566993 : Nat := 118140960795 + 6566993 * 2 ^ 59
def prefixEnd_6566993 : Nat := 4983230072969 + 3 ^ 40 * 6566993 * 2
def baseEnd_6566993 : Nat := 1124007954570443447795485

theorem tailTrace_6566993 : CollatzResearch.WordTrace tailWord_6566993 prefixEnd_6566993 1124007954570443447795485 := by
  unfold tailWord_6566993
  simp only [CollatzResearch.WordTrace]
  refine ⟨239517911897913388958105633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159678607931942259305403755 239517911897913388958105633)
  ·
    refine ⟨179638433923435041718579225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239517911897913388958105633 179638433923435041718579225)
    ·
      refine ⟨134728825442576281288934419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179638433923435041718579225 134728825442576281288934419)
      ·
        refine ⟨202093238163864421933401629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134728825442576281288934419 202093238163864421933401629)
        ·
          refine ⟨75784964311449158225025611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202093238163864421933401629 75784964311449158225025611)
          ·
            refine ⟨113677446467173737337538417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75784964311449158225025611 113677446467173737337538417)
            ·
              refine ⟨85258084850380303003153813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113677446467173737337538417 85258084850380303003153813)
              ·
                refine ⟨3996472727361576703272835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85258084850380303003153813 3996472727361576703272835)
                ·
                  refine ⟨5994709091042365054909253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996472727361576703272835 5994709091042365054909253)
                  ·
                    refine ⟨1124007954570443447795485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994709091042365054909253 1124007954570443447795485)
                    ·
                      rfl

theorem cell23_6566993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 6, 1, 4].length) (baseStart_6566993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6566993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6566993 prefixEnd_6566993 := by exact prefixLift 6566993
  have htrace : WordTrace (prefixWord ++ tailWord_6566993) baseStart_6566993 baseEnd_6566993 := by
    simpa [prefixWord, tailWord_6566993, baseEnd_6566993] using wordTrace_append hprefix tailTrace_6566993
  have hstable : (prefixWord ++ tailWord_6566993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6566993).length < 2 ^ (prefixWord ++ tailWord_6566993).sum := by decide
  have hdescent : baseEnd_6566993 < baseStart_6566993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6566993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567009 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_6567009 : Nat := 118140960795 + 6567009 * 2 ^ 59
def prefixEnd_6567009 : Nat := 4983230072969 + 3 ^ 40 * 6567009 * 2
def baseEnd_6567009 : Nat := 3372032079401802280786381

theorem tailTrace_6567009 : CollatzResearch.WordTrace tailWord_6567009 prefixEnd_6567009 3372032079401802280786381 := by
  unfold tailWord_6567009
  simp only [CollatzResearch.WordTrace]
  refine ⟨239518495465855423690688081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159678996977236949127125387 239518495465855423690688081)
  ·
    refine ⟨179638871599391567768016061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239518495465855423690688081 179638871599391567768016061)
    ·
      refine ⟨67364576849771837913006023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179638871599391567768016061 67364576849771837913006023)
      ·
        refine ⟨101046865274657756869509035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67364576849771837913006023 101046865274657756869509035)
        ·
          refine ⟨151570297911986635304263553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101046865274657756869509035 151570297911986635304263553)
          ·
            refine ⟨113677723433989976478197665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151570297911986635304263553 113677723433989976478197665)
            ·
              refine ⟨85258292575492482358648249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113677723433989976478197665 85258292575492482358648249)
              ·
                refine ⟨63943719431619361768986187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85258292575492482358648249 63943719431619361768986187)
                ·
                  refine ⟨95915579147429042653479281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63943719431619361768986187 95915579147429042653479281)
                  ·
                    refine ⟨71936684360571781990109461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95915579147429042653479281 71936684360571781990109461)
                    ·
                      refine ⟨3372032079401802280786381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71936684360571781990109461 3372032079401802280786381)
                      ·
                        rfl

theorem cell23_6567009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_6567009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567009 prefixEnd_6567009 := by exact prefixLift 6567009
  have htrace : WordTrace (prefixWord ++ tailWord_6567009) baseStart_6567009 baseEnd_6567009 := by
    simpa [prefixWord, tailWord_6567009, baseEnd_6567009] using wordTrace_append hprefix tailTrace_6567009
  have hstable : (prefixWord ++ tailWord_6567009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567009).length < 2 ^ (prefixWord ++ tailWord_6567009).sum := by decide
  have hdescent : baseEnd_6567009 < baseStart_6567009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567043 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 2, 3, 2]
def baseStart_6567043 : Nat := 118140960795 + 6567043 * 2 ^ 59
def prefixEnd_6567043 : Nat := 4983230072969 + 3 ^ 40 * 6567043 * 2
def baseEnd_6567043 : Nat := 3372049537744055147761225

theorem tailTrace_6567043 : CollatzResearch.WordTrace tailWord_6567043 prefixEnd_6567043 3372049537744055147761225 := by
  unfold tailWord_6567043
  simp only [CollatzResearch.WordTrace]
  refine ⟨239519735547732247497425783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159679823698488164998283855 239519735547732247497425783)
  ·
    refine ⟨359279603321598371246138675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239519735547732247497425783 359279603321598371246138675)
    ·
      refine ⟨538919404982397556869208013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359279603321598371246138675 538919404982397556869208013)
      ·
        refine ⟨202094776868399083825953005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538919404982397556869208013 202094776868399083825953005)
        ·
          refine ⟨75785541325649656434732377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202094776868399083825953005 75785541325649656434732377)
          ·
            refine ⟨56839155994237242326049283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75785541325649656434732377 56839155994237242326049283)
            ·
              refine ⟨85258733991355863489073925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56839155994237242326049283 85258733991355863489073925)
              ·
                refine ⟨15986012623379224404201361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85258733991355863489073925 15986012623379224404201361)
                ·
                  refine ⟨11989509467534418303151021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15986012623379224404201361 11989509467534418303151021)
                  ·
                    refine ⟨4496066050325406863681633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11989509467534418303151021 4496066050325406863681633)
                    ·
                      refine ⟨3372049537744055147761225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496066050325406863681633 3372049537744055147761225)
                      ·
                        rfl

theorem cell23_6567043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_6567043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567043 prefixEnd_6567043 := by exact prefixLift 6567043
  have htrace : WordTrace (prefixWord ++ tailWord_6567043) baseStart_6567043 baseEnd_6567043 := by
    simpa [prefixWord, tailWord_6567043, baseEnd_6567043] using wordTrace_append hprefix tailTrace_6567043
  have hstable : (prefixWord ++ tailWord_6567043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567043).length < 2 ^ (prefixWord ++ tailWord_6567043).sum := by decide
  have hdescent : baseEnd_6567043 < baseStart_6567043 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567073 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 4]
def baseStart_6567073 : Nat := 118140960795 + 6567073 * 2 ^ 59
def prefixEnd_6567073 : Nat := 4983230072969 + 3 ^ 40 * 6567073 * 2
def baseEnd_6567073 : Nat := 3372064942163690030386087

theorem tailTrace_6567073 : CollatzResearch.WordTrace tailWord_6567073 prefixEnd_6567073 3372064942163690030386087 := by
  unfold tailWord_6567073
  simp only [CollatzResearch.WordTrace]
  refine ⟨239520829737623562621017873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159680553158415708414011915 239520829737623562621017873)
  ·
    refine ⟨179640622303217671965763405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239520829737623562621017873 179640622303217671965763405)
    ·
      refine ⟨67365233363706626987161277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 179640622303217671965763405 67365233363706626987161277)
      ·
        refine ⟨25261962511389985120185479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67365233363706626987161277 25261962511389985120185479)
        ·
          refine ⟨37892943767084977680278219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25261962511389985120185479 37892943767084977680278219)
          ·
            refine ⟨56839415650627466520417329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37892943767084977680278219 56839415650627466520417329)
            ·
              refine ⟨42629561737970599890312997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56839415650627466520417329 42629561737970599890312997)
              ·
                refine ⟨7993042825869487479433687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42629561737970599890312997 7993042825869487479433687)
                ·
                  refine ⟨11989564238804231219150531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993042825869487479433687 11989564238804231219150531)
                  ·
                    refine ⟨17984346358206346828725797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11989564238804231219150531 17984346358206346828725797)
                    ·
                      refine ⟨3372064942163690030386087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17984346358206346828725797 3372064942163690030386087)
                      ·
                        rfl

theorem cell23_6567073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_6567073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567073 prefixEnd_6567073 := by exact prefixLift 6567073
  have htrace : WordTrace (prefixWord ++ tailWord_6567073) baseStart_6567073 baseEnd_6567073 := by
    simpa [prefixWord, tailWord_6567073, baseEnd_6567073] using wordTrace_append hprefix tailTrace_6567073
  have hstable : (prefixWord ++ tailWord_6567073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567073).length < 2 ^ (prefixWord ++ tailWord_6567073).sum := by decide
  have hdescent : baseEnd_6567073 < baseStart_6567073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567090 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4]
def baseStart_6567090 : Nat := 118140960795 + 6567090 * 2 ^ 59
def prefixEnd_6567090 : Nat := 4983230072969 + 3 ^ 40 * 6567090 * 2
def baseEnd_6567090 : Nat := 3372073671334816463873509

theorem tailTrace_6567090 : CollatzResearch.WordTrace tailWord_6567090 prefixEnd_6567090 3372073671334816463873509 := by
  unfold tailWord_6567090
  simp only [CollatzResearch.WordTrace]
  refine ⟨59880362444640493631096681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159680966519041316349591149 59880362444640493631096681)
  ·
    refine ⟨44910271833480370223322511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59880362444640493631096681 44910271833480370223322511)
    ·
      refine ⟨67365407750220555334983767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44910271833480370223322511 67365407750220555334983767)
      ·
        refine ⟨101048111625330833002475651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67365407750220555334983767 101048111625330833002475651)
        ·
          refine ⟨151572167437996249503713477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101048111625330833002475651 151572167437996249503713477)
          ·
            refine ⟨28419781394624296781946277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151572167437996249503713477 28419781394624296781946277)
            ·
              refine ⟨5328709011492055646614927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28419781394624296781946277 5328709011492055646614927)
              ·
                refine ⟨7993063517238083469922391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328709011492055646614927 7993063517238083469922391)
                ·
                  refine ⟨11989595275857125204883587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993063517238083469922391 11989595275857125204883587)
                  ·
                    refine ⟨17984392913785687807325381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11989595275857125204883587 17984392913785687807325381)
                    ·
                      refine ⟨3372073671334816463873509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17984392913785687807325381 3372073671334816463873509)
                      ·
                        rfl

theorem cell23_6567090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 1, 4].length) (baseStart_6567090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567090 prefixEnd_6567090 := by exact prefixLift 6567090
  have htrace : WordTrace (prefixWord ++ tailWord_6567090) baseStart_6567090 baseEnd_6567090 := by
    simpa [prefixWord, tailWord_6567090, baseEnd_6567090] using wordTrace_append hprefix tailTrace_6567090
  have hstable : (prefixWord ++ tailWord_6567090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567090).length < 2 ^ (prefixWord ++ tailWord_6567090).sum := by decide
  have hdescent : baseEnd_6567090 < baseStart_6567090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567100 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_6567100 : Nat := 118140960795 + 6567100 * 2 ^ 59
def prefixEnd_6567100 : Nat := 4983230072969 + 3 ^ 40 * 6567100 * 2
def baseEnd_6567100 : Nat := 1124026268713787141582821

theorem tailTrace_6567100 : CollatzResearch.WordTrace tailWord_6567100 prefixEnd_6567100 1124026268713787141582821 := by
  unfold tailWord_6567100
  simp only [CollatzResearch.WordTrace]
  refine ⟨119760907254262873116125377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159681209672350497488167169 119760907254262873116125377)
  ·
    refine ⟨89820680440697154837094033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119760907254262873116125377 89820680440697154837094033)
    ·
      refine ⟨67365510330522866127820525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89820680440697154837094033 67365510330522866127820525)
      ·
        refine ⟨25262066373946074797932697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67365510330522866127820525 25262066373946074797932697)
        ·
          refine ⟨18946549780459556098449523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25262066373946074797932697 18946549780459556098449523)
          ·
            refine ⟨28419824670689334147674285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18946549780459556098449523 28419824670689334147674285)
            ·
              refine ⟨10657434251508500305377857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28419824670689334147674285 10657434251508500305377857)
              ·
                refine ⟨7993075688631375229033393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10657434251508500305377857 7993075688631375229033393)
                ·
                  refine ⟨5994806766473531421775045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7993075688631375229033393 5994806766473531421775045)
                  ·
                    refine ⟨1124026268713787141582821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994806766473531421775045 1124026268713787141582821)
                    ·
                      rfl

theorem cell23_6567100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_6567100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567100 prefixEnd_6567100 := by exact prefixLift 6567100
  have htrace : WordTrace (prefixWord ++ tailWord_6567100) baseStart_6567100 baseEnd_6567100 := by
    simpa [prefixWord, tailWord_6567100, baseEnd_6567100] using wordTrace_append hprefix tailTrace_6567100
  have hstable : (prefixWord ++ tailWord_6567100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567100).length < 2 ^ (prefixWord ++ tailWord_6567100).sum := by decide
  have hdescent : baseEnd_6567100 < baseStart_6567100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567136 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_6567136 : Nat := 118140960795 + 6567136 * 2 ^ 59
def prefixEnd_6567136 : Nat := 4983230072969 + 3 ^ 40 * 6567136 * 2
def baseEnd_6567136 : Nat := 3372097291444923283898297

theorem tailTrace_6567136 : CollatzResearch.WordTrace tailWord_6567136 prefixEnd_6567136 3372097291444923283898297 := by
  unfold tailWord_6567136
  simp only [CollatzResearch.WordTrace]
  refine ⟨119761563768197662190280631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159682085024263549587040841 119761563768197662190280631)
  ·
    refine ⟨179642345652296493285420947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119761563768197662190280631 179642345652296493285420947)
    ·
      refine ⟨269463518478444739928131421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179642345652296493285420947 269463518478444739928131421)
      ·
        refine ⟨101048819429416777473049283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269463518478444739928131421 101048819429416777473049283)
        ·
          refine ⟨151573229144125166209573925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101048819429416777473049283 151573229144125166209573925)
          ·
            refine ⟨28419980464523468664295111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151573229144125166209573925 28419980464523468664295111)
            ·
              refine ⟨42629970696785202996442667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28419980464523468664295111 42629970696785202996442667)
              ·
                refine ⟨63944956045177804494664001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42629970696785202996442667 63944956045177804494664001)
                ·
                  refine ⟨47958717033883353370998001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63944956045177804494664001 47958717033883353370998001)
                  ·
                    refine ⟨35969037775412515028248501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47958717033883353370998001 35969037775412515028248501)
                    ·
                      refine ⟨3372097291444923283898297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35969037775412515028248501 3372097291444923283898297)
                      ·
                        rfl

theorem cell23_6567136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_6567136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567136 prefixEnd_6567136 := by exact prefixLift 6567136
  have htrace : WordTrace (prefixWord ++ tailWord_6567136) baseStart_6567136 baseEnd_6567136 := by
    simpa [prefixWord, tailWord_6567136, baseEnd_6567136] using wordTrace_append hprefix tailTrace_6567136
  have hstable : (prefixWord ++ tailWord_6567136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567136).length < 2 ^ (prefixWord ++ tailWord_6567136).sum := by decide
  have hdescent : baseEnd_6567136 < baseStart_6567136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567141 : List Nat := [1, 3, 1, 4, 3, 2, 1, 3, 1, 2, 2]
def baseStart_6567141 : Nat := 118140960795 + 6567141 * 2 ^ 59
def prefixEnd_6567141 : Nat := 4983230072969 + 3 ^ 40 * 6567141 * 2
def baseEnd_6567141 : Nat := 3372099858848195764335775

theorem tailTrace_6567141 : CollatzResearch.WordTrace tailWord_6567141 prefixEnd_6567141 3372099858848195764335775 := by
  unfold tailWord_6567141
  simp only [CollatzResearch.WordTrace]
  refine ⟨239523309901377210234493277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159682206600918140156328851 239523309901377210234493277)
  ·
    refine ⟨89821241213016453837934979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239523309901377210234493277 89821241213016453837934979)
    ·
      refine ⟨134731861819524680756902469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89821241213016453837934979 134731861819524680756902469)
      ·
        refine ⟨25262224091160877641919213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134731861819524680756902469 25262224091160877641919213)
        ·
          refine ⟨9473334034185329115719705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25262224091160877641919213 9473334034185329115719705)
          ·
            refine ⟨7105000525638996836789779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9473334034185329115719705 7105000525638996836789779)
            ·
              refine ⟨10657500788458495255184669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7105000525638996836789779 10657500788458495255184669)
              ·
                refine ⟨3996562795671935720694251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10657500788458495255184669 3996562795671935720694251)
                ·
                  refine ⟨5994844193507903581041377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996562795671935720694251 5994844193507903581041377)
                  ·
                    refine ⟨4496133145130927685781033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5994844193507903581041377 4496133145130927685781033)
                    ·
                      refine ⟨3372099858848195764335775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496133145130927685781033 3372099858848195764335775)
                      ·
                        rfl

theorem cell23_6567141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_6567141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567141 prefixEnd_6567141 := by exact prefixLift 6567141
  have htrace : WordTrace (prefixWord ++ tailWord_6567141) baseStart_6567141 baseEnd_6567141 := by
    simpa [prefixWord, tailWord_6567141, baseEnd_6567141] using wordTrace_append hprefix tailTrace_6567141
  have hstable : (prefixWord ++ tailWord_6567141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567141).length < 2 ^ (prefixWord ++ tailWord_6567141).sum := by decide
  have hdescent : baseEnd_6567141 < baseStart_6567141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567197 : List Nat := [1, 4, 2, 3, 1, 2, 1, 2, 1, 4, 2]
def baseStart_6567197 : Nat := 118140960795 + 6567197 * 2 ^ 59
def prefixEnd_6567197 : Nat := 4983230072969 + 3 ^ 40 * 6567197 * 2
def baseEnd_6567197 : Nat := 3372128613764847545235517

theorem tailTrace_6567197 : CollatzResearch.WordTrace tailWord_6567197 prefixEnd_6567197 3372128613764847545235517 := by
  unfold tailWord_6567197
  simp only [CollatzResearch.WordTrace]
  refine ⟨239525352389174331798531845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159683568259449554532354563 239525352389174331798531845)
  ·
    refine ⟨44911003572970187212224721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 239525352389174331798531845 44911003572970187212224721)
    ·
      refine ⟨33683252679727640409168541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44911003572970187212224721 33683252679727640409168541)
      ·
        refine ⟨12631219754897865153438203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33683252679727640409168541 12631219754897865153438203)
        ·
          refine ⟨18946829632346797730157305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12631219754897865153438203 18946829632346797730157305)
          ·
            refine ⟨14210122224260098297617979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18946829632346797730157305 14210122224260098297617979)
            ·
              refine ⟨21315183336390147446426969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14210122224260098297617979 21315183336390147446426969)
              ·
                refine ⟨15986387502292610584820227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21315183336390147446426969 15986387502292610584820227)
                ·
                  refine ⟨23979581253438915877230341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15986387502292610584820227 23979581253438915877230341)
                  ·
                    refine ⟨4496171485019796726980689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23979581253438915877230341 4496171485019796726980689)
                    ·
                      refine ⟨3372128613764847545235517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496171485019796726980689 3372128613764847545235517)
                      ·
                        rfl

theorem cell23_6567197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_6567197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567197 prefixEnd_6567197 := by exact prefixLift 6567197
  have htrace : WordTrace (prefixWord ++ tailWord_6567197) baseStart_6567197 baseEnd_6567197 := by
    simpa [prefixWord, tailWord_6567197, baseEnd_6567197] using wordTrace_append hprefix tailTrace_6567197
  have hstable : (prefixWord ++ tailWord_6567197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567197).length < 2 ^ (prefixWord ++ tailWord_6567197).sum := by decide
  have hdescent : baseEnd_6567197 < baseStart_6567197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567230 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 2, 3, 3]
def baseStart_6567230 : Nat := 118140960795 + 6567230 * 2 ^ 59
def prefixEnd_6567230 : Nat := 4983230072969 + 3 ^ 40 * 6567230 * 2
def baseEnd_6567230 : Nat := 3372145558626445916122865

theorem tailTrace_6567230 : CollatzResearch.WordTrace tailWord_6567230 prefixEnd_6567230 3372145558626445916122865 := by
  unfold tailWord_6567230
  simp only [CollatzResearch.WordTrace]
  refine ⟨29940819499756847304310393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159684370665369852289655429 29940819499756847304310393)
  ·
    refine ⟨22455614624817635478232795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29940819499756847304310393 22455614624817635478232795)
    ·
      refine ⟨33683421937226453217349193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22455614624817635478232795 33683421937226453217349193)
      ·
        refine ⟨25262566452919839913011895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33683421937226453217349193 25262566452919839913011895)
        ·
          refine ⟨37893849679379759869517843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25262566452919839913011895 37893849679379759869517843)
          ·
            refine ⟨56840774519069639804276765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37893849679379759869517843 56840774519069639804276765)
            ·
              refine ⟨21315290444651114926603787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56840774519069639804276765 21315290444651114926603787)
              ·
                refine ⟨31972935666976672389905681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21315290444651114926603787 31972935666976672389905681)
                ·
                  refine ⟨23979701750232504292429261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31972935666976672389905681 23979701750232504292429261)
                  ·
                    refine ⟨8992388156337189109660973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23979701750232504292429261 8992388156337189109660973)
                    ·
                      refine ⟨3372145558626445916122865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8992388156337189109660973 3372145558626445916122865)
                      ·
                        rfl

theorem cell23_6567230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_6567230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567230 prefixEnd_6567230 := by exact prefixLift 6567230
  have htrace : WordTrace (prefixWord ++ tailWord_6567230) baseStart_6567230 baseEnd_6567230 := by
    simpa [prefixWord, tailWord_6567230, baseEnd_6567230] using wordTrace_append hprefix tailTrace_6567230
  have hstable : (prefixWord ++ tailWord_6567230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567230).length < 2 ^ (prefixWord ++ tailWord_6567230).sum := by decide
  have hdescent : baseEnd_6567230 < baseStart_6567230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567263 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 7, 4]
def baseStart_6567263 : Nat := 118140960795 + 6567263 * 2 ^ 59
def prefixEnd_6567263 : Nat := 4983230072969 + 3 ^ 40 * 6567263 * 2
def baseEnd_6567263 : Nat := 1124054167829348095670071

theorem tailTrace_6567263 : CollatzResearch.WordTrace tailWord_6567263 prefixEnd_6567263 1124054167829348095670071 := by
  unfold tailWord_6567263
  simp only [CollatzResearch.WordTrace]
  refine ⟨239527759606935225070434443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159685173071290150046956295 239527759606935225070434443)
  ·
    refine ⟨359291639410402837605651665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239527759606935225070434443 359291639410402837605651665)
    ·
      refine ⟨269468729557802128204238749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 359291639410402837605651665 269468729557802128204238749)
      ·
        refine ⟨101050773584175798076589531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269468729557802128204238749 101050773584175798076589531)
        ·
          refine ⟨151576160376263697114884297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101050773584175798076589531 151576160376263697114884297)
          ·
            refine ⟨113682120282197772836163223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151576160376263697114884297 113682120282197772836163223)
            ·
              refine ⟨170523180423296659254244835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113682120282197772836163223 170523180423296659254244835)
              ·
                refine ⟨255784770634944988881367253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170523180423296659254244835 255784770634944988881367253)
                ·
                  refine ⟨5994955561756523176907045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 255784770634944988881367253 5994955561756523176907045)
                  ·
                    refine ⟨1124054167829348095670071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994955561756523176907045 1124054167829348095670071)
                    ·
                      rfl

theorem cell23_6567263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 7, 4].length) (baseStart_6567263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567263 prefixEnd_6567263 := by exact prefixLift 6567263
  have htrace : WordTrace (prefixWord ++ tailWord_6567263) baseStart_6567263 baseEnd_6567263 := by
    simpa [prefixWord, tailWord_6567263, baseEnd_6567263] using wordTrace_append hprefix tailTrace_6567263
  have hstable : (prefixWord ++ tailWord_6567263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567263).length < 2 ^ (prefixWord ++ tailWord_6567263).sum := by decide
  have hdescent : baseEnd_6567263 < baseStart_6567263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567280 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 3, 4]
def baseStart_6567280 : Nat := 118140960795 + 6567280 * 2 ^ 59
def prefixEnd_6567280 : Nat := 4983230072969 + 3 ^ 40 * 6567280 * 2
def baseEnd_6567280 : Nat := 1124057077553056906832545

theorem tailTrace_6567280 : CollatzResearch.WordTrace tailWord_6567280 prefixEnd_6567280 1124057077553056906832545 := by
  unfold tailWord_6567280
  simp only [CollatzResearch.WordTrace]
  refine ⟨119764189823936818486901647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159685586431915757982535529 119764189823936818486901647)
  ·
    refine ⟨179646284735905227730352471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119764189823936818486901647 179646284735905227730352471)
    ·
      refine ⟨269469427103857841595528707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179646284735905227730352471 269469427103857841595528707)
      ·
        refine ⟨404204140655786762393293061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269469427103857841595528707 404204140655786762393293061)
        ·
          refine ⟨75788276372960017948742449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 404204140655786762393293061 75788276372960017948742449)
          ·
            refine ⟨56841207279720013461556837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75788276372960017948742449 56841207279720013461556837)
            ·
              refine ⟨10657726364947502524041907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56841207279720013461556837 10657726364947502524041907)
              ·
                refine ⟨15986589547421253786062861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10657726364947502524041907 15986589547421253786062861)
                ·
                  refine ⟨5994971080282970169773573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15986589547421253786062861 5994971080282970169773573)
                  ·
                    refine ⟨1124057077553056906832545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5994971080282970169773573 1124057077553056906832545)
                    ·
                      rfl

theorem cell23_6567280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 3, 4].length) (baseStart_6567280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567280 prefixEnd_6567280 := by exact prefixLift 6567280
  have htrace : WordTrace (prefixWord ++ tailWord_6567280) baseStart_6567280 baseEnd_6567280 := by
    simpa [prefixWord, tailWord_6567280, baseEnd_6567280] using wordTrace_append hprefix tailTrace_6567280
  have hstable : (prefixWord ++ tailWord_6567280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567280).length < 2 ^ (prefixWord ++ tailWord_6567280).sum := by decide
  have hdescent : baseEnd_6567280 < baseStart_6567280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567324 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6567324 : Nat := 118140960795 + 6567324 * 2 ^ 59
def prefixEnd_6567324 : Nat := 4983230072969 + 3 ^ 40 * 6567324 * 2
def baseEnd_6567324 : Nat := 3372193825807968548347433

theorem tailTrace_6567324 : CollatzResearch.WordTrace tailWord_6567324 prefixEnd_6567324 3372193825807968548347433 := by
  unfold tailWord_6567324
  simp only [CollatzResearch.WordTrace]
  refine ⟨119764992229857116244202513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159686656306476154992270017 119764992229857116244202513)
  ·
    refine ⟨89823744172392837183151885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119764992229857116244202513 89823744172392837183151885)
    ·
      refine ⟨33683904064647313943681957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89823744172392837183151885 33683904064647313943681957)
      ·
        refine ⟨6315732012121371364440367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33683904064647313943681957 6315732012121371364440367)
        ·
          refine ⟨9473598018182057046660551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6315732012121371364440367 9473598018182057046660551)
          ·
            refine ⟨14210397027273085569990827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9473598018182057046660551 14210397027273085569990827)
            ·
              refine ⟨21315595540909628354986241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14210397027273085569990827 21315595540909628354986241)
              ·
                refine ⟨15986696655682221266239681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21315595540909628354986241 15986696655682221266239681)
                ·
                  refine ⟨11990022491761665949679761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15986696655682221266239681 11990022491761665949679761)
                  ·
                    refine ⟨8992516868821249462259821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11990022491761665949679761 8992516868821249462259821)
                    ·
                      refine ⟨3372193825807968548347433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8992516868821249462259821 3372193825807968548347433)
                      ·
                        rfl

theorem cell23_6567324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6567324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567324 prefixEnd_6567324 := by exact prefixLift 6567324
  have htrace : WordTrace (prefixWord ++ tailWord_6567324) baseStart_6567324 baseEnd_6567324 := by
    simpa [prefixWord, tailWord_6567324, baseEnd_6567324] using wordTrace_append hprefix tailTrace_6567324
  have hstable : (prefixWord ++ tailWord_6567324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567324).length < 2 ^ (prefixWord ++ tailWord_6567324).sum := by decide
  have hdescent : baseEnd_6567324 < baseStart_6567324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567360 : List Nat := [2, 1, 1, 2, 3, 1, 2, 1, 2, 6, 2]
def baseStart_6567360 : Nat := 118140960795 + 6567360 * 2 ^ 59
def prefixEnd_6567360 : Nat := 4983230072969 + 3 ^ 40 * 6567360 * 2
def baseEnd_6567360 : Nat := 3372212311111530407497267

theorem tailTrace_6567360 : CollatzResearch.WordTrace tailWord_6567360 prefixEnd_6567360 3372212311111530407497267 := by
  unfold tailWord_6567360
  simp only [CollatzResearch.WordTrace]
  refine ⟨119765648743791905318357767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159687531658389207091143689 119765648743791905318357767)
  ·
    refine ⟨179648473115687857977536651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119765648743791905318357767 179648473115687857977536651)
    ·
      refine ⟨269472709673531786966304977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179648473115687857977536651 269472709673531786966304977)
      ·
        refine ⟨202104532255148840224728733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 269472709673531786966304977 202104532255148840224728733)
        ·
          refine ⟨75789199595680815084273275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 202104532255148840224728733 75789199595680815084273275)
          ·
            refine ⟨113683799393521222626409913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75789199595680815084273275 113683799393521222626409913)
            ·
              refine ⟨85262849545140916969807435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113683799393521222626409913 85262849545140916969807435)
              ·
                refine ⟨127894274317711375454711153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85262849545140916969807435 127894274317711375454711153)
                ·
                  refine ⟨95920705738283531591033365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127894274317711375454711153 95920705738283531591033365)
                  ·
                    refine ⟨4496283081482040543329689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95920705738283531591033365 4496283081482040543329689)
                    ·
                      refine ⟨3372212311111530407497267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496283081482040543329689 3372212311111530407497267)
                      ·
                        rfl

theorem cell23_6567360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 2, 6, 2].length) (baseStart_6567360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567360 prefixEnd_6567360 := by exact prefixLift 6567360
  have htrace : WordTrace (prefixWord ++ tailWord_6567360) baseStart_6567360 baseEnd_6567360 := by
    simpa [prefixWord, tailWord_6567360, baseEnd_6567360] using wordTrace_append hprefix tailTrace_6567360
  have hstable : (prefixWord ++ tailWord_6567360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567360).length < 2 ^ (prefixWord ++ tailWord_6567360).sum := by decide
  have hdescent : baseEnd_6567360 < baseStart_6567360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567363 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5]
def baseStart_6567363 : Nat := 118140960795 + 6567363 * 2 ^ 59
def prefixEnd_6567363 : Nat := 4983230072969 + 3 ^ 40 * 6567363 * 2
def baseEnd_6567363 : Nat := 3372213851553493895759753

theorem tailTrace_6567363 : CollatzResearch.WordTrace tailWord_6567363 prefixEnd_6567363 3372213851553493895759753 := by
  unfold tailWord_6567363
  simp only [CollatzResearch.WordTrace]
  refine ⟨239531406906572942149074743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159687604604381961432716495 239531406906572942149074743)
  ·
    refine ⟨359297110359859413223612115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239531406906572942149074743 359297110359859413223612115)
    ·
      refine ⟨538945665539789119835418173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 359297110359859413223612115 538945665539789119835418173)
      ·
        refine ⟨202104624577420919938281815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 538945665539789119835418173 202104624577420919938281815)
        ·
          refine ⟨303156936866131379907422723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202104624577420919938281815 303156936866131379907422723)
          ·
            refine ⟨454735405299197069861134085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303156936866131379907422723 454735405299197069861134085)
            ·
              refine ⟨85262888493599450598962641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 454735405299197069861134085 85262888493599450598962641)
              ·
                refine ⟨63947166370199587949221981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85262888493599450598962641 63947166370199587949221981)
                ·
                  refine ⟨23980187388824845480958243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63947166370199587949221981 23980187388824845480958243)
                  ·
                    refine ⟨35970281083237268221437365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23980187388824845480958243 35970281083237268221437365)
                    ·
                      refine ⟨3372213851553493895759753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35970281083237268221437365 3372213851553493895759753)
                      ·
                        rfl

theorem cell23_6567363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_6567363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567363 prefixEnd_6567363 := by exact prefixLift 6567363
  have htrace : WordTrace (prefixWord ++ tailWord_6567363) baseStart_6567363 baseEnd_6567363 := by
    simpa [prefixWord, tailWord_6567363, baseEnd_6567363] using wordTrace_append hprefix tailTrace_6567363
  have hstable : (prefixWord ++ tailWord_6567363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567363).length < 2 ^ (prefixWord ++ tailWord_6567363).sum := by decide
  have hdescent : baseEnd_6567363 < baseStart_6567363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567364 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_6567364 : Nat := 118140960795 + 6567364 * 2 ^ 59
def prefixEnd_6567364 : Nat := 4983230072969 + 3 ^ 40 * 6567364 * 2
def baseEnd_6567364 : Nat := 3372214365034148391847249

theorem tailTrace_6567364 : CollatzResearch.WordTrace tailWord_6567364 prefixEnd_6567364 3372214365034148391847249 := by
  unfold tailWord_6567364
  simp only [CollatzResearch.WordTrace]
  refine ⟨119765721689784659659930573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159687628919712879546574097 119765721689784659659930573)
  ·
    refine ⟨44912145633669247372473965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119765721689784659659930573 44912145633669247372473965)
    ·
      refine ⟨16842054612625967764677737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44912145633669247372473965 16842054612625967764677737)
      ·
        refine ⟨12631540959469475823508303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16842054612625967764677737 12631540959469475823508303)
        ·
          refine ⟨18947311439204213735262455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12631540959469475823508303 18947311439204213735262455)
          ·
            refine ⟨28420967158806320602893683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18947311439204213735262455 28420967158806320602893683)
            ·
              refine ⟨42631450738209480904340525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28420967158806320602893683 42631450738209480904340525)
              ·
                refine ⟨15986794026828555339127697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42631450738209480904340525 15986794026828555339127697)
                ·
                  refine ⟨11990095520121416504345773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15986794026828555339127697 11990095520121416504345773)
                  ·
                    refine ⟨4496285820045531189129665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11990095520121416504345773 4496285820045531189129665)
                    ·
                      refine ⟨3372214365034148391847249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4496285820045531189129665 3372214365034148391847249)
                      ·
                        rfl

theorem cell23_6567364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_6567364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567364 prefixEnd_6567364 := by exact prefixLift 6567364
  have htrace : WordTrace (prefixWord ++ tailWord_6567364) baseStart_6567364 baseEnd_6567364 := by
    simpa [prefixWord, tailWord_6567364, baseEnd_6567364] using wordTrace_append hprefix tailTrace_6567364
  have hstable : (prefixWord ++ tailWord_6567364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567364).length < 2 ^ (prefixWord ++ tailWord_6567364).sum := by decide
  have hdescent : baseEnd_6567364 < baseStart_6567364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567370 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 1, 6]
def baseStart_6567370 : Nat := 118140960795 + 6567370 * 2 ^ 59
def prefixEnd_6567370 : Nat := 4983230072969 + 3 ^ 40 * 6567370 * 2
def baseEnd_6567370 : Nat := 1124072481972691789457407

theorem tailTrace_6567370 : CollatzResearch.WordTrace tailWord_6567370 prefixEnd_6567370 1124072481972691789457407 := by
  unfold tailWord_6567370
  simp only [CollatzResearch.WordTrace]
  refine ⟨59882915554386895586144891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159687774811698388229719709 59882915554386895586144891)
  ·
    refine ⟨89824373331580343379217337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59882915554386895586144891 89824373331580343379217337)
    ·
      refine ⟨67368279998685257534413003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89824373331580343379217337 67368279998685257534413003)
      ·
        refine ⟨101052419998027886301619505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67368279998685257534413003 101052419998027886301619505)
        ·
          refine ⟨75789314998520914726214629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101052419998027886301619505 75789314998520914726214629)
          ·
            refine ⟨14210496562222671511165243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75789314998520914726214629 14210496562222671511165243)
            ·
              refine ⟨21315744843334007266747865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14210496562222671511165243 21315744843334007266747865)
              ·
                refine ⟨15986808632500505450060899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21315744843334007266747865 15986808632500505450060899)
                ·
                  refine ⟨23980212948750758175091349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15986808632500505450060899 23980212948750758175091349)
                  ·
                    refine ⟨1124072481972691789457407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23980212948750758175091349 1124072481972691789457407)
                    ·
                      rfl

theorem cell23_6567370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_6567370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567370 prefixEnd_6567370 := by exact prefixLift 6567370
  have htrace : WordTrace (prefixWord ++ tailWord_6567370) baseStart_6567370 baseEnd_6567370 := by
    simpa [prefixWord, tailWord_6567370, baseEnd_6567370] using wordTrace_append hprefix tailTrace_6567370
  have hstable : (prefixWord ++ tailWord_6567370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567370).length < 2 ^ (prefixWord ++ tailWord_6567370).sum := by decide
  have hdescent : baseEnd_6567370 < baseStart_6567370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567397 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 3]
def baseStart_6567397 : Nat := 118140960795 + 6567397 * 2 ^ 59
def prefixEnd_6567397 : Nat := 4983230072969 + 3 ^ 40 * 6567397 * 2
def baseEnd_6567397 : Nat := 3372231309895746762734597

theorem tailTrace_6567397 : CollatzResearch.WordTrace tailWord_6567397 prefixEnd_6567397 3372231309895746762734597 := by
  unfold tailWord_6567397
  simp only [CollatzResearch.WordTrace]
  refine ⟨239532646988449765955812445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159688431325633177303874963 239532646988449765955812445)
  ·
    refine ⟨89824742620668662233429667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239532646988449765955812445 89824742620668662233429667)
    ·
      refine ⟨134737113931002993350144501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89824742620668662233429667 134737113931002993350144501)
      ·
        refine ⟨12631604431031530626576047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134737113931002993350144501 12631604431031530626576047)
        ·
          refine ⟨18947406646547295939864071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12631604431031530626576047 18947406646547295939864071)
          ·
            refine ⟨28421109969820943909796107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18947406646547295939864071 28421109969820943909796107)
            ·
              refine ⟨42631664954731415864694161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28421109969820943909796107 42631664954731415864694161)
              ·
                refine ⟨31973748716048561898520621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42631664954731415864694161 31973748716048561898520621)
                ·
                  refine ⟨11990155768518210711945233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31973748716048561898520621 11990155768518210711945233)
                  ·
                    refine ⟨8992616826388658033958925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11990155768518210711945233 8992616826388658033958925)
                    ·
                      refine ⟨3372231309895746762734597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8992616826388658033958925 3372231309895746762734597)
                      ·
                        rfl

theorem cell23_6567397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_6567397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567397 prefixEnd_6567397 := by exact prefixLift 6567397
  have htrace : WordTrace (prefixWord ++ tailWord_6567397) baseStart_6567397 baseEnd_6567397 := by
    simpa [prefixWord, tailWord_6567397, baseEnd_6567397] using wordTrace_append hprefix tailTrace_6567397
  have hstable : (prefixWord ++ tailWord_6567397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567397).length < 2 ^ (prefixWord ++ tailWord_6567397).sum := by decide
  have hdescent : baseEnd_6567397 < baseStart_6567397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567428 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6567428 : Nat := 118140960795 + 6567428 * 2 ^ 59
def prefixEnd_6567428 : Nat := 4983230072969 + 3 ^ 40 * 6567428 * 2
def baseEnd_6567428 : Nat := 3372247227796036141446955

theorem tailTrace_6567428 : CollatzResearch.WordTrace tailWord_6567428 prefixEnd_6567428 3372247227796036141446955 := by
  unfold tailWord_6567428
  simp only [CollatzResearch.WordTrace]
  refine ⟨119766888825668729125095469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159689185100891638833460625 119766888825668729125095469)
  ·
    refine ⟨44912583309625773421910801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119766888825668729125095469 44912583309625773421910801)
    ·
      refine ⟨33684437482219330066433101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44912583309625773421910801 33684437482219330066433101)
      ·
        refine ⟨12631664055832248774912413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33684437482219330066433101 12631664055832248774912413)
        ·
          refine ⟨4736874020937093290592155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12631664055832248774912413 4736874020937093290592155)
          ·
            refine ⟨7105311031405639935888233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4736874020937093290592155 7105311031405639935888233)
            ·
              refine ⟨5328983273554229951916175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7105311031405639935888233 5328983273554229951916175)
              ·
                refine ⟨7993474910331344927874263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328983273554229951916175 7993474910331344927874263)
                ·
                  refine ⟨11990212365497017391811395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993474910331344927874263 11990212365497017391811395)
                  ·
                    refine ⟨17985318548245526087717093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11990212365497017391811395 17985318548245526087717093)
                    ·
                      refine ⟨3372247227796036141446955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17985318548245526087717093 3372247227796036141446955)
                      ·
                        rfl

theorem cell23_6567428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6567428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567428 prefixEnd_6567428 := by exact prefixLift 6567428
  have htrace : WordTrace (prefixWord ++ tailWord_6567428) baseStart_6567428 baseEnd_6567428 := by
    simpa [prefixWord, tailWord_6567428, baseEnd_6567428] using wordTrace_append hprefix tailTrace_6567428
  have hstable : (prefixWord ++ tailWord_6567428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567428).length < 2 ^ (prefixWord ++ tailWord_6567428).sum := by decide
  have hdescent : baseEnd_6567428 < baseStart_6567428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567431 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 1, 2, 3]
def baseStart_6567431 : Nat := 118140960795 + 6567431 * 2 ^ 59
def prefixEnd_6567431 : Nat := 4983230072969 + 3 ^ 40 * 6567431 * 2
def baseEnd_6567431 : Nat := 3372248768237999629709441

theorem tailTrace_6567431 : CollatzResearch.WordTrace tailWord_6567431 prefixEnd_6567431 3372248768237999629709441 := by
  unfold tailWord_6567431
  simp only [CollatzResearch.WordTrace]
  refine ⟨239533887070326589762550147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159689258046884393175033431 239533887070326589762550147)
  ·
    refine ⟨359300830605489884643825221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 239533887070326589762550147 359300830605489884643825221)
    ·
      refine ⟨67368905738529353370717229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 359300830605489884643825221 67368905738529353370717229)
      ·
        refine ⟨25263339651948507514018961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67368905738529353370717229 25263339651948507514018961)
        ·
          refine ⟨18947504738961380635514221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25263339651948507514018961 18947504738961380635514221)
          ·
            refine ⟨7105314277110517738317833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18947504738961380635514221 7105314277110517738317833)
            ·
              refine ⟨5328985707832888303738375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7105314277110517738317833 5328985707832888303738375)
              ·
                refine ⟨7993478561749332455607563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5328985707832888303738375 7993478561749332455607563)
                ·
                  refine ⟨11990217842623998683411345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7993478561749332455607563 11990217842623998683411345)
                  ·
                    refine ⟨8992663381967999012558509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11990217842623998683411345 8992663381967999012558509)
                    ·
                      refine ⟨3372248768237999629709441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8992663381967999012558509 3372248768237999629709441)
                      ·
                        rfl

theorem cell23_6567431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_6567431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567431 prefixEnd_6567431 := by exact prefixLift 6567431
  have htrace : WordTrace (prefixWord ++ tailWord_6567431) baseStart_6567431 baseEnd_6567431 := by
    simpa [prefixWord, tailWord_6567431, baseEnd_6567431] using wordTrace_append hprefix tailTrace_6567431
  have hstable : (prefixWord ++ tailWord_6567431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567431).length < 2 ^ (prefixWord ++ tailWord_6567431).sum := by decide
  have hdescent : baseEnd_6567431 < baseStart_6567431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567520 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 6, 5]
def baseStart_6567520 : Nat := 118140960795 + 6567520 * 2 ^ 59
def prefixEnd_6567520 : Nat := 4983230072969 + 3 ^ 40 * 6567520 * 2
def baseEnd_6567520 : Nat := 1124098156005416593832177

theorem tailTrace_6567520 : CollatzResearch.WordTrace tailWord_6567520 prefixEnd_6567520 1124098156005416593832177 := by
  unfold tailWord_6567520
  simp only [CollatzResearch.WordTrace]
  refine ⟨119768566583502078981270007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159691422111336105308360009 119768566583502078981270007)
  ·
    refine ⟨179652849875253118471905011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119768566583502078981270007 179652849875253118471905011)
    ·
      refine ⟨269479274812879677707857517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179652849875253118471905011 269479274812879677707857517)
      ·
        refine ⟨101054728054829879140446569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 269479274812879677707857517 101054728054829879140446569)
        ·
          refine ⟨75791046041122409355334927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101054728054829879140446569 75791046041122409355334927)
          ·
            refine ⟨113686569061683614033002391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75791046041122409355334927 113686569061683614033002391)
            ·
              refine ⟨170529853592525421049503587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113686569061683614033002391 170529853592525421049503587)
              ·
                refine ⟨255794780388788131574255381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170529853592525421049503587 255794780388788131574255381)
                ·
                  refine ⟨11990380330724443667543221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 255794780388788131574255381 11990380330724443667543221)
                  ·
                    refine ⟨1124098156005416593832177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11990380330724443667543221 1124098156005416593832177)
                    ·
                      rfl

theorem cell23_6567520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 6, 5].length) (baseStart_6567520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567520 prefixEnd_6567520 := by exact prefixLift 6567520
  have htrace : WordTrace (prefixWord ++ tailWord_6567520) baseStart_6567520 baseEnd_6567520 := by
    simpa [prefixWord, tailWord_6567520, baseEnd_6567520] using wordTrace_append hprefix tailTrace_6567520
  have hstable : (prefixWord ++ tailWord_6567520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567520).length < 2 ^ (prefixWord ++ tailWord_6567520).sum := by decide
  have hdescent : baseEnd_6567520 < baseStart_6567520 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567557 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 4]
def baseStart_6567557 : Nat := 118140960795 + 6567557 * 2 ^ 59
def prefixEnd_6567557 : Nat := 4983230072969 + 3 ^ 40 * 6567557 * 2
def baseEnd_6567557 : Nat := 3372313466800466136733861

theorem tailTrace_6567557 : CollatzResearch.WordTrace tailWord_6567557 prefixEnd_6567557 3372313466800466136733861 := by
  unfold tailWord_6567557
  simp only [CollatzResearch.WordTrace]
  refine ⟨239538482667870113281636925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159692321778580075521091283 239538482667870113281636925)
  ·
    refine ⟨89826931000451292480613847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 239538482667870113281636925 89826931000451292480613847)
    ·
      refine ⟨134740396500676938720920771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89826931000451292480613847 134740396500676938720920771)
      ·
        refine ⟨202110594751015408081381157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134740396500676938720920771 202110594751015408081381157)
        ·
          refine ⟨37895736515815389015258967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 202110594751015408081381157 37895736515815389015258967)
          ·
            refine ⟨56843604773723083522888451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37895736515815389015258967 56843604773723083522888451)
            ·
              refine ⟨85265407160584625284332677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56843604773723083522888451 85265407160584625284332677)
              ·
                refine ⟨15987263842609617240812377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85265407160584625284332677 15987263842609617240812377)
                ·
                  refine ⟨11990447881957212930609283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15987263842609617240812377 11990447881957212930609283)
                  ·
                    refine ⟨17985671822935819395913925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11990447881957212930609283 17985671822935819395913925)
                    ·
                      refine ⟨3372313466800466136733861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17985671822935819395913925 3372313466800466136733861)
                      ·
                        rfl

theorem cell23_6567557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 1, 4].length) (baseStart_6567557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567557 prefixEnd_6567557 := by exact prefixLift 6567557
  have htrace : WordTrace (prefixWord ++ tailWord_6567557) baseStart_6567557 baseEnd_6567557 := by
    simpa [prefixWord, tailWord_6567557, baseEnd_6567557] using wordTrace_append hprefix tailTrace_6567557
  have hstable : (prefixWord ++ tailWord_6567557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567557).length < 2 ^ (prefixWord ++ tailWord_6567557).sum := by decide
  have hdescent : baseEnd_6567557 < baseStart_6567557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567584 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 3, 4]
def baseStart_6567584 : Nat := 118140960795 + 6567584 * 2 ^ 59
def prefixEnd_6567584 : Nat := 4983230072969 + 3 ^ 40 * 6567584 * 2
def baseEnd_6567584 : Nat := 1124109110259379177032079

theorem tailTrace_6567584 : CollatzResearch.WordTrace tailWord_6567584 prefixEnd_6567584 1124109110259379177032079 := by
  unfold tailWord_6567584
  simp only [CollatzResearch.WordTrace]
  refine ⟨119769733719386148446434903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 159692978292514864595246537 119769733719386148446434903)
  ·
    refine ⟨179654600579079222669652355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119769733719386148446434903 179654600579079222669652355)
    ·
      refine ⟨269481900868618834004478533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179654600579079222669652355 269481900868618834004478533)
      ·
        refine ⟨50527856412866031375839725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 269481900868618834004478533 50527856412866031375839725)
        ·
          refine ⟨18947946154824761765939897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50527856412866031375839725 18947946154824761765939897)
          ·
            refine ⟨14210959616118571324454923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18947946154824761765939897 14210959616118571324454923)
            ·
              refine ⟨21316439424177856986682385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14210959616118571324454923 21316439424177856986682385)
              ·
                refine ⟨15987329568133392740011789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21316439424177856986682385 15987329568133392740011789)
                ·
                  refine ⟨5995248588050022277504421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15987329568133392740011789 5995248588050022277504421)
                  ·
                    refine ⟨1124109110259379177032079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5995248588050022277504421 1124109110259379177032079)
                    ·
                      rfl

theorem cell23_6567584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 3, 4].length) (baseStart_6567584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567584 prefixEnd_6567584 := by exact prefixLift 6567584
  have htrace : WordTrace (prefixWord ++ tailWord_6567584) baseStart_6567584 baseEnd_6567584 := by
    simpa [prefixWord, tailWord_6567584, baseEnd_6567584] using wordTrace_append hprefix tailTrace_6567584
  have hstable : (prefixWord ++ tailWord_6567584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567584).length < 2 ^ (prefixWord ++ tailWord_6567584).sum := by decide
  have hdescent : baseEnd_6567584 < baseStart_6567584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567597 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 8]
def baseStart_6567597 : Nat := 118140960795 + 6567597 * 2 ^ 59
def prefixEnd_6567597 : Nat := 4983230072969 + 3 ^ 40 * 6567597 * 2
def baseEnd_6567597 : Nat := 374703778447405108914853

theorem tailTrace_6567597 : CollatzResearch.WordTrace tailWord_6567597 prefixEnd_6567597 374703778447405108914853 := by
  unfold tailWord_6567597
  simp only [CollatzResearch.WordTrace]
  refine ⟨239539941587725200113093045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 159693294391816800075395363 239539941587725200113093045)
  ·
    refine ⟨22456869523849237510602473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 239539941587725200113093045 22456869523849237510602473)
    ·
      refine ⟨16842652142886928132951855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22456869523849237510602473 16842652142886928132951855)
      ·
        refine ⟨25263978214330392199427783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16842652142886928132951855 25263978214330392199427783)
        ·
          refine ⟨37895967321495588299141675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25263978214330392199427783 37895967321495588299141675)
          ·
            refine ⟨56843950982243382448712513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37895967321495588299141675 56843950982243382448712513)
            ·
              refine ⟨42632963236682536836534385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56843950982243382448712513 42632963236682536836534385)
              ·
                refine ⟨31974722427511902627400789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42632963236682536836534385 31974722427511902627400789)
                ·
                  refine ⟨374703778447405108914853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31974722427511902627400789 374703778447405108914853)
                  ·
                    rfl

theorem cell23_6567597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_6567597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567597 prefixEnd_6567597 := by exact prefixLift 6567597
  have htrace : WordTrace (prefixWord ++ tailWord_6567597) baseStart_6567597 baseEnd_6567597 := by
    simpa [prefixWord, tailWord_6567597, baseEnd_6567597] using wordTrace_append hprefix tailTrace_6567597
  have hstable : (prefixWord ++ tailWord_6567597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567597).length < 2 ^ (prefixWord ++ tailWord_6567597).sum := by decide
  have hdescent : baseEnd_6567597 < baseStart_6567597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567614 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 6]
def baseStart_6567614 : Nat := 118140960795 + 6567614 * 2 ^ 59
def prefixEnd_6567614 : Nat := 4983230072969 + 3 ^ 40 * 6567614 * 2
def baseEnd_6567614 : Nat := 374704748355308045969011

theorem tailTrace_6567614 : CollatzResearch.WordTrace tailWord_6567614 prefixEnd_6567614 374704748355308045969011 := by
  unfold tailWord_6567614
  simp only [CollatzResearch.WordTrace]
  refine ⟨29942570203582951502057737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 159693707752442408010974597 29942570203582951502057737)
  ·
    refine ⟨22456927652687213626543303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29942570203582951502057737 22456927652687213626543303)
    ·
      refine ⟨33685391479030820439814955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22456927652687213626543303 33685391479030820439814955)
      ·
        refine ⟨50528087218546230659722433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33685391479030820439814955 50528087218546230659722433)
        ·
          refine ⟨37896065413909672994791825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50528087218546230659722433 37896065413909672994791825)
          ·
            refine ⟨28422049060432254746093869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37896065413909672994791825 28422049060432254746093869)
            ·
              refine ⟨10658268397662095529785201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28422049060432254746093869 10658268397662095529785201)
              ·
                refine ⟨7993701298246571647338901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10658268397662095529785201 7993701298246571647338901)
                ·
                  refine ⟨374704748355308045969011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7993701298246571647338901 374704748355308045969011)
                  ·
                    rfl

theorem cell23_6567614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_6567614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567614 prefixEnd_6567614 := by exact prefixLift 6567614
  have htrace : WordTrace (prefixWord ++ tailWord_6567614) baseStart_6567614 baseEnd_6567614 := by
    simpa [prefixWord, tailWord_6567614, baseEnd_6567614] using wordTrace_append hprefix tailTrace_6567614
  have hstable : (prefixWord ++ tailWord_6567614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567614).length < 2 ^ (prefixWord ++ tailWord_6567614).sum := by decide
  have hdescent : baseEnd_6567614 < baseStart_6567614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6567658 : List Nat := [3, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_6567658 : Nat := 118140960795 + 6567658 * 2 ^ 59
def prefixEnd_6567658 : Nat := 4983230072969 + 3 ^ 40 * 6567658 * 2
def baseEnd_6567658 : Nat := 3372365328346570241570897

theorem tailTrace_6567658 : CollatzResearch.WordTrace tailWord_6567658 prefixEnd_6567658 3372365328346570241570897 := by
  unfold tailWord_6567658
  simp only [CollatzResearch.WordTrace]
  refine ⟨59885541610126051882765907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 159694777627002805020709085 59885541610126051882765907)
  ·
    refine ⟨89828312415189077824148861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59885541610126051882765907 89828312415189077824148861)
    ·
      refine ⟨33685617155695904184055823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89828312415189077824148861 33685617155695904184055823)
      ·
        refine ⟨50528425733543856276083735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33685617155695904184055823 50528425733543856276083735)
        ·
          refine ⟨75792638600315784414125603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50528425733543856276083735 75792638600315784414125603)
          ·
            refine ⟨113688957900473676621188405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75792638600315784414125603 113688957900473676621188405)
            ·
              refine ⟨10658339803169407183236413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113688957900473676621188405 10658339803169407183236413)
              ·
                refine ⟨3996877426188527693713655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10658339803169407183236413 3996877426188527693713655)
                ·
                  refine ⟨5995316139282791540570483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3996877426188527693713655 5995316139282791540570483)
                  ·
                    refine ⟨8992974208924187310855725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5995316139282791540570483 8992974208924187310855725)
                    ·
                      refine ⟨3372365328346570241570897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8992974208924187310855725 3372365328346570241570897)
                      ·
                        rfl

theorem cell23_6567658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_6567658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6567658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6567658 prefixEnd_6567658 := by exact prefixLift 6567658
  have htrace : WordTrace (prefixWord ++ tailWord_6567658) baseStart_6567658 baseEnd_6567658 := by
    simpa [prefixWord, tailWord_6567658, baseEnd_6567658] using wordTrace_append hprefix tailTrace_6567658
  have hstable : (prefixWord ++ tailWord_6567658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6567658).length < 2 ^ (prefixWord ++ tailWord_6567658).sum := by decide
  have hdescent : baseEnd_6567658 < baseStart_6567658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6567658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
