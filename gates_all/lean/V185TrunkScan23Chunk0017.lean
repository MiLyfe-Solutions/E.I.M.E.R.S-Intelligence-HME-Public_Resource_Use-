import V185TrunkScan23Chunk0016

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_100029 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_100029 : Nat := 118140960795 + 100029 * 2 ^ 59
def prefixEnd_100029 : Nat := 4983230072969 + 3 ^ 40 * 100029 * 2
def baseEnd_100029 : Nat := 51362956388694369777481

theorem tailTrace_100029 : CollatzResearch.WordTrace tailWord_100029 prefixEnd_100029 51362956388694369777481 := by
  unfold tailWord_100029
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648357354619491438215141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2432238236412994292143427 3648357354619491438215141)
  ·
    refine ⟨684067003991154644665339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3648357354619491438215141 684067003991154644665339)
    ·
      refine ⟨1026100505986731966998009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684067003991154644665339 1026100505986731966998009)
      ·
        refine ⟨769575379490048975248507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1026100505986731966998009 769575379490048975248507)
        ·
          refine ⟨1154363069235073462872761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 769575379490048975248507 1154363069235073462872761)
          ·
            refine ⟨865772301926305097154571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1154363069235073462872761 865772301926305097154571)
            ·
              refine ⟨1298658452889457645731857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865772301926305097154571 1298658452889457645731857)
              ·
                refine ⟨973993839667093234298893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1298658452889457645731857 973993839667093234298893)
                ·
                  refine ⟨365247689875159962862085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 973993839667093234298893 365247689875159962862085)
                  ·
                    refine ⟨68483941851592493036641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 365247689875159962862085 68483941851592493036641)
                    ·
                      refine ⟨51362956388694369777481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68483941851592493036641 51362956388694369777481)
                      ·
                        rfl

theorem cell23_100029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_100029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100029 prefixEnd_100029 := by exact prefixLift 100029
  have htrace : WordTrace (prefixWord ++ tailWord_100029) baseStart_100029 baseEnd_100029 := by
    simpa [prefixWord, tailWord_100029, baseEnd_100029] using wordTrace_append hprefix tailTrace_100029
  have hstable : (prefixWord ++ tailWord_100029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100029).length < 2 ^ (prefixWord ++ tailWord_100029).sum := by decide
  have hdescent : baseEnd_100029 < baseStart_100029 := by decide
  rcases family_descends (prefixWord ++ tailWord_100029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100032 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_100032 : Nat := 118140960795 + 100032 * 2 ^ 59
def prefixEnd_100032 : Nat := 4983230072969 + 3 ^ 40 * 100032 * 2
def baseEnd_100032 : Nat := 51364496830657858039967

theorem tailTrace_100032 : CollatzResearch.WordTrace tailWord_100032 prefixEnd_100032 51364496830657858039967 := by
  unfold tailWord_100032
  simp only [CollatzResearch.WordTrace]
  refine ⟨1824233386804311475287175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2432311182405748633716233 1824233386804311475287175)
  ·
    refine ⟨2736350080206467212930763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1824233386804311475287175 2736350080206467212930763)
    ·
      refine ⟨4104525120309700819396145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2736350080206467212930763 4104525120309700819396145)
      ·
        refine ⟨3078393840232275614547109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4104525120309700819396145 3078393840232275614547109)
        ·
          refine ⟨577198845043551677727583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3078393840232275614547109 577198845043551677727583)
          ·
            refine ⟨865798267565327516591375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577198845043551677727583 865798267565327516591375)
            ·
              refine ⟨1298697401347991274887063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 865798267565327516591375 1298697401347991274887063)
              ·
                refine ⟨1948046102021986912330595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1298697401347991274887063 1948046102021986912330595)
                ·
                  refine ⟨2922069153032980368495893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1948046102021986912330595 2922069153032980368495893)
                  ·
                    refine ⟨136971991548420954773245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2922069153032980368495893 136971991548420954773245)
                    ·
                      refine ⟨51364496830657858039967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 136971991548420954773245 51364496830657858039967)
                      ·
                        rfl

theorem cell23_100032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_100032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100032 prefixEnd_100032 := by exact prefixLift 100032
  have htrace : WordTrace (prefixWord ++ tailWord_100032) baseStart_100032 baseEnd_100032 := by
    simpa [prefixWord, tailWord_100032, baseEnd_100032] using wordTrace_append hprefix tailTrace_100032
  have hstable : (prefixWord ++ tailWord_100032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100032).length < 2 ^ (prefixWord ++ tailWord_100032).sum := by decide
  have hdescent : baseEnd_100032 < baseStart_100032 := by decide
  rcases family_descends (prefixWord ++ tailWord_100032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100035 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 13]
def baseStart_100035 : Nat := 118140960795 + 100035 * 2 ^ 59
def prefixEnd_100035 : Nat := 4983230072969 + 3 ^ 40 * 100035 * 2
def baseEnd_100035 : Nat := 5707337474735705144717

theorem tailTrace_100035 : CollatzResearch.WordTrace tailWord_100035 prefixEnd_100035 5707337474735705144717 := by
  unfold tailWord_100035
  simp only [CollatzResearch.WordTrace]
  refine ⟨3648576192597754462933559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2432384128398502975289039 3648576192597754462933559)
  ·
    refine ⟨5472864288896631694400339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3648576192597754462933559 5472864288896631694400339)
    ·
      refine ⟨8209296433344947541600509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5472864288896631694400339 8209296433344947541600509)
      ·
        refine ⟨3078486162504355328100191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8209296433344947541600509 3078486162504355328100191)
        ·
          refine ⟨4617729243756532992150287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3078486162504355328100191 4617729243756532992150287)
          ·
            refine ⟨6926593865634799488225431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4617729243756532992150287 6926593865634799488225431)
            ·
              refine ⟨10389890798452199232338147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6926593865634799488225431 10389890798452199232338147)
              ·
                refine ⟨15584836197678298848507221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10389890798452199232338147 15584836197678298848507221)
                ·
                  refine ⟨5707337474735705144717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 13 15584836197678298848507221 5707337474735705144717)
                  ·
                    rfl

theorem cell23_100035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 13].length) (baseStart_100035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100035 prefixEnd_100035 := by exact prefixLift 100035
  have htrace : WordTrace (prefixWord ++ tailWord_100035) baseStart_100035 baseEnd_100035 := by
    simpa [prefixWord, tailWord_100035, baseEnd_100035] using wordTrace_append hprefix tailTrace_100035
  have hstable : (prefixWord ++ tailWord_100035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100035).length < 2 ^ (prefixWord ++ tailWord_100035).sum := by decide
  have hdescent : baseEnd_100035 < baseStart_100035 := by decide
  rcases family_descends (prefixWord ++ tailWord_100035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100046 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_100046 : Nat := 118140960795 + 100046 * 2 ^ 59
def prefixEnd_100046 : Nat := 4983230072969 + 3 ^ 40 * 100046 * 2
def baseEnd_100046 : Nat := 51371685559820803264903

theorem tailTrace_100046 : CollatzResearch.WordTrace tailWord_100046 prefixEnd_100046 51371685559820803264903 := by
  unfold tailWord_100046
  simp only [CollatzResearch.WordTrace]
  refine ⟨456122174444737917697999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2432651597038602227722661 456122174444737917697999)
  ·
    refine ⟨684183261667106876546999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 456122174444737917697999 684183261667106876546999)
    ·
      refine ⟨1026274892500660314820499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684183261667106876546999 1026274892500660314820499)
      ·
        refine ⟨1539412338750990472230749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026274892500660314820499 1539412338750990472230749)
        ·
          refine ⟨577279627031621427086531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1539412338750990472230749 577279627031621427086531)
          ·
            refine ⟨865919440547432140629797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577279627031621427086531 865919440547432140629797)
            ·
              refine ⟨162359895102643526368087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 865919440547432140629797 162359895102643526368087)
              ·
                refine ⟨243539842653965289552131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162359895102643526368087 243539842653965289552131)
                ·
                  refine ⟨365309763980947934328197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 243539842653965289552131 365309763980947934328197)
                  ·
                    refine ⟨68495580746427737686537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 365309763980947934328197 68495580746427737686537)
                    ·
                      refine ⟨51371685559820803264903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68495580746427737686537 51371685559820803264903)
                      ·
                        rfl

theorem cell23_100046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_100046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100046 prefixEnd_100046 := by exact prefixLift 100046
  have htrace : WordTrace (prefixWord ++ tailWord_100046) baseStart_100046 baseEnd_100046 := by
    simpa [prefixWord, tailWord_100046, baseEnd_100046] using wordTrace_append hprefix tailTrace_100046
  have hstable : (prefixWord ++ tailWord_100046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100046).length < 2 ^ (prefixWord ++ tailWord_100046).sum := by decide
  have hdescent : baseEnd_100046 < baseStart_100046 := by decide
  rcases family_descends (prefixWord ++ tailWord_100046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100067 : List Nat := [1, 1, 1, 7, 3, 1, 2, 1, 1, 3, 2]
def baseStart_100067 : Nat := 118140960795 + 100067 * 2 ^ 59
def prefixEnd_100067 : Nat := 4983230072969 + 3 ^ 40 * 100067 * 2
def baseEnd_100067 : Nat := 51382468653565221102307

theorem tailTrace_100067 : CollatzResearch.WordTrace tailWord_100067 prefixEnd_100067 51382468653565221102307 := by
  unfold tailWord_100067
  simp only [CollatzResearch.WordTrace]
  refine ⟨3649743328481823928098455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2433162218987882618732303 3649743328481823928098455)
  ·
    refine ⟨5474614992722735892147683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3649743328481823928098455 5474614992722735892147683)
    ·
      refine ⟨8211922489084103838221525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5474614992722735892147683 8211922489084103838221525)
      ·
        refine ⟨192466933337908683708317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8211922489084103838221525 192466933337908683708317)
        ·
          refine ⟨72175100001715756390619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 192466933337908683708317 72175100001715756390619)
          ·
            refine ⟨108262650002573634585929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72175100001715756390619 108262650002573634585929)
            ·
              refine ⟨81196987501930225939447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108262650002573634585929 81196987501930225939447)
              ·
                refine ⟨121795481252895338909171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81196987501930225939447 121795481252895338909171)
                ·
                  refine ⟨182693221879343008363757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 121795481252895338909171 182693221879343008363757)
                  ·
                    refine ⟨68509958204753628136409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 182693221879343008363757 68509958204753628136409)
                    ·
                      refine ⟨51382468653565221102307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68509958204753628136409 51382468653565221102307)
                      ·
                        rfl

theorem cell23_100067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_100067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100067 prefixEnd_100067 := by exact prefixLift 100067
  have htrace : WordTrace (prefixWord ++ tailWord_100067) baseStart_100067 baseEnd_100067 := by
    simpa [prefixWord, tailWord_100067, baseEnd_100067] using wordTrace_append hprefix tailTrace_100067
  have hstable : (prefixWord ++ tailWord_100067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100067).length < 2 ^ (prefixWord ++ tailWord_100067).sum := by decide
  have hdescent : baseEnd_100067 < baseStart_100067 := by decide
  rcases family_descends (prefixWord ++ tailWord_100067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100086 : List Nat := [5, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_100086 : Nat := 118140960795 + 100086 * 2 ^ 59
def prefixEnd_100086 : Nat := 4983230072969 + 3 ^ 40 * 100086 * 2
def baseEnd_100086 : Nat := 5710247198444516307191

theorem tailTrace_100086 : CollatzResearch.WordTrace tailWord_100086 prefixEnd_100086 5710247198444516307191 := by
  unfold tailWord_100086
  simp only [CollatzResearch.WordTrace]
  refine ⟨228152269713311885815007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2433624210275326782026741 228152269713311885815007)
  ·
    refine ⟨342228404569967828722511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 228152269713311885815007 342228404569967828722511)
    ·
      refine ⟨513342606854951743083767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 342228404569967828722511 513342606854951743083767)
      ·
        refine ⟨770013910282427614625651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 513342606854951743083767 770013910282427614625651)
        ·
          refine ⟨1155020865423641421938477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 770013910282427614625651 1155020865423641421938477)
          ·
            refine ⟨433132824533865533226929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1155020865423641421938477 433132824533865533226929)
            ·
              refine ⟨324849618400399149920197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433132824533865533226929 324849618400399149920197)
              ·
                refine ⟨60909303450074840610037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 324849618400399149920197 60909303450074840610037)
                ·
                  refine ⟨5710247198444516307191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 60909303450074840610037 5710247198444516307191)
                  ·
                    rfl

theorem cell23_100086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_100086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100086 prefixEnd_100086 := by exact prefixLift 100086
  have htrace : WordTrace (prefixWord ++ tailWord_100086) baseStart_100086 baseEnd_100086 := by
    simpa [prefixWord, tailWord_100086, baseEnd_100086] using wordTrace_append hprefix tailTrace_100086
  have hstable : (prefixWord ++ tailWord_100086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100086).length < 2 ^ (prefixWord ++ tailWord_100086).sum := by decide
  have hdescent : baseEnd_100086 < baseStart_100086 := by decide
  rcases family_descends (prefixWord ++ tailWord_100086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100092 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_100092 : Nat := 118140960795 + 100092 * 2 ^ 59
def prefixEnd_100092 : Nat := 4983230072969 + 3 ^ 40 * 100092 * 2
def baseEnd_100092 : Nat := 51395305669927623289691

theorem tailTrace_100092 : CollatzResearch.WordTrace tailWord_100092 prefixEnd_100092 51395305669927623289691 := by
  unfold tailWord_100092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1825327576695626598879265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2433770102260835465172353 1825327576695626598879265)
  ·
    refine ⟨1368995682521719949159449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1825327576695626598879265 1368995682521719949159449)
    ·
      refine ⟨1026746761891289961869587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1368995682521719949159449 1026746761891289961869587)
      ·
        refine ⟨1540120142836934942804381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1026746761891289961869587 1540120142836934942804381)
        ·
          refine ⟨577545053563850603551643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1540120142836934942804381 577545053563850603551643)
          ·
            refine ⟨866317580345775905327465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 577545053563850603551643 866317580345775905327465)
            ·
              refine ⟨649738185259331928995599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 866317580345775905327465 649738185259331928995599)
              ·
                refine ⟨974607277888997893493399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 649738185259331928995599 974607277888997893493399)
                ·
                  refine ⟨1461910916833496840240099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 974607277888997893493399 1461910916833496840240099)
                  ·
                    refine ⟨2192866375250245260360149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1461910916833496840240099 2192866375250245260360149)
                    ·
                      refine ⟨51395305669927623289691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2192866375250245260360149 51395305669927623289691)
                      ·
                        rfl

theorem cell23_100092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_100092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100092 prefixEnd_100092 := by exact prefixLift 100092
  have htrace : WordTrace (prefixWord ++ tailWord_100092) baseStart_100092 baseEnd_100092 := by
    simpa [prefixWord, tailWord_100092, baseEnd_100092] using wordTrace_append hprefix tailTrace_100092
  have hstable : (prefixWord ++ tailWord_100092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100092).length < 2 ^ (prefixWord ++ tailWord_100092).sum := by decide
  have hdescent : baseEnd_100092 < baseStart_100092 := by decide
  rcases family_descends (prefixWord ++ tailWord_100092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100119 : List Nat := [1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 4]
def baseStart_100119 : Nat := 118140960795 + 100119 * 2 ^ 59
def prefixEnd_100119 : Nat := 4983230072969 + 3 ^ 40 * 100119 * 2
def baseEnd_100119 : Nat := 51409169647599017652067

theorem tailTrace_100119 : CollatzResearch.WordTrace tailWord_100119 prefixEnd_100119 51409169647599017652067 := by
  unfold tailWord_100119
  simp only [CollatzResearch.WordTrace]
  refine ⟨3651639924293436808991411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2434426616195624539327607 3651639924293436808991411)
  ·
    refine ⟨5477459886440155213487117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3651639924293436808991411 5477459886440155213487117)
    ·
      refine ⟨2054047457415058205057669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5477459886440155213487117 2054047457415058205057669)
      ·
        refine ⟨385133898265323413448313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2054047457415058205057669 385133898265323413448313)
        ·
          refine ⟨288850423698992560086235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385133898265323413448313 288850423698992560086235)
          ·
            refine ⟨433275635548488840129353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 288850423698992560086235 433275635548488840129353)
            ·
              refine ⟨324956726661366630097015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 433275635548488840129353 324956726661366630097015)
              ·
                refine ⟨487435089992049945145523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 324956726661366630097015 487435089992049945145523)
                ·
                  refine ⟨731152634988074917718285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 487435089992049945145523 731152634988074917718285)
                  ·
                    refine ⟨274182238120528094144357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 731152634988074917718285 274182238120528094144357)
                    ·
                      refine ⟨51409169647599017652067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 274182238120528094144357 51409169647599017652067)
                      ·
                        rfl

theorem cell23_100119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_100119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100119 prefixEnd_100119 := by exact prefixLift 100119
  have htrace : WordTrace (prefixWord ++ tailWord_100119) baseStart_100119 baseEnd_100119 := by
    simpa [prefixWord, tailWord_100119, baseEnd_100119] using wordTrace_append hprefix tailTrace_100119
  have hstable : (prefixWord ++ tailWord_100119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100119).length < 2 ^ (prefixWord ++ tailWord_100119).sum := by decide
  have hdescent : baseEnd_100119 < baseStart_100119 := by decide
  rcases family_descends (prefixWord ++ tailWord_100119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100136 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_100136 : Nat := 118140960795 + 100136 * 2 ^ 59
def prefixEnd_100136 : Nat := 4983230072969 + 3 ^ 40 * 100136 * 2
def baseEnd_100136 : Nat := 51417898818725451139489

theorem tailTrace_100136 : CollatzResearch.WordTrace tailWord_100136 prefixEnd_100136 51417898818725451139489 := by
  unfold tailWord_100136
  simp only [CollatzResearch.WordTrace]
  refine ⟨1826129982615924356180131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2434839976821232474906841 1826129982615924356180131)
  ·
    refine ⟨2739194973923886534270197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1826129982615924356180131 2739194973923886534270197)
    ·
      refine ⟨256799528805364362587831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2739194973923886534270197 256799528805364362587831)
      ·
        refine ⟨385199293208046543881747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 256799528805364362587831 385199293208046543881747)
        ·
          refine ⟨577798939812069815822621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 385199293208046543881747 577798939812069815822621)
          ·
            refine ⟨216674602429526180933483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 577798939812069815822621 216674602429526180933483)
            ·
              refine ⟨325011903644289271400225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 216674602429526180933483 325011903644289271400225)
              ·
                refine ⟨243758927733216953550169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 325011903644289271400225 243758927733216953550169)
                ·
                  refine ⟨182819195799912715162627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243758927733216953550169 182819195799912715162627)
                  ·
                    refine ⟨274228793699869072743941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182819195799912715162627 274228793699869072743941)
                    ·
                      refine ⟨51417898818725451139489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 274228793699869072743941 51417898818725451139489)
                      ·
                        rfl

theorem cell23_100136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_100136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100136 prefixEnd_100136 := by exact prefixLift 100136
  have htrace : WordTrace (prefixWord ++ tailWord_100136) baseStart_100136 baseEnd_100136 := by
    simpa [prefixWord, tailWord_100136, baseEnd_100136] using wordTrace_append hprefix tailTrace_100136
  have hstable : (prefixWord ++ tailWord_100136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100136).length < 2 ^ (prefixWord ++ tailWord_100136).sum := by decide
  have hdescent : baseEnd_100136 < baseStart_100136 := by decide
  rcases family_descends (prefixWord ++ tailWord_100136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100146 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 3, 4]
def baseStart_100146 : Nat := 118140960795 + 100146 * 2 ^ 59
def prefixEnd_100146 : Nat := 4983230072969 + 3 ^ 40 * 100146 * 2
def baseEnd_100146 : Nat := 17141011208423470671481

theorem tailTrace_100146 : CollatzResearch.WordTrace tailWord_100146 prefixEnd_100146 17141011208423470671481 := by
  unfold tailWord_100146
  simp only [CollatzResearch.WordTrace]
  refine ⟨913156173798905105056073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2435083130130413613482861 913156173798905105056073)
  ·
    refine ⟨684867130349178828792055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 913156173798905105056073 684867130349178828792055)
    ·
      refine ⟨1027300695523768243188083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 684867130349178828792055 1027300695523768243188083)
      ·
        refine ⟨1540951043285652364782125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1027300695523768243188083 1540951043285652364782125)
        ·
          refine ⟨577856641232119636793297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1540951043285652364782125 577856641232119636793297)
          ·
            refine ⟨433392480924089727594973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 577856641232119636793297 433392480924089727594973)
            ·
              refine ⟨162522180346533647848115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433392480924089727594973 162522180346533647848115)
              ·
                refine ⟨243783270519800471772173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162522180346533647848115 243783270519800471772173)
                ·
                  refine ⟨91418726444925176914565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 243783270519800471772173 91418726444925176914565)
                  ·
                    refine ⟨17141011208423470671481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91418726444925176914565 17141011208423470671481)
                    ·
                      rfl

theorem cell23_100146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_100146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100146 prefixEnd_100146 := by exact prefixLift 100146
  have htrace : WordTrace (prefixWord ++ tailWord_100146) baseStart_100146 baseEnd_100146 := by
    simpa [prefixWord, tailWord_100146, baseEnd_100146] using wordTrace_append hprefix tailTrace_100146
  have hstable : (prefixWord ++ tailWord_100146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100146).length < 2 ^ (prefixWord ++ tailWord_100146).sum := by decide
  have hdescent : baseEnd_100146 < baseStart_100146 := by decide
  rcases family_descends (prefixWord ++ tailWord_100146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100173 : List Nat := [1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 3]
def baseStart_100173 : Nat := 118140960795 + 100173 * 2 ^ 59
def prefixEnd_100173 : Nat := 4983230072969 + 3 ^ 40 * 100173 * 2
def baseEnd_100173 : Nat := 51436897602941806376819

theorem tailTrace_100173 : CollatzResearch.WordTrace tailWord_100173 prefixEnd_100173 51436897602941806376819 := by
  unfold tailWord_100173
  simp only [CollatzResearch.WordTrace]
  refine ⟨3653609466097804031457173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2435739644065202687638115 3653609466097804031457173)
  ·
    refine ⟨171262943723334563974555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3653609466097804031457173 171262943723334563974555)
    ·
      refine ⟨256894415585001845961833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 171262943723334563974555 256894415585001845961833)
      ·
        refine ⟨192670811688751384471375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 256894415585001845961833 192670811688751384471375)
        ·
          refine ⟨289006217533127076707063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192670811688751384471375 289006217533127076707063)
          ·
            refine ⟨433509326299690615060595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289006217533127076707063 433509326299690615060595)
            ·
              refine ⟨650263989449535922590893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433509326299690615060595 650263989449535922590893)
              ·
                refine ⟨243848996043575970971585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 650263989449535922590893 243848996043575970971585)
                ·
                  refine ⟨182886747032681978228689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 243848996043575970971585 182886747032681978228689)
                  ·
                    refine ⟨137165060274511483671517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 182886747032681978228689 137165060274511483671517)
                    ·
                      refine ⟨51436897602941806376819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 137165060274511483671517 51436897602941806376819)
                      ·
                        rfl

theorem cell23_100173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_100173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100173 prefixEnd_100173 := by exact prefixLift 100173
  have htrace : WordTrace (prefixWord ++ tailWord_100173) baseStart_100173 baseEnd_100173 := by
    simpa [prefixWord, tailWord_100173, baseEnd_100173] using wordTrace_append hprefix tailTrace_100173
  have hstable : (prefixWord ++ tailWord_100173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100173).length < 2 ^ (prefixWord ++ tailWord_100173).sum := by decide
  have hdescent : baseEnd_100173 < baseStart_100173 := by decide
  rcases family_descends (prefixWord ++ tailWord_100173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100206 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_100206 : Nat := 118140960795 + 100206 * 2 ^ 59
def prefixEnd_100206 : Nat := 4983230072969 + 3 ^ 40 * 100206 * 2
def baseEnd_100206 : Nat := 17151280821513392421389

theorem tailTrace_100206 : CollatzResearch.WordTrace tailWord_100206 prefixEnd_100206 17151280821513392421389 := by
  unfold tailWord_100206
  simp only [CollatzResearch.WordTrace]
  refine ⟨456851634372281333426059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2436542049985500444938981 456851634372281333426059)
  ·
    refine ⟨685277451558422000139089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 456851634372281333426059 685277451558422000139089)
    ·
      refine ⟨513958088668816500104317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 685277451558422000139089 513958088668816500104317)
      ·
        refine ⟨192734283250806187539119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 513958088668816500104317 192734283250806187539119)
        ·
          refine ⟨289101424876209281308679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 192734283250806187539119 289101424876209281308679)
          ·
            refine ⟨433652137314313921963019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289101424876209281308679 433652137314313921963019)
            ·
              refine ⟨650478205971470882944529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 433652137314313921963019 650478205971470882944529)
              ·
                refine ⟨487858654478603162208397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 650478205971470882944529 487858654478603162208397)
                ·
                  refine ⟨182946995429476185828149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 487858654478603162208397 182946995429476185828149)
                  ·
                    refine ⟨17151280821513392421389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 182946995429476185828149 17151280821513392421389)
                    ·
                      rfl

theorem cell23_100206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_100206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100206 prefixEnd_100206 := by exact prefixLift 100206
  have htrace : WordTrace (prefixWord ++ tailWord_100206) baseStart_100206 baseEnd_100206 := by
    simpa [prefixWord, tailWord_100206, baseEnd_100206] using wordTrace_append hprefix tailTrace_100206
  have hstable : (prefixWord ++ tailWord_100206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100206).length < 2 ^ (prefixWord ++ tailWord_100206).sum := by decide
  have hdescent : baseEnd_100206 < baseStart_100206 := by decide
  rcases family_descends (prefixWord ++ tailWord_100206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100209 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_100209 : Nat := 118140960795 + 100209 * 2 ^ 59
def prefixEnd_100209 : Nat := 4983230072969 + 3 ^ 40 * 100209 * 2
def baseEnd_100209 : Nat := 51455382906503665526653

theorem tailTrace_100209 : CollatzResearch.WordTrace tailWord_100209 prefixEnd_100209 51455382906503665526653 := by
  unfold tailWord_100209
  simp only [CollatzResearch.WordTrace]
  refine ⟨3654922493967382179767681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2436614995978254786511787 3654922493967382179767681)
  ·
    refine ⟨2741191870475536634825761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3654922493967382179767681 2741191870475536634825761)
    ·
      refine ⟨2055893902856652476119321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2741191870475536634825761 2055893902856652476119321)
      ·
        refine ⟨1541920427142489357089491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2055893902856652476119321 1541920427142489357089491)
        ·
          refine ⟨2312880640713734035634237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1541920427142489357089491 2312880640713734035634237)
          ·
            refine ⟨867330240267650263362839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2312880640713734035634237 867330240267650263362839)
            ·
              refine ⟨1300995360401475395044259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 867330240267650263362839 1300995360401475395044259)
              ·
                refine ⟨1951493040602213092566389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1300995360401475395044259 1951493040602213092566389)
                ·
                  refine ⟨182952472556457477428099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1951493040602213092566389 182952472556457477428099)
                  ·
                    refine ⟨274428708834686216142149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 182952472556457477428099 274428708834686216142149)
                    ·
                      refine ⟨51455382906503665526653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 274428708834686216142149 51455382906503665526653)
                      ·
                        rfl

theorem cell23_100209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_100209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100209 prefixEnd_100209 := by exact prefixLift 100209
  have htrace : WordTrace (prefixWord ++ tailWord_100209) baseStart_100209 baseEnd_100209 := by
    simpa [prefixWord, tailWord_100209, baseEnd_100209] using wordTrace_append hprefix tailTrace_100209
  have hstable : (prefixWord ++ tailWord_100209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100209).length < 2 ^ (prefixWord ++ tailWord_100209).sum := by decide
  have hdescent : baseEnd_100209 < baseStart_100209 := by decide
  rcases family_descends (prefixWord ++ tailWord_100209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100219 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 6, 4]
def baseStart_100219 : Nat := 118140960795 + 100219 * 2 ^ 59
def prefixEnd_100219 : Nat := 4983230072969 + 3 ^ 40 * 100219 * 2
def baseEnd_100219 : Nat := 17153505904349542133869

theorem tailTrace_100219 : CollatzResearch.WordTrace tailWord_100219 prefixEnd_100219 17153505904349542133869 := by
  unfold tailWord_100219
  simp only [CollatzResearch.WordTrace]
  refine ⟨3655287223931153887631711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2436858149287435925087807 3655287223931153887631711)
  ·
    refine ⟨5482930835896730831447567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3655287223931153887631711 5482930835896730831447567)
    ·
      refine ⟨8224396253845096247171351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5482930835896730831447567 8224396253845096247171351)
      ·
        refine ⟨12336594380767644370757027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8224396253845096247171351 12336594380767644370757027)
        ·
          refine ⟨18504891571151466556135541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12336594380767644370757027 18504891571151466556135541)
          ·
            refine ⟨1734833584795449989637707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18504891571151466556135541 1734833584795449989637707)
            ·
              refine ⟨2602250377193174984456561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1734833584795449989637707 2602250377193174984456561)
              ·
                refine ⟨1951687782894881238342421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2602250377193174984456561 1951687782894881238342421)
                ·
                  refine ⟨91485364823197558047301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1951687782894881238342421 91485364823197558047301)
                  ·
                    refine ⟨17153505904349542133869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91485364823197558047301 17153505904349542133869)
                    ·
                      rfl

theorem cell23_100219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 6, 4].length) (baseStart_100219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100219 prefixEnd_100219 := by exact prefixLift 100219
  have htrace : WordTrace (prefixWord ++ tailWord_100219) baseStart_100219 baseEnd_100219 := by
    simpa [prefixWord, tailWord_100219, baseEnd_100219] using wordTrace_append hprefix tailTrace_100219
  have hstable : (prefixWord ++ tailWord_100219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100219).length < 2 ^ (prefixWord ++ tailWord_100219).sum := by decide
  have hdescent : baseEnd_100219 < baseStart_100219 := by decide
  rcases family_descends (prefixWord ++ tailWord_100219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100253 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_100253 : Nat := 118140960795 + 100253 * 2 ^ 59
def prefixEnd_100253 : Nat := 4983230072969 + 3 ^ 40 * 100253 * 2
def baseEnd_100253 : Nat := 17159325351767164458817

theorem tailTrace_100253 : CollatzResearch.WordTrace tailWord_100253 prefixEnd_100253 17159325351767164458817 := by
  unfold tailWord_100253
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656527305807977694369413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2437684870538651796246275 3656527305807977694369413)
  ·
    refine ⟨685598869838995817694265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3656527305807977694369413 685598869838995817694265)
    ·
      refine ⟨514199152379246863270699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 685598869838995817694265 514199152379246863270699)
      ·
        refine ⟨771298728568870294906049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514199152379246863270699 771298728568870294906049)
        ·
          refine ⟨578474046426652721179537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 771298728568870294906049 578474046426652721179537)
          ·
            refine ⟨433855534819989540884653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 578474046426652721179537 433855534819989540884653)
            ·
              refine ⟨162695825557496077831745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 433855534819989540884653 162695825557496077831745)
              ·
                refine ⟨122021869168122058373809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162695825557496077831745 122021869168122058373809)
                ·
                  refine ⟨91516401876091543780357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122021869168122058373809 91516401876091543780357)
                  ·
                    refine ⟨17159325351767164458817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91516401876091543780357 17159325351767164458817)
                    ·
                      rfl

theorem cell23_100253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_100253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100253 prefixEnd_100253 := by exact prefixLift 100253
  have htrace : WordTrace (prefixWord ++ tailWord_100253) baseStart_100253 baseEnd_100253 := by
    simpa [prefixWord, tailWord_100253, baseEnd_100253] using wordTrace_append hprefix tailTrace_100253
  have hstable : (prefixWord ++ tailWord_100253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100253).length < 2 ^ (prefixWord ++ tailWord_100253).sum := by decide
  have hdescent : baseEnd_100253 < baseStart_100253 := by decide
  rcases family_descends (prefixWord ++ tailWord_100253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100260 : List Nat := [2, 3, 1, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_100260 : Nat := 118140960795 + 100260 * 2 ^ 59
def prefixEnd_100260 : Nat := 4983230072969 + 3 ^ 40 * 100260 * 2
def baseEnd_100260 : Nat := 51481570419882965988919

theorem tailTrace_100260 : CollatzResearch.WordTrace tailWord_100260 prefixEnd_100260 51481570419882965988919 := by
  unfold tailWord_100260
  simp only [CollatzResearch.WordTrace]
  refine ⟨1828391308391308944937117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2437855077855078593249489 1828391308391308944937117)
  ·
    refine ⟨685646740646740854351419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1828391308391308944937117 685646740646740854351419)
    ·
      refine ⟨1028470110970111281527129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 685646740646740854351419 1028470110970111281527129)
      ·
        refine ⟨771352583227583461145347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1028470110970111281527129 771352583227583461145347)
        ·
          refine ⟨1157028874841375191718021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 771352583227583461145347 1157028874841375191718021)
          ·
            refine ⟨216942914032757848447129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1157028874841375191718021 216942914032757848447129)
            ·
              refine ⟨162707185524568386335347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 216942914032757848447129 162707185524568386335347)
              ·
                refine ⟨244060778286852579503021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162707185524568386335347 244060778286852579503021)
                ·
                  refine ⟨91522791857569717313633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244060778286852579503021 91522791857569717313633)
                  ·
                    refine ⟨68642093893177287985225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91522791857569717313633 68642093893177287985225)
                    ·
                      refine ⟨51481570419882965988919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68642093893177287985225 51481570419882965988919)
                      ·
                        rfl

theorem cell23_100260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_100260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100260 prefixEnd_100260 := by exact prefixLift 100260
  have htrace : WordTrace (prefixWord ++ tailWord_100260) baseStart_100260 baseEnd_100260 := by
    simpa [prefixWord, tailWord_100260, baseEnd_100260] using wordTrace_append hprefix tailTrace_100260
  have hstable : (prefixWord ++ tailWord_100260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100260).length < 2 ^ (prefixWord ++ tailWord_100260).sum := by decide
  have hdescent : baseEnd_100260 < baseStart_100260 := by decide
  rcases family_descends (prefixWord ++ tailWord_100260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100273 : List Nat := [1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 4]
def baseStart_100273 : Nat := 118140960795 + 100273 * 2 ^ 59
def prefixEnd_100273 : Nat := 4983230072969 + 3 ^ 40 * 100273 * 2
def baseEnd_100273 : Nat := 51488245668391415126359

theorem tailTrace_100273 : CollatzResearch.WordTrace tailWord_100273 prefixEnd_100273 51488245668391415126359 := by
  unfold tailWord_100273
  simp only [CollatzResearch.WordTrace]
  refine ⟨3657256765735521110097473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2438171177157014073398315 3657256765735521110097473)
  ·
    refine ⟨2742942574301640832573105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3657256765735521110097473 2742942574301640832573105)
    ·
      refine ⟨2057206930726230624429829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2742942574301640832573105 2057206930726230624429829)
      ·
        refine ⟨385726299511168242080593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2057206930726230624429829 385726299511168242080593)
        ·
          refine ⟨289294724633376181560445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 385726299511168242080593 289294724633376181560445)
          ·
            refine ⟨108485521737516068085167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 289294724633376181560445 108485521737516068085167)
            ·
              refine ⟨162728282606274102127751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108485521737516068085167 162728282606274102127751)
              ·
                refine ⟨244092423909411153191627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162728282606274102127751 244092423909411153191627)
                ·
                  refine ⟨366138635864116729787441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244092423909411153191627 366138635864116729787441)
                  ·
                    refine ⟨274603976898087547340581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 366138635864116729787441 274603976898087547340581)
                    ·
                      refine ⟨51488245668391415126359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 274603976898087547340581 51488245668391415126359)
                      ·
                        rfl

theorem cell23_100273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_100273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100273 prefixEnd_100273 := by exact prefixLift 100273
  have htrace : WordTrace (prefixWord ++ tailWord_100273) baseStart_100273 baseEnd_100273 := by
    simpa [prefixWord, tailWord_100273, baseEnd_100273] using wordTrace_append hprefix tailTrace_100273
  have hstable : (prefixWord ++ tailWord_100273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100273).length < 2 ^ (prefixWord ++ tailWord_100273).sum := by decide
  have hdescent : baseEnd_100273 < baseStart_100273 := by decide
  rcases family_descends (prefixWord ++ tailWord_100273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100303 : List Nat := [1, 1, 2, 1, 1, 5, 1, 5, 1, 3, 2]
def baseStart_100303 : Nat := 118140960795 + 100303 * 2 ^ 59
def prefixEnd_100303 : Nat := 4983230072969 + 3 ^ 40 * 100303 * 2
def baseEnd_100303 : Nat := 51503650088026297751221

theorem tailTrace_100303 : CollatzResearch.WordTrace tailWord_100303 prefixEnd_100303 51503650088026297751221 := by
  unfold tailWord_100303
  simp only [CollatzResearch.WordTrace]
  refine ⟨3658350955626836233689563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2438900637084557489126375 3658350955626836233689563)
  ·
    refine ⟨5487526433440254350534345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3658350955626836233689563 5487526433440254350534345)
    ·
      refine ⟨4115644825080190762900759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5487526433440254350534345 4115644825080190762900759)
      ·
        refine ⟨6173467237620286144351139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4115644825080190762900759 6173467237620286144351139)
        ·
          refine ⟨9260200856430429216526709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6173467237620286144351139 9260200856430429216526709)
          ·
            refine ⟨868143830290352739049379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9260200856430429216526709 868143830290352739049379)
            ·
              refine ⟨1302215745435529108574069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 868143830290352739049379 1302215745435529108574069)
              ·
                refine ⟨122082726134580853928819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1302215745435529108574069 122082726134580853928819)
                ·
                  refine ⟨183124089201871280893229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122082726134580853928819 183124089201871280893229)
                  ·
                    refine ⟨68671533450701730334961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183124089201871280893229 68671533450701730334961)
                    ·
                      refine ⟨51503650088026297751221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68671533450701730334961 51503650088026297751221)
                      ·
                        rfl

theorem cell23_100303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 3, 2].length) (baseStart_100303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100303 prefixEnd_100303 := by exact prefixLift 100303
  have htrace : WordTrace (prefixWord ++ tailWord_100303) baseStart_100303 baseEnd_100303 := by
    simpa [prefixWord, tailWord_100303, baseEnd_100303] using wordTrace_append hprefix tailTrace_100303
  have hstable : (prefixWord ++ tailWord_100303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100303).length < 2 ^ (prefixWord ++ tailWord_100303).sum := by decide
  have hdescent : baseEnd_100303 < baseStart_100303 := by decide
  rcases family_descends (prefixWord ++ tailWord_100303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100337 : List Nat := [1, 2, 2, 2, 5, 2, 1, 2, 1, 3, 2]
def baseStart_100337 : Nat := 118140960795 + 100337 * 2 ^ 59
def prefixEnd_100337 : Nat := 4983230072969 + 3 ^ 40 * 100337 * 2
def baseEnd_100337 : Nat := 51521108430279164726065

theorem tailTrace_100337 : CollatzResearch.WordTrace tailWord_100337 prefixEnd_100337 51521108430279164726065 := by
  unfold tailWord_100337
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659591037503660040427265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2439727358335773360284843 3659591037503660040427265)
  ·
    refine ⟨2744693278127745030320449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3659591037503660040427265 2744693278127745030320449)
    ·
      refine ⟨2058519958595808772740337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744693278127745030320449 2058519958595808772740337)
      ·
        refine ⟨1543889968946856579555253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2058519958595808772740337 1543889968946856579555253)
        ·
          refine ⟨144739684588767804333305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1543889968946856579555253 144739684588767804333305)
          ·
            refine ⟨108554763441575853249979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144739684588767804333305 108554763441575853249979)
            ·
              refine ⟨162832145162363779874969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108554763441575853249979 162832145162363779874969)
              ·
                refine ⟨122124108871772834906227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 162832145162363779874969 122124108871772834906227)
                ·
                  refine ⟨183186163307659252359341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122124108871772834906227 183186163307659252359341)
                  ·
                    refine ⟨68694811240372219634753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183186163307659252359341 68694811240372219634753)
                    ·
                      refine ⟨51521108430279164726065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68694811240372219634753 51521108430279164726065)
                      ·
                        rfl

theorem cell23_100337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 3, 2].length) (baseStart_100337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100337 prefixEnd_100337 := by exact prefixLift 100337
  have htrace : WordTrace (prefixWord ++ tailWord_100337) baseStart_100337 baseEnd_100337 := by
    simpa [prefixWord, tailWord_100337, baseEnd_100337] using wordTrace_append hprefix tailTrace_100337
  have hstable : (prefixWord ++ tailWord_100337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100337).length < 2 ^ (prefixWord ++ tailWord_100337).sum := by decide
  have hdescent : baseEnd_100337 < baseStart_100337 := by decide
  rcases family_descends (prefixWord ++ tailWord_100337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100339 : List Nat := [1, 1, 1, 2, 2, 2, 1, 6, 7]
def baseStart_100339 : Nat := 118140960795 + 100339 * 2 ^ 59
def prefixEnd_100339 : Nat := 4983230072969 + 3 ^ 40 * 100339 * 2
def baseEnd_100339 : Nat := 5724681710176461877895

theorem tailTrace_100339 : CollatzResearch.WordTrace tailWord_100339 prefixEnd_100339 5724681710176461877895 := by
  unfold tailWord_100339
  simp only [CollatzResearch.WordTrace]
  refine ⟨3659663983496414382000071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2439775988997609588000047 3659663983496414382000071)
  ·
    refine ⟨5489495975244621573000107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3659663983496414382000071 5489495975244621573000107)
    ·
      refine ⟨8234243962866932359500161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489495975244621573000107 8234243962866932359500161)
      ·
        refine ⟨6175682972150199269625121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8234243962866932359500161 6175682972150199269625121)
        ·
          refine ⟨4631762229112649452218841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175682972150199269625121 4631762229112649452218841)
          ·
            refine ⟨3473821671834487089164131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4631762229112649452218841 3473821671834487089164131)
            ·
              refine ⟨5210732507751730633746197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473821671834487089164131 5210732507751730633746197)
              ·
                refine ⟨244253086300862373456853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5210732507751730633746197 244253086300862373456853)
                ·
                  refine ⟨5724681710176461877895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 244253086300862373456853 5724681710176461877895)
                  ·
                    rfl

theorem cell23_100339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 6, 7].length) (baseStart_100339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100339 prefixEnd_100339 := by exact prefixLift 100339
  have htrace : WordTrace (prefixWord ++ tailWord_100339) baseStart_100339 baseEnd_100339 := by
    simpa [prefixWord, tailWord_100339, baseEnd_100339] using wordTrace_append hprefix tailTrace_100339
  have hstable : (prefixWord ++ tailWord_100339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100339).length < 2 ^ (prefixWord ++ tailWord_100339).sum := by decide
  have hdescent : baseEnd_100339 < baseStart_100339 := by decide
  rcases family_descends (prefixWord ++ tailWord_100339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100350 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_100350 : Nat := 118140960795 + 100350 * 2 ^ 59
def prefixEnd_100350 : Nat := 4983230072969 + 3 ^ 40 * 100350 * 2
def baseEnd_100350 : Nat := 51527783678787613863505

theorem tailTrace_100350 : CollatzResearch.WordTrace tailWord_100350 prefixEnd_100350 51527783678787613863505 := by
  unfold tailWord_100350
  simp only [CollatzResearch.WordTrace]
  refine ⟨457508148307070407581313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2440043457637708840433669 457508148307070407581313)
  ·
    refine ⟨343131111230302805685985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 457508148307070407581313 343131111230302805685985)
    ·
      refine ⟨257348333422727104264489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 343131111230302805685985 257348333422727104264489)
      ·
        refine ⟨193011250067045328198367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 257348333422727104264489 193011250067045328198367)
        ·
          refine ⟨289516875100567992297551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193011250067045328198367 289516875100567992297551)
          ·
            refine ⟨434275312650851988446327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 289516875100567992297551 434275312650851988446327)
            ·
              refine ⟨651412968976277982669491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 434275312650851988446327 651412968976277982669491)
              ·
                refine ⟨977119453464416974004237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 651412968976277982669491 977119453464416974004237)
                ·
                  refine ⟨366419795049156365251589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 977119453464416974004237 366419795049156365251589)
                  ·
                    refine ⟨68703711571716818484673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366419795049156365251589 68703711571716818484673)
                    ·
                      refine ⟨51527783678787613863505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68703711571716818484673 51527783678787613863505)
                      ·
                        rfl

theorem cell23_100350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_100350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100350 prefixEnd_100350 := by exact prefixLift 100350
  have htrace : WordTrace (prefixWord ++ tailWord_100350) baseStart_100350 baseEnd_100350 := by
    simpa [prefixWord, tailWord_100350, baseEnd_100350] using wordTrace_append hprefix tailTrace_100350
  have hstable : (prefixWord ++ tailWord_100350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100350).length < 2 ^ (prefixWord ++ tailWord_100350).sum := by decide
  have hdescent : baseEnd_100350 < baseStart_100350 := by decide
  rcases family_descends (prefixWord ++ tailWord_100350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100369 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 5, 7]
def baseStart_100369 : Nat := 118140960795 + 100369 * 2 ^ 59
def prefixEnd_100369 : Nat := 4983230072969 + 3 ^ 40 * 100369 * 2
def baseEnd_100369 : Nat := 17179179937074346508639

theorem tailTrace_100369 : CollatzResearch.WordTrace tailWord_100369 prefixEnd_100369 17179179937074346508639 := by
  unfold tailWord_100369
  simp only [CollatzResearch.WordTrace]
  refine ⟨3660758173387729505592161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2440505448925153003728107 3660758173387729505592161)
  ·
    refine ⟨2745568630040797129194121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3660758173387729505592161 2745568630040797129194121)
    ·
      refine ⟨2059176472530597846895591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2745568630040797129194121 2059176472530597846895591)
      ·
        refine ⟨3088764708795896770343387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2059176472530597846895591 3088764708795896770343387)
        ·
          refine ⟨4633147063193845155515081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3088764708795896770343387 4633147063193845155515081)
          ·
            refine ⟨3474860297395383866636311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4633147063193845155515081 3474860297395383866636311)
            ·
              refine ⟨5212290446093075799954467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3474860297395383866636311 5212290446093075799954467)
              ·
                refine ⟨7818435669139613699931701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212290446093075799954467 7818435669139613699931701)
                ·
                  refine ⟨732978343981838784368597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7818435669139613699931701 732978343981838784368597)
                  ·
                    refine ⟨17179179937074346508639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 732978343981838784368597 17179179937074346508639)
                    ·
                      rfl

theorem cell23_100369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_100369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100369 prefixEnd_100369 := by exact prefixLift 100369
  have htrace : WordTrace (prefixWord ++ tailWord_100369) baseStart_100369 baseEnd_100369 := by
    simpa [prefixWord, tailWord_100369, baseEnd_100369] using wordTrace_append hprefix tailTrace_100369
  have hstable : (prefixWord ++ tailWord_100369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100369).length < 2 ^ (prefixWord ++ tailWord_100369).sum := by decide
  have hdescent : baseEnd_100369 < baseStart_100369 := by decide
  rcases family_descends (prefixWord ++ tailWord_100369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100379 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7]
def baseStart_100379 : Nat := 118140960795 + 100379 * 2 ^ 59
def prefixEnd_100379 : Nat := 4983230072969 + 3 ^ 40 * 100379 * 2
def baseEnd_100379 : Nat := 51542674617768000400871

theorem tailTrace_100379 : CollatzResearch.WordTrace tailWord_100379 prefixEnd_100379 51542674617768000400871 := by
  unfold tailWord_100379
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661122903351501213456191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2440748602234334142304127 3661122903351501213456191)
  ·
    refine ⟨5491684355027251820184287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661122903351501213456191 5491684355027251820184287)
    ·
      refine ⟨8237526532540877730276431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5491684355027251820184287 8237526532540877730276431)
      ·
        refine ⟨12356289798811316595414647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8237526532540877730276431 12356289798811316595414647)
        ·
          refine ⟨18534434698216974893121971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12356289798811316595414647 18534434698216974893121971)
          ·
            refine ⟨27801652047325462339682957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18534434698216974893121971 27801652047325462339682957)
            ·
              refine ⟨10425619517747048377381109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27801652047325462339682957 10425619517747048377381109)
              ·
                refine ⟨977401829788785785379479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10425619517747048377381109 977401829788785785379479)
                ·
                  refine ⟨1466102744683178678069219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 977401829788785785379479 1466102744683178678069219)
                  ·
                    refine ⟨2199154117024768017103829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1466102744683178678069219 2199154117024768017103829)
                    ·
                      refine ⟨51542674617768000400871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2199154117024768017103829 51542674617768000400871)
                      ·
                        rfl

theorem cell23_100379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 1, 7].length) (baseStart_100379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100379 prefixEnd_100379 := by exact prefixLift 100379
  have htrace : WordTrace (prefixWord ++ tailWord_100379) baseStart_100379 baseEnd_100379 := by
    simpa [prefixWord, tailWord_100379, baseEnd_100379] using wordTrace_append hprefix tailTrace_100379
  have hstable : (prefixWord ++ tailWord_100379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100379).length < 2 ^ (prefixWord ++ tailWord_100379).sum := by decide
  have hdescent : baseEnd_100379 < baseStart_100379 := by decide
  rcases family_descends (prefixWord ++ tailWord_100379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100386 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_100386 : Nat := 118140960795 + 100386 * 2 ^ 59
def prefixEnd_100386 : Nat := 4983230072969 + 3 ^ 40 * 100386 * 2
def baseEnd_100386 : Nat := 17182089660783157671113

theorem tailTrace_100386 : CollatzResearch.WordTrace tailWord_100386 prefixEnd_100386 17182089660783157671113 := by
  unfold tailWord_100386
  simp only [CollatzResearch.WordTrace]
  refine ⟨915344553581535352240253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2440918809550760939307341 915344553581535352240253)
  ·
    refine ⟨343254207593075757090095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 915344553581535352240253 343254207593075757090095)
    ·
      refine ⟨514881311389613635635143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343254207593075757090095 514881311389613635635143)
      ·
        refine ⟨772321967084420453452715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 514881311389613635635143 772321967084420453452715)
        ·
          refine ⟨1158482950626630680179073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772321967084420453452715 1158482950626630680179073)
          ·
            refine ⟨868862212969973010134305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1158482950626630680179073 868862212969973010134305)
            ·
              refine ⟨651646659727479757600729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 868862212969973010134305 651646659727479757600729)
              ·
                refine ⟨488734994795609818200547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 651646659727479757600729 488734994795609818200547)
                ·
                  refine ⟨733102492193414727300821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 488734994795609818200547 733102492193414727300821)
                  ·
                    refine ⟨17182089660783157671113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 733102492193414727300821 17182089660783157671113)
                    ·
                      rfl

theorem cell23_100386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_100386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100386 prefixEnd_100386 := by exact prefixLift 100386
  have htrace : WordTrace (prefixWord ++ tailWord_100386) baseStart_100386 baseEnd_100386 := by
    simpa [prefixWord, tailWord_100386, baseEnd_100386] using wordTrace_append hprefix tailTrace_100386
  have hstable : (prefixWord ++ tailWord_100386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100386).length < 2 ^ (prefixWord ++ tailWord_100386).sum := by decide
  have hdescent : baseEnd_100386 < baseStart_100386 := by decide
  rcases family_descends (prefixWord ++ tailWord_100386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100399 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 1, 10]
def baseStart_100399 : Nat := 118140960795 + 100399 * 2 ^ 59
def prefixEnd_100399 : Nat := 4983230072969 + 3 ^ 40 * 100399 * 2
def baseEnd_100399 : Nat := 17184314743619307383593

theorem tailTrace_100399 : CollatzResearch.WordTrace tailWord_100399 prefixEnd_100399 17184314743619307383593 := by
  unfold tailWord_100399
  simp only [CollatzResearch.WordTrace]
  refine ⟨3661852363279044629184251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2441234908852696419456167 3661852363279044629184251)
  ·
    refine ⟨5492778544918566943776377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3661852363279044629184251 5492778544918566943776377)
    ·
      refine ⟨4119583908688925207832283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5492778544918566943776377 4119583908688925207832283)
      ·
        refine ⟨6179375863033387811748425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4119583908688925207832283 6179375863033387811748425)
        ·
          refine ⟨4634531897275040858811319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6179375863033387811748425 4634531897275040858811319)
          ·
            refine ⟨6951797845912561288216979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4634531897275040858811319 6951797845912561288216979)
            ·
              refine ⟨10427696768868841932325469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6951797845912561288216979 10427696768868841932325469)
              ·
                refine ⟨3910386288325815724622051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10427696768868841932325469 3910386288325815724622051)
                ·
                  refine ⟨5865579432488723586933077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3910386288325815724622051 5865579432488723586933077)
                  ·
                    refine ⟨17184314743619307383593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 5865579432488723586933077 17184314743619307383593)
                    ·
                      rfl

theorem cell23_100399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 10].length) (baseStart_100399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100399 prefixEnd_100399 := by exact prefixLift 100399
  have htrace : WordTrace (prefixWord ++ tailWord_100399) baseStart_100399 baseEnd_100399 := by
    simpa [prefixWord, tailWord_100399, baseEnd_100399] using wordTrace_append hprefix tailTrace_100399
  have hstable : (prefixWord ++ tailWord_100399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100399).length < 2 ^ (prefixWord ++ tailWord_100399).sum := by decide
  have hdescent : baseEnd_100399 < baseStart_100399 := by decide
  rcases family_descends (prefixWord ++ tailWord_100399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100423 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 4, 4, 2]
def baseStart_100423 : Nat := 118140960795 + 100423 * 2 ^ 59
def prefixEnd_100423 : Nat := 4983230072969 + 3 ^ 40 * 100423 * 2
def baseEnd_100423 : Nat := 51565267766565828250669

theorem tailTrace_100423 : CollatzResearch.WordTrace tailWord_100423 prefixEnd_100423 51565267766565828250669 := by
  unfold tailWord_100423
  simp only [CollatzResearch.WordTrace]
  refine ⟨3662727715192096728057923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2441818476794731152038615 3662727715192096728057923)
  ·
    refine ⟨5494091572788145092086885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3662727715192096728057923 5494091572788145092086885)
    ·
      refine ⟨1030142169897777204766291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5494091572788145092086885 1030142169897777204766291)
      ·
        refine ⟨1545213254846665807149437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1030142169897777204766291 1545213254846665807149437)
        ·
          refine ⟨579454970567499677681039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1545213254846665807149437 579454970567499677681039)
          ·
            refine ⟨869182455851249516521559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579454970567499677681039 869182455851249516521559)
            ·
              refine ⟨1303773683776874274782339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869182455851249516521559 1303773683776874274782339)
              ·
                refine ⟨1955660525665311412173509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1303773683776874274782339 1955660525665311412173509)
                ·
                  refine ⟨366686348562245889782533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1955660525665311412173509 366686348562245889782533)
                  ·
                    refine ⟨68753690355421104334225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 366686348562245889782533 68753690355421104334225)
                    ·
                      refine ⟨51565267766565828250669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68753690355421104334225 51565267766565828250669)
                      ·
                        rfl

theorem cell23_100423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_100423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100423 prefixEnd_100423 := by exact prefixLift 100423
  have htrace : WordTrace (prefixWord ++ tailWord_100423) baseStart_100423 baseEnd_100423 := by
    simpa [prefixWord, tailWord_100423, baseEnd_100423] using wordTrace_append hprefix tailTrace_100423
  have hstable : (prefixWord ++ tailWord_100423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100423).length < 2 ^ (prefixWord ++ tailWord_100423).sum := by decide
  have hdescent : baseEnd_100423 < baseStart_100423 := by decide
  rcases family_descends (prefixWord ++ tailWord_100423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100436 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_100436 : Nat := 118140960795 + 100436 * 2 ^ 59
def prefixEnd_100436 : Nat := 4983230072969 + 3 ^ 40 * 100436 * 2
def baseEnd_100436 : Nat := 51571943015074277388109

theorem tailTrace_100436 : CollatzResearch.WordTrace tailWord_100436 prefixEnd_100436 51571943015074277388109 := by
  unfold tailWord_100436
  simp only [CollatzResearch.WordTrace]
  refine ⟨1831600932072499974140581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2442134576096666632187441 1831600932072499974140581)
  ·
    refine ⟨343425174763593745151359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1831600932072499974140581 343425174763593745151359)
    ·
      refine ⟨515137762145390617727039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 343425174763593745151359 515137762145390617727039)
      ·
        refine ⟨772706643218085926590559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515137762145390617727039 772706643218085926590559)
        ·
          refine ⟨1159059964827128889885839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 772706643218085926590559 1159059964827128889885839)
          ·
            refine ⟨1738589947240693334828759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159059964827128889885839 1738589947240693334828759)
            ·
              refine ⟨2607884920861040002243139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1738589947240693334828759 2607884920861040002243139)
              ·
                refine ⟨3911827381291560003364709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2607884920861040002243139 3911827381291560003364709)
                ·
                  refine ⟨733467633992167500630883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3911827381291560003364709 733467633992167500630883)
                  ·
                    refine ⟨1100201450988251250946325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 733467633992167500630883 1100201450988251250946325)
                    ·
                      refine ⟨51571943015074277388109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1100201450988251250946325 51571943015074277388109)
                      ·
                        rfl

theorem cell23_100436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_100436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100436 prefixEnd_100436 := by exact prefixLift 100436
  have htrace : WordTrace (prefixWord ++ tailWord_100436) baseStart_100436 baseEnd_100436 := by
    simpa [prefixWord, tailWord_100436, baseEnd_100436] using wordTrace_append hprefix tailTrace_100436
  have hstable : (prefixWord ++ tailWord_100436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100436).length < 2 ^ (prefixWord ++ tailWord_100436).sum := by decide
  have hdescent : baseEnd_100436 < baseStart_100436 := by decide
  rcases family_descends (prefixWord ++ tailWord_100436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100578 : List Nat := [3, 3, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_100578 : Nat := 118140960795 + 100578 * 2 ^ 59
def prefixEnd_100578 : Nat := 4983230072969 + 3 ^ 40 * 100578 * 2
def baseEnd_100578 : Nat := 17214952422670907270819

theorem tailTrace_100578 : CollatzResearch.WordTrace tailWord_100578 prefixEnd_100578 17214952422670907270819 := by
  unfold tailWord_100578
  simp only [CollatzResearch.WordTrace]
  refine ⟨917095257407639549987597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2445587353087038799966925 917095257407639549987597)
  ·
    refine ⟨343910721527864831245349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 917095257407639549987597 343910721527864831245349)
    ·
      refine ⟨64483260286474655858503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 343910721527864831245349 64483260286474655858503)
      ·
        refine ⟨96724890429711983787755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64483260286474655858503 96724890429711983787755)
        ·
          refine ⟨145087335644567975681633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96724890429711983787755 145087335644567975681633)
          ·
            refine ⟨108815501733425981761225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145087335644567975681633 108815501733425981761225)
            ·
              refine ⟨81611626300069486320919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108815501733425981761225 81611626300069486320919)
              ·
                refine ⟨122417439450104229481379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81611626300069486320919 122417439450104229481379)
                ·
                  refine ⟨183626159175156344222069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122417439450104229481379 183626159175156344222069)
                  ·
                    refine ⟨17214952422670907270819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 183626159175156344222069 17214952422670907270819)
                    ·
                      rfl

theorem cell23_100578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_100578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100578 prefixEnd_100578 := by exact prefixLift 100578
  have htrace : WordTrace (prefixWord ++ tailWord_100578) baseStart_100578 baseEnd_100578 := by
    simpa [prefixWord, tailWord_100578, baseEnd_100578] using wordTrace_append hprefix tailTrace_100578
  have hstable : (prefixWord ++ tailWord_100578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100578).length < 2 ^ (prefixWord ++ tailWord_100578).sum := by decide
  have hdescent : baseEnd_100578 < baseStart_100578 := by decide
  rcases family_descends (prefixWord ++ tailWord_100578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100580 : List Nat := [2, 3, 1, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_100580 : Nat := 118140960795 + 100580 * 2 ^ 59
def prefixEnd_100580 : Nat := 4983230072969 + 3 ^ 40 * 100580 * 2
def baseEnd_100580 : Nat := 51645884229321713987447

theorem tailTrace_100580 : CollatzResearch.WordTrace tailWord_100580 prefixEnd_100580 51645884229321713987447 := by
  unfold tailWord_100580
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834226987811656270761597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2445635983748875027682129 1834226987811656270761597)
  ·
    refine ⟨687835120429371101535599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1834226987811656270761597 687835120429371101535599)
    ·
      refine ⟨1031752680644056652303399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 687835120429371101535599 1031752680644056652303399)
      ·
        refine ⟨1547629020966084978455099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031752680644056652303399 1547629020966084978455099)
        ·
          refine ⟨2321443531449127467682649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1547629020966084978455099 2321443531449127467682649)
          ·
            refine ⟨1741082648586845600761987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2321443531449127467682649 1741082648586845600761987)
            ·
              refine ⟨2611623972880268401142981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1741082648586845600761987 2611623972880268401142981)
              ·
                refine ⟨489679494915050325214309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2611623972880268401142981 489679494915050325214309)
                ·
                  refine ⟨91814905296571935977683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 489679494915050325214309 91814905296571935977683)
                  ·
                    refine ⟨137722357944857903966525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 91814905296571935977683 137722357944857903966525)
                    ·
                      refine ⟨51645884229321713987447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 137722357944857903966525 51645884229321713987447)
                      ·
                        rfl

theorem cell23_100580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_100580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100580 prefixEnd_100580 := by exact prefixLift 100580
  have htrace : WordTrace (prefixWord ++ tailWord_100580) baseStart_100580 baseEnd_100580 := by
    simpa [prefixWord, tailWord_100580, baseEnd_100580] using wordTrace_append hprefix tailTrace_100580
  have hstable : (prefixWord ++ tailWord_100580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100580).length < 2 ^ (prefixWord ++ tailWord_100580).sum := by decide
  have hdescent : baseEnd_100580 < baseStart_100580 := by decide
  rcases family_descends (prefixWord ++ tailWord_100580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100581 : List Nat := [1, 3, 1, 4, 2, 2, 2, 3, 1, 2, 2]
def baseStart_100581 : Nat := 118140960795 + 100581 * 2 ^ 59
def prefixEnd_100581 : Nat := 4983230072969 + 3 ^ 40 * 100581 * 2
def baseEnd_100581 : Nat := 51646397709976210074943

theorem tailTrace_100581 : CollatzResearch.WordTrace tailWord_100581 prefixEnd_100581 51646397709976210074943 := by
  unfold tailWord_100581
  simp only [CollatzResearch.WordTrace]
  refine ⟨3668490448619689712309597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2445660299079793141539731 3668490448619689712309597)
  ·
    refine ⟨1375683918232383642116099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3668490448619689712309597 1375683918232383642116099)
    ·
      refine ⟨2063525877348575463174149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1375683918232383642116099 2063525877348575463174149)
      ·
        refine ⟨386911102002857899345153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2063525877348575463174149 386911102002857899345153)
        ·
          refine ⟨290183326502143424508865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 386911102002857899345153 290183326502143424508865)
          ·
            refine ⟨217637494876607568381649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290183326502143424508865 217637494876607568381649)
            ·
              refine ⟨163228121157455676286237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 217637494876607568381649 163228121157455676286237)
              ·
                refine ⟨61210545434045878607339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163228121157455676286237 61210545434045878607339)
                ·
                  refine ⟨91815818151068817911009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61210545434045878607339 91815818151068817911009)
                  ·
                    refine ⟨68861863613301613433257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91815818151068817911009 68861863613301613433257)
                    ·
                      refine ⟨51646397709976210074943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 68861863613301613433257 51646397709976210074943)
                      ·
                        rfl

theorem cell23_100581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_100581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100581 prefixEnd_100581 := by exact prefixLift 100581
  have htrace : WordTrace (prefixWord ++ tailWord_100581) baseStart_100581 baseEnd_100581 := by
    simpa [prefixWord, tailWord_100581, baseEnd_100581] using wordTrace_append hprefix tailTrace_100581
  have hstable : (prefixWord ++ tailWord_100581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100581).length < 2 ^ (prefixWord ++ tailWord_100581).sum := by decide
  have hdescent : baseEnd_100581 < baseStart_100581 := by decide
  rcases family_descends (prefixWord ++ tailWord_100581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100584 : List Nat := [2, 1, 4, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_100584 : Nat := 118140960795 + 100584 * 2 ^ 59
def prefixEnd_100584 : Nat := 4983230072969 + 3 ^ 40 * 100584 * 2
def baseEnd_100584 : Nat := 51647938151939698337429

theorem tailTrace_100584 : CollatzResearch.WordTrace tailWord_100584 prefixEnd_100584 51647938151939698337429 := by
  unfold tailWord_100584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834299933804410612334403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2445733245072547483112537 1834299933804410612334403)
  ·
    refine ⟨2751449900706615918501605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834299933804410612334403 2751449900706615918501605)
    ·
      refine ⟨515896856382490484719051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2751449900706615918501605 515896856382490484719051)
      ·
        refine ⟨773845284573735727078577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515896856382490484719051 773845284573735727078577)
        ·
          refine ⟨580383963430301795308933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773845284573735727078577 580383963430301795308933)
          ·
            refine ⟨108821993143181586620425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 580383963430301795308933 108821993143181586620425)
            ·
              refine ⟨81616494857386189965319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108821993143181586620425 81616494857386189965319)
              ·
                refine ⟨122424742286079284947979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81616494857386189965319 122424742286079284947979)
                ·
                  refine ⟨183637113429118927421969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122424742286079284947979 183637113429118927421969)
                  ·
                    refine ⟨137727835071839195566477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183637113429118927421969 137727835071839195566477)
                    ·
                      refine ⟨51647938151939698337429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 137727835071839195566477 51647938151939698337429)
                      ·
                        rfl

theorem cell23_100584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_100584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100584 prefixEnd_100584 := by exact prefixLift 100584
  have htrace : WordTrace (prefixWord ++ tailWord_100584) baseStart_100584 baseEnd_100584 := by
    simpa [prefixWord, tailWord_100584, baseEnd_100584] using wordTrace_append hprefix tailTrace_100584
  have hstable : (prefixWord ++ tailWord_100584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100584).length < 2 ^ (prefixWord ++ tailWord_100584).sum := by decide
  have hdescent : baseEnd_100584 < baseStart_100584 := by decide
  rcases family_descends (prefixWord ++ tailWord_100584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100623 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 3]
def baseStart_100623 : Nat := 118140960795 + 100623 * 2 ^ 59
def prefixEnd_100623 : Nat := 4983230072969 + 3 ^ 40 * 100623 * 2
def baseEnd_100623 : Nat := 51667963897465045749749

theorem tailTrace_100623 : CollatzResearch.WordTrace tailWord_100623 prefixEnd_100623 51667963897465045749749 := by
  unfold tailWord_100623
  simp only [CollatzResearch.WordTrace]
  refine ⟨3670022314467530885338523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2446681542978353923559015 3670022314467530885338523)
  ·
    refine ⟨5505033471701296328007785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3670022314467530885338523 5505033471701296328007785)
    ·
      refine ⟨4128775103775972246005839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5505033471701296328007785 4128775103775972246005839)
      ·
        refine ⟨6193162655663958369008759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4128775103775972246005839 6193162655663958369008759)
        ·
          refine ⟨9289743983495937553513139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6193162655663958369008759 9289743983495937553513139)
          ·
            refine ⟨13934615975243906330269709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9289743983495937553513139 13934615975243906330269709)
            ·
              refine ⟨5225480990716464873851141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13934615975243906330269709 5225480990716464873851141)
              ·
                refine ⟨979777685759337163847089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5225480990716464873851141 979777685759337163847089)
                ·
                  refine ⟨734833264319502872885317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 979777685759337163847089 734833264319502872885317)
                  ·
                    refine ⟨137781237059906788665997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 734833264319502872885317 137781237059906788665997)
                    ·
                      refine ⟨51667963897465045749749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 137781237059906788665997 51667963897465045749749)
                      ·
                        rfl

theorem cell23_100623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 3].length) (baseStart_100623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100623 prefixEnd_100623 := by exact prefixLift 100623
  have htrace : WordTrace (prefixWord ++ tailWord_100623) baseStart_100623 baseEnd_100623 := by
    simpa [prefixWord, tailWord_100623, baseEnd_100623] using wordTrace_append hprefix tailTrace_100623
  have hstable : (prefixWord ++ tailWord_100623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100623).length < 2 ^ (prefixWord ++ tailWord_100623).sum := by decide
  have hdescent : baseEnd_100623 < baseStart_100623 := by decide
  rcases family_descends (prefixWord ++ tailWord_100623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100640 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_100640 : Nat := 118140960795 + 100640 * 2 ^ 59
def prefixEnd_100640 : Nat := 4983230072969 + 3 ^ 40 * 100640 * 2
def baseEnd_100640 : Nat := 51676693068591479237171

theorem tailTrace_100640 : CollatzResearch.WordTrace tailWord_100640 prefixEnd_100640 51676693068591479237171 := by
  unfold tailWord_100640
  simp only [CollatzResearch.WordTrace]
  refine ⟨1835321177702971394353687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2447094903603961859138249 1835321177702971394353687)
  ·
    refine ⟨2752981766554457091530531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1835321177702971394353687 2752981766554457091530531)
    ·
      refine ⟨4129472649831685637295797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752981766554457091530531 4129472649831685637295797)
      ·
        refine ⟨387138060921720528496481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4129472649831685637295797 387138060921720528496481)
        ·
          refine ⟨290353545691290396372361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387138060921720528496481 290353545691290396372361)
          ·
            refine ⟨217765159268467797279271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290353545691290396372361 217765159268467797279271)
            ·
              refine ⟨326647738902701695918907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 217765159268467797279271 326647738902701695918907)
              ·
                refine ⟨489971608354052543878361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 326647738902701695918907 489971608354052543878361)
                ·
                  refine ⟨367478706265539407908771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 489971608354052543878361 367478706265539407908771)
                  ·
                    refine ⟨551218059398309111863157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 367478706265539407908771 551218059398309111863157)
                    ·
                      refine ⟨51676693068591479237171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 551218059398309111863157 51676693068591479237171)
                      ·
                        rfl

theorem cell23_100640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_100640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100640 prefixEnd_100640 := by exact prefixLift 100640
  have htrace : WordTrace (prefixWord ++ tailWord_100640) baseStart_100640 baseEnd_100640 := by
    simpa [prefixWord, tailWord_100640, baseEnd_100640] using wordTrace_append hprefix tailTrace_100640
  have hstable : (prefixWord ++ tailWord_100640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100640).length < 2 ^ (prefixWord ++ tailWord_100640).sum := by decide
  have hdescent : baseEnd_100640 < baseStart_100640 := by decide
  rcases family_descends (prefixWord ++ tailWord_100640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100690 : List Nat := [3, 2, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_100690 : Nat := 118140960795 + 100690 * 2 ^ 59
def prefixEnd_100690 : Nat := 4983230072969 + 3 ^ 40 * 100690 * 2
def baseEnd_100690 : Nat := 17234122367105427870647

theorem tailTrace_100690 : CollatzResearch.WordTrace tailWord_100690 prefixEnd_100690 17234122367105427870647 := by
  unfold tailWord_100690
  simp only [CollatzResearch.WordTrace]
  refine ⟨918116501306200332006881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2448310670149867552018349 918116501306200332006881)
  ·
    refine ⟨688587375979650249005161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 918116501306200332006881 688587375979650249005161)
    ·
      refine ⟨516440531984737686753871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 688587375979650249005161 516440531984737686753871)
      ·
        refine ⟨774660797977106530130807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516440531984737686753871 774660797977106530130807)
        ·
          refine ⟨1161991196965659795196211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774660797977106530130807 1161991196965659795196211)
          ·
            refine ⟨1742986795448489692794317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161991196965659795196211 1742986795448489692794317)
            ·
              refine ⟨653620048293183634797869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1742986795448489692794317 653620048293183634797869)
              ·
                refine ⟨245107518109943863049201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 653620048293183634797869 245107518109943863049201)
                ·
                  refine ⟨183830638582457897286901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245107518109943863049201 183830638582457897286901)
                  ·
                    refine ⟨17234122367105427870647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 183830638582457897286901 17234122367105427870647)
                    ·
                      rfl

theorem cell23_100690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_100690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100690 prefixEnd_100690 := by exact prefixLift 100690
  have htrace : WordTrace (prefixWord ++ tailWord_100690) baseStart_100690 baseEnd_100690 := by
    simpa [prefixWord, tailWord_100690, baseEnd_100690] using wordTrace_append hprefix tailTrace_100690
  have hstable : (prefixWord ++ tailWord_100690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100690).length < 2 ^ (prefixWord ++ tailWord_100690).sum := by decide
  have hdescent : baseEnd_100690 < baseStart_100690 := by decide
  rcases family_descends (prefixWord ++ tailWord_100690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100713 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_100713 : Nat := 118140960795 + 100713 * 2 ^ 59
def prefixEnd_100713 : Nat := 4983230072969 + 3 ^ 40 * 100713 * 2
def baseEnd_100713 : Nat := 51714177156369693624335

theorem tailTrace_100713 : CollatzResearch.WordTrace tailWord_100713 prefixEnd_100713 51714177156369693624335 := by
  unfold tailWord_100713
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673304884141476256114793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2448869922760984170743195 3673304884141476256114793)
  ·
    refine ⟨2754978663106107192086095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3673304884141476256114793 2754978663106107192086095)
    ·
      refine ⟨4132467994659160788129143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2754978663106107192086095 4132467994659160788129143)
      ·
        refine ⟨6198701991988741182193715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4132467994659160788129143 6198701991988741182193715)
        ·
          refine ⟨9298052987983111773290573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6198701991988741182193715 9298052987983111773290573)
          ·
            refine ⟨3486769870493666914983965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9298052987983111773290573 3486769870493666914983965)
            ·
              refine ⟨1307538701435125093118987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3486769870493666914983965 1307538701435125093118987)
              ·
                refine ⟨1961308052152687639678481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1307538701435125093118987 1961308052152687639678481)
                ·
                  refine ⟨1470981039114515729758861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1961308052152687639678481 1470981039114515729758861)
                  ·
                    refine ⟨551617889667943398659573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1470981039114515729758861 551617889667943398659573)
                    ·
                      refine ⟨51714177156369693624335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 551617889667943398659573 51714177156369693624335)
                      ·
                        rfl

theorem cell23_100713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_100713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100713 prefixEnd_100713 := by exact prefixLift 100713
  have htrace : WordTrace (prefixWord ++ tailWord_100713) baseStart_100713 baseEnd_100713 := by
    simpa [prefixWord, tailWord_100713, baseEnd_100713] using wordTrace_append hprefix tailTrace_100713
  have hstable : (prefixWord ++ tailWord_100713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100713).length < 2 ^ (prefixWord ++ tailWord_100713).sum := by decide
  have hdescent : baseEnd_100713 < baseStart_100713 := by decide
  rcases family_descends (prefixWord ++ tailWord_100713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100723 : List Nat := [1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6]
def baseStart_100723 : Nat := 118140960795 + 100723 * 2 ^ 59
def prefixEnd_100723 : Nat := 4983230072969 + 3 ^ 40 * 100723 * 2
def baseEnd_100723 : Nat := 51719311962914654499289

theorem tailTrace_100723 : CollatzResearch.WordTrace tailWord_100723 prefixEnd_100723 51719311962914654499289 := by
  unfold tailWord_100723
  simp only [CollatzResearch.WordTrace]
  refine ⟨3673669614105247963978823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2449113076070165309319215 3673669614105247963978823)
  ·
    refine ⟨5510504421157871945968235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3673669614105247963978823 5510504421157871945968235)
    ·
      refine ⟨8265756631736807918952353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5510504421157871945968235 8265756631736807918952353)
      ·
        refine ⟨6199317473802605939214265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8265756631736807918952353 6199317473802605939214265)
        ·
          refine ⟨4649488105351954454410699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6199317473802605939214265 4649488105351954454410699)
          ·
            refine ⟨6974232158027931681616049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4649488105351954454410699 6974232158027931681616049)
            ·
              refine ⟨5230674118520948761212037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6974232158027931681616049 5230674118520948761212037)
              ·
                refine ⟨980751397222677892727257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5230674118520948761212037 980751397222677892727257)
                ·
                  refine ⟨735563547917008419545443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 980751397222677892727257 735563547917008419545443)
                  ·
                    refine ⟨1103345321875512629318165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 735563547917008419545443 1103345321875512629318165)
                    ·
                      refine ⟨51719311962914654499289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1103345321875512629318165 51719311962914654499289)
                      ·
                        rfl

theorem cell23_100723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_100723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100723 prefixEnd_100723 := by exact prefixLift 100723
  have htrace : WordTrace (prefixWord ++ tailWord_100723) baseStart_100723 baseEnd_100723 := by
    simpa [prefixWord, tailWord_100723, baseEnd_100723] using wordTrace_append hprefix tailTrace_100723
  have hstable : (prefixWord ++ tailWord_100723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100723).length < 2 ^ (prefixWord ++ tailWord_100723).sum := by decide
  have hdescent : baseEnd_100723 < baseStart_100723 := by decide
  rcases family_descends (prefixWord ++ tailWord_100723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100737 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 5, 4]
def baseStart_100737 : Nat := 118140960795 + 100737 * 2 ^ 59
def prefixEnd_100737 : Nat := 4983230072969 + 3 ^ 40 * 100737 * 2
def baseEnd_100737 : Nat := 17242166897359199908075

theorem tailTrace_100737 : CollatzResearch.WordTrace tailWord_100737 prefixEnd_100737 17242166897359199908075 := by
  unfold tailWord_100737
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674180236054528354988465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2449453490703018903325643 3674180236054528354988465)
  ·
    refine ⟨2755635177040896266241349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3674180236054528354988465 2755635177040896266241349)
    ·
      refine ⟨516681595695168049920253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2755635177040896266241349 516681595695168049920253)
      ·
        refine ⟨193755598385688018720095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516681595695168049920253 193755598385688018720095)
        ·
          refine ⟨290633397578532028080143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193755598385688018720095 290633397578532028080143)
          ·
            refine ⟨435950096367798042120215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290633397578532028080143 435950096367798042120215)
            ·
              refine ⟨653925144551697063180323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435950096367798042120215 653925144551697063180323)
              ·
                refine ⟨980887716827545594770485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 653925144551697063180323 980887716827545594770485)
                ·
                  refine ⟨91958223452582399509733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 980887716827545594770485 91958223452582399509733)
                  ·
                    refine ⟨17242166897359199908075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 91958223452582399509733 17242166897359199908075)
                    ·
                      rfl

theorem cell23_100737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_100737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100737 prefixEnd_100737 := by exact prefixLift 100737
  have htrace : WordTrace (prefixWord ++ tailWord_100737) baseStart_100737 baseEnd_100737 := by
    simpa [prefixWord, tailWord_100737, baseEnd_100737] using wordTrace_append hprefix tailTrace_100737
  have hstable : (prefixWord ++ tailWord_100737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100737).length < 2 ^ (prefixWord ++ tailWord_100737).sum := by decide
  have hdescent : baseEnd_100737 < baseStart_100737 := by decide
  rcases family_descends (prefixWord ++ tailWord_100737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100747 : List Nat := [1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 3]
def baseStart_100747 : Nat := 118140960795 + 100747 * 2 ^ 59
def prefixEnd_100747 : Nat := 4983230072969 + 3 ^ 40 * 100747 * 2
def baseEnd_100747 : Nat := 51731635498622560599179

theorem tailTrace_100747 : CollatzResearch.WordTrace tailWord_100747 prefixEnd_100747 51731635498622560599179 := by
  unfold tailWord_100747
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674544966018300062852495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2449696644012200041901663 3674544966018300062852495)
  ·
    refine ⟨5511817449027450094278743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3674544966018300062852495 5511817449027450094278743)
    ·
      refine ⟨8267726173541175141418115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5511817449027450094278743 8267726173541175141418115)
      ·
        refine ⟨12401589260311762712127173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8267726173541175141418115 12401589260311762712127173)
        ·
          refine ⟨2325297986308455508523845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12401589260311762712127173 2325297986308455508523845)
          ·
            refine ⟨435993372432835407848221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2325297986308455508523845 435993372432835407848221)
            ·
              refine ⟨163497514662313277943083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435993372432835407848221 163497514662313277943083)
              ·
                refine ⟨245246271993469916914625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163497514662313277943083 245246271993469916914625)
                ·
                  refine ⟨183934703995102437685969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245246271993469916914625 183934703995102437685969)
                  ·
                    refine ⟨137951027996326828264477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 183934703995102437685969 137951027996326828264477)
                    ·
                      refine ⟨51731635498622560599179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 137951027996326828264477 51731635498622560599179)
                      ·
                        rfl

theorem cell23_100747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 2, 3].length) (baseStart_100747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100747 prefixEnd_100747 := by exact prefixLift 100747
  have htrace : WordTrace (prefixWord ++ tailWord_100747) baseStart_100747 baseEnd_100747 := by
    simpa [prefixWord, tailWord_100747, baseEnd_100747] using wordTrace_append hprefix tailTrace_100747
  have hstable : (prefixWord ++ tailWord_100747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100747).length < 2 ^ (prefixWord ++ tailWord_100747).sum := by decide
  have hdescent : baseEnd_100747 < baseStart_100747 := by decide
  rcases family_descends (prefixWord ++ tailWord_100747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100753 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_100753 : Nat := 118140960795 + 100753 * 2 ^ 59
def prefixEnd_100753 : Nat := 4983230072969 + 3 ^ 40 * 100753 * 2
def baseEnd_100753 : Nat := 51734716382549537124151

theorem tailTrace_100753 : CollatzResearch.WordTrace tailWord_100753 prefixEnd_100753 51734716382549537124151 := by
  unfold tailWord_100753
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674763803996563087570913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2449842535997708725047275 3674763803996563087570913)
  ·
    refine ⟨2756072852997422315678185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3674763803996563087570913 2756072852997422315678185)
    ·
      refine ⟨2067054639748066736758639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2756072852997422315678185 2067054639748066736758639)
      ·
        refine ⟨3100581959622100105137959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067054639748066736758639 3100581959622100105137959)
        ·
          refine ⟨4650872939433150157706939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3100581959622100105137959 4650872939433150157706939)
          ·
            refine ⟨6976309409149725236560409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4650872939433150157706939 6976309409149725236560409)
            ·
              refine ⟨5232232056862293927420307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6976309409149725236560409 5232232056862293927420307)
              ·
                refine ⟨7848348085293440891130461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5232232056862293927420307 7848348085293440891130461)
                ·
                  refine ⟨2943130531985040334173923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7848348085293440891130461 2943130531985040334173923)
                  ·
                    refine ⟨4414695797977560501260885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943130531985040334173923 4414695797977560501260885)
                    ·
                      refine ⟨51734716382549537124151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4414695797977560501260885 51734716382549537124151)
                      ·
                        rfl

theorem cell23_100753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_100753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100753 prefixEnd_100753 := by exact prefixLift 100753
  have htrace : WordTrace (prefixWord ++ tailWord_100753) baseStart_100753 baseEnd_100753 := by
    simpa [prefixWord, tailWord_100753, baseEnd_100753] using wordTrace_append hprefix tailTrace_100753
  have hstable : (prefixWord ++ tailWord_100753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100753).length < 2 ^ (prefixWord ++ tailWord_100753).sum := by decide
  have hdescent : baseEnd_100753 < baseStart_100753 := by decide
  rcases family_descends (prefixWord ++ tailWord_100753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100770 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_100770 : Nat := 118140960795 + 100770 * 2 ^ 59
def prefixEnd_100770 : Nat := 4983230072969 + 3 ^ 40 * 100770 * 2
def baseEnd_100770 : Nat := 51743445553675970611573

theorem tailTrace_100770 : CollatzResearch.WordTrace tailWord_100770 prefixEnd_100770 51743445553675970611573 := by
  unfold tailWord_100770
  simp only [CollatzResearch.WordTrace]
  refine ⟨918845961233743747734941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2450255896623316660626509 918845961233743747734941)
  ·
    refine ⟨344567235462653905400603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 918845961233743747734941 344567235462653905400603)
    ·
      refine ⟨516850853193980858100905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344567235462653905400603 516850853193980858100905)
      ·
        refine ⟨387638139895485643575679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 516850853193980858100905 387638139895485643575679)
        ·
          refine ⟨581457209843228465363519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387638139895485643575679 581457209843228465363519)
          ·
            refine ⟨872185814764842698045279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581457209843228465363519 872185814764842698045279)
            ·
              refine ⟨1308278722147264047067919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872185814764842698045279 1308278722147264047067919)
              ·
                refine ⟨1962418083220896070601879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1308278722147264047067919 1962418083220896070601879)
                ·
                  refine ⟨2943627124831344105902819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1962418083220896070601879 2943627124831344105902819)
                  ·
                    refine ⟨4415440687247016158854229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2943627124831344105902819 4415440687247016158854229)
                    ·
                      refine ⟨51743445553675970611573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4415440687247016158854229 51743445553675970611573)
                      ·
                        rfl

theorem cell23_100770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_100770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100770 prefixEnd_100770 := by exact prefixLift 100770
  have htrace : WordTrace (prefixWord ++ tailWord_100770) baseStart_100770 baseEnd_100770 := by
    simpa [prefixWord, tailWord_100770, baseEnd_100770] using wordTrace_append hprefix tailTrace_100770
  have hstable : (prefixWord ++ tailWord_100770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100770).length < 2 ^ (prefixWord ++ tailWord_100770).sum := by decide
  have hdescent : baseEnd_100770 < baseStart_100770 := by decide
  rcases family_descends (prefixWord ++ tailWord_100770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100797 : List Nat := [1, 4, 1, 2, 2, 2, 1, 4, 1, 5]
def baseStart_100797 : Nat := 118140960795 + 100797 * 2 ^ 59
def prefixEnd_100797 : Nat := 4983230072969 + 3 ^ 40 * 100797 * 2
def baseEnd_100797 : Nat := 17252436510449121657983

theorem tailTrace_100797 : CollatzResearch.WordTrace tailWord_100797 prefixEnd_100797 17252436510449121657983 := by
  unfold tailWord_100797
  simp only [CollatzResearch.WordTrace]
  refine ⟨3676368615837158602172645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2450912410558105734781763 3676368615837158602172645)
  ·
    refine ⟨689319115469467237907371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3676368615837158602172645 689319115469467237907371)
    ·
      refine ⟨1033978673204200856861057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689319115469467237907371 1033978673204200856861057)
      ·
        refine ⟨775484004903150642645793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033978673204200856861057 775484004903150642645793)
        ·
          refine ⟨581613003677362981984345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775484004903150642645793 581613003677362981984345)
          ·
            refine ⟨436209752758022236488259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581613003677362981984345 436209752758022236488259)
            ·
              refine ⟨654314629137033354732389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436209752758022236488259 654314629137033354732389)
              ·
                refine ⟨122683992963193754012323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654314629137033354732389 122683992963193754012323)
                ·
                  refine ⟨184025989444790631018485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122683992963193754012323 184025989444790631018485)
                  ·
                    refine ⟨17252436510449121657983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184025989444790631018485 17252436510449121657983)
                    ·
                      rfl

theorem cell23_100797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_100797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100797 prefixEnd_100797 := by exact prefixLift 100797
  have htrace : WordTrace (prefixWord ++ tailWord_100797) baseStart_100797 baseEnd_100797 := by
    simpa [prefixWord, tailWord_100797, baseEnd_100797] using wordTrace_append hprefix tailTrace_100797
  have hstable : (prefixWord ++ tailWord_100797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100797).length < 2 ^ (prefixWord ++ tailWord_100797).sum := by decide
  have hdescent : baseEnd_100797 < baseStart_100797 := by decide
  rcases family_descends (prefixWord ++ tailWord_100797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100810 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_100810 : Nat := 118140960795 + 100810 * 2 ^ 59
def prefixEnd_100810 : Nat := 4983230072969 + 3 ^ 40 * 100810 * 2
def baseEnd_100810 : Nat := 17254661593285271370463

theorem tailTrace_100810 : CollatzResearch.WordTrace tailWord_100810 prefixEnd_100810 17254661593285271370463 := by
  unfold tailWord_100810
  simp only [CollatzResearch.WordTrace]
  refine ⟨919210691197515455598971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2451228509860041214930589 919210691197515455598971)
  ·
    refine ⟨1378816036796273183398457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 919210691197515455598971 1378816036796273183398457)
    ·
      refine ⟨1034112027597204887548843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1378816036796273183398457 1034112027597204887548843)
      ·
        refine ⟨1551168041395807331323265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034112027597204887548843 1551168041395807331323265)
        ·
          refine ⟨1163376031046855498492449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1551168041395807331323265 1163376031046855498492449)
          ·
            refine ⟨872532023285141623869337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163376031046855498492449 872532023285141623869337)
            ·
              refine ⟨654399017463856217902003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872532023285141623869337 654399017463856217902003)
              ·
                refine ⟨981598526195784326853005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654399017463856217902003 981598526195784326853005)
                ·
                  refine ⟨368099447323419122569877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 981598526195784326853005 368099447323419122569877)
                  ·
                    refine ⟨17254661593285271370463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 368099447323419122569877 17254661593285271370463)
                    ·
                      rfl

theorem cell23_100810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_100810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100810 prefixEnd_100810 := by exact prefixLift 100810
  have htrace : WordTrace (prefixWord ++ tailWord_100810) baseStart_100810 baseEnd_100810 := by
    simpa [prefixWord, tailWord_100810, baseEnd_100810] using wordTrace_append hprefix tailTrace_100810
  have hstable : (prefixWord ++ tailWord_100810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100810).length < 2 ^ (prefixWord ++ tailWord_100810).sum := by decide
  have hdescent : baseEnd_100810 < baseStart_100810 := by decide
  rcases family_descends (prefixWord ++ tailWord_100810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100840 : List Nat := [2, 1, 4, 1, 1, 3, 1, 10]
def baseStart_100840 : Nat := 118140960795 + 100840 * 2 ^ 59
def prefixEnd_100840 : Nat := 4983230072969 + 3 ^ 40 * 100840 * 2
def baseEnd_100840 : Nat := 1917755155536692471713

theorem tailTrace_100840 : CollatzResearch.WordTrace tailWord_100840 prefixEnd_100840 1917755155536692471713 := by
  unfold tailWord_100840
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838968477340688472993987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2451957969787584630658649 1838968477340688472993987)
  ·
    refine ⟨2758452716011032709490981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1838968477340688472993987 2758452716011032709490981)
    ·
      refine ⟨517209884252068633029559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2758452716011032709490981 517209884252068633029559)
      ·
        refine ⟨775814826378102949544339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517209884252068633029559 775814826378102949544339)
        ·
          refine ⟨1163722239567154424316509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775814826378102949544339 1163722239567154424316509)
          ·
            refine ⟨436395839837682909118691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163722239567154424316509 436395839837682909118691)
            ·
              refine ⟨654593759756524363678037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436395839837682909118691 654593759756524363678037)
              ·
                refine ⟨1917755155536692471713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 654593759756524363678037 1917755155536692471713)
                ·
                  rfl

theorem cell23_100840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 10].length) (baseStart_100840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100840 prefixEnd_100840 := by exact prefixLift 100840
  have htrace : WordTrace (prefixWord ++ tailWord_100840) baseStart_100840 baseEnd_100840 := by
    simpa [prefixWord, tailWord_100840, baseEnd_100840] using wordTrace_append hprefix tailTrace_100840
  have hstable : (prefixWord ++ tailWord_100840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100840).length < 2 ^ (prefixWord ++ tailWord_100840).sum := by decide
  have hdescent : baseEnd_100840 < baseStart_100840 := by decide
  rcases family_descends (prefixWord ++ tailWord_100840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100854 : List Nat := [5, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_100854 : Nat := 118140960795 + 100854 * 2 ^ 59
def prefixEnd_100854 : Nat := 4983230072969 + 3 ^ 40 * 100854 * 2
def baseEnd_100854 : Nat := 51786577928653641961187

theorem tailTrace_100854 : CollatzResearch.WordTrace tailWord_100854 prefixEnd_100854 51786577928653641961187 := by
  unfold tailWord_100854
  simp only [CollatzResearch.WordTrace]
  refine ⟨229902973539416083562351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2452298384420438224665077 229902973539416083562351)
  ·
    refine ⟨344854460309124125343527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229902973539416083562351 344854460309124125343527)
    ·
      refine ⟨517281690463686188015291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344854460309124125343527 517281690463686188015291)
      ·
        refine ⟨775922535695529282022937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517281690463686188015291 775922535695529282022937)
        ·
          refine ⟨581941901771646961517203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775922535695529282022937 581941901771646961517203)
          ·
            refine ⟨872912852657470442275805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581941901771646961517203 872912852657470442275805)
            ·
              refine ⟨327342319746551415853427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872912852657470442275805 327342319746551415853427)
              ·
                refine ⟨491013479619827123780141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327342319746551415853427 491013479619827123780141)
                ·
                  refine ⟨184130054857435171417553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 491013479619827123780141 184130054857435171417553)
                  ·
                    refine ⟨138097541143076378563165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184130054857435171417553 138097541143076378563165)
                    ·
                      refine ⟨51786577928653641961187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 138097541143076378563165 51786577928653641961187)
                      ·
                        rfl

theorem cell23_100854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_100854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100854 prefixEnd_100854 := by exact prefixLift 100854
  have htrace : WordTrace (prefixWord ++ tailWord_100854) baseStart_100854 baseEnd_100854 := by
    simpa [prefixWord, tailWord_100854, baseEnd_100854] using wordTrace_append hprefix tailTrace_100854
  have hstable : (prefixWord ++ tailWord_100854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100854).length < 2 ^ (prefixWord ++ tailWord_100854).sum := by decide
  have hdescent : baseEnd_100854 < baseStart_100854 := by decide
  rcases family_descends (prefixWord ++ tailWord_100854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100867 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 3]
def baseStart_100867 : Nat := 118140960795 + 100867 * 2 ^ 59
def prefixEnd_100867 : Nat := 4983230072969 + 3 ^ 40 * 100867 * 2
def baseEnd_100867 : Nat := 51793253177162091098627

theorem tailTrace_100867 : CollatzResearch.WordTrace tailWord_100867 prefixEnd_100867 51793253177162091098627 := by
  unfold tailWord_100867
  simp only [CollatzResearch.WordTrace]
  refine ⟨3678921725583560557220855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2452614483722373704813903 3678921725583560557220855)
  ·
    refine ⟨5518382588375340835831283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3678921725583560557220855 5518382588375340835831283)
    ·
      refine ⟨8277573882563011253746925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5518382588375340835831283 8277573882563011253746925)
      ·
        refine ⟨3104090205961129220155097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8277573882563011253746925 3104090205961129220155097)
        ·
          refine ⟨2328067654470846915116323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3104090205961129220155097 2328067654470846915116323)
          ·
            refine ⟨3492101481706270372674485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2328067654470846915116323 3492101481706270372674485)
            ·
              refine ⟨327384513909962847438233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3492101481706270372674485 327384513909962847438233)
              ·
                refine ⟨245538385432472135578675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327384513909962847438233 245538385432472135578675)
                ·
                  refine ⟨368307578148708203368013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245538385432472135578675 368307578148708203368013)
                  ·
                    refine ⟨138115341805765576263005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 368307578148708203368013 138115341805765576263005)
                    ·
                      refine ⟨51793253177162091098627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 138115341805765576263005 51793253177162091098627)
                      ·
                        rfl

theorem cell23_100867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_100867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100867 prefixEnd_100867 := by exact prefixLift 100867
  have htrace : WordTrace (prefixWord ++ tailWord_100867) baseStart_100867 baseEnd_100867 := by
    simpa [prefixWord, tailWord_100867, baseEnd_100867] using wordTrace_append hprefix tailTrace_100867
  have hstable : (prefixWord ++ tailWord_100867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100867).length < 2 ^ (prefixWord ++ tailWord_100867).sum := by decide
  have hdescent : baseEnd_100867 < baseStart_100867 := by decide
  rcases family_descends (prefixWord ++ tailWord_100867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_100871 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 1, 1, 5]
def baseStart_100871 : Nat := 118140960795 + 100871 * 2 ^ 59
def prefixEnd_100871 : Nat := 4983230072969 + 3 ^ 40 * 100871 * 2
def baseEnd_100871 : Nat := 51795307099780075448609

theorem tailTrace_100871 : CollatzResearch.WordTrace tailWord_100871 prefixEnd_100871 51795307099780075448609 := by
  unfold tailWord_100871
  simp only [CollatzResearch.WordTrace]
  refine ⟨3679067617569069240366467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2452711745046046160244311 3679067617569069240366467)
  ·
    refine ⟨5518601426353603860549701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3679067617569069240366467 5518601426353603860549701)
    ·
      refine ⟨1034737767441300723853069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5518601426353603860549701 1034737767441300723853069)
      ·
        refine ⟨388026662790487771444901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1034737767441300723853069 388026662790487771444901)
        ·
          refine ⟨72754999273216457145919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 388026662790487771444901 72754999273216457145919)
          ·
            refine ⟨109132498909824685718879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72754999273216457145919 109132498909824685718879)
            ·
              refine ⟨163698748364737028578319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109132498909824685718879 163698748364737028578319)
              ·
                refine ⟨245548122547105542867479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163698748364737028578319 245548122547105542867479)
                ·
                  refine ⟨368322183820658314301219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245548122547105542867479 368322183820658314301219)
                  ·
                    refine ⟨552483275730987471451829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 368322183820658314301219 552483275730987471451829)
                    ·
                      refine ⟨51795307099780075448609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 552483275730987471451829 51795307099780075448609)
                      ·
                        rfl

theorem cell23_100871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_100871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_100871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_100871 prefixEnd_100871 := by exact prefixLift 100871
  have htrace : WordTrace (prefixWord ++ tailWord_100871) baseStart_100871 baseEnd_100871 := by
    simpa [prefixWord, tailWord_100871, baseEnd_100871] using wordTrace_append hprefix tailTrace_100871
  have hstable : (prefixWord ++ tailWord_100871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_100871).length < 2 ^ (prefixWord ++ tailWord_100871).sum := by decide
  have hdescent : baseEnd_100871 < baseStart_100871 := by decide
  rcases family_descends (prefixWord ++ tailWord_100871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101081 : List Nat := [1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 3]
def baseStart_101081 : Nat := 118140960795 + 101081 * 2 ^ 59
def prefixEnd_101081 : Nat := 4983230072969 + 3 ^ 40 * 101081 * 2
def baseEnd_101081 : Nat := 51903138037224253822643

theorem tailTrace_101081 : CollatzResearch.WordTrace tailWord_101081 prefixEnd_101081 51903138037224253822643 := by
  unfold tailWord_101081
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686726946808275105511097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2457817964538850070340731 3686726946808275105511097)
  ·
    refine ⟨2765045210106206329133323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3686726946808275105511097 2765045210106206329133323)
    ·
      refine ⟨4147567815159309493699985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2765045210106206329133323 4147567815159309493699985)
      ·
        refine ⟨3110675861369482120274989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4147567815159309493699985 3110675861369482120274989)
        ·
          refine ⟨1166503448013555795103121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3110675861369482120274989 1166503448013555795103121)
          ·
            refine ⟨874877586010166846327341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166503448013555795103121 874877586010166846327341)
            ·
              refine ⟨328079094753812567372753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874877586010166846327341 328079094753812567372753)
              ·
                refine ⟨246059321065359425529565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328079094753812567372753 246059321065359425529565)
                ·
                  refine ⟨92272245399509784573587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246059321065359425529565 92272245399509784573587)
                  ·
                    refine ⟨138408368099264676860381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92272245399509784573587 138408368099264676860381)
                    ·
                      refine ⟨51903138037224253822643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 138408368099264676860381 51903138037224253822643)
                      ·
                        rfl

theorem cell23_101081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_101081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101081 prefixEnd_101081 := by exact prefixLift 101081
  have htrace : WordTrace (prefixWord ++ tailWord_101081) baseStart_101081 baseEnd_101081 := by
    simpa [prefixWord, tailWord_101081, baseEnd_101081] using wordTrace_append hprefix tailTrace_101081
  have hstable : (prefixWord ++ tailWord_101081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101081).length < 2 ^ (prefixWord ++ tailWord_101081).sum := by decide
  have hdescent : baseEnd_101081 < baseStart_101081 := by decide
  rcases family_descends (prefixWord ++ tailWord_101081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101101 : List Nat := [1, 5, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_101101 : Nat := 118140960795 + 101101 * 2 ^ 59
def prefixEnd_101101 : Nat := 4983230072969 + 3 ^ 40 * 101101 * 2
def baseEnd_101101 : Nat := 17304469216771391857517

theorem tailTrace_101101 : CollatzResearch.WordTrace tailWord_101101 prefixEnd_101101 17304469216771391857517 := by
  unfold tailWord_101101
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687456406735818521239157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2458304271157212347492771 3687456406735818521239157)
  ·
    refine ⟨345699038131482986366171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3687456406735818521239157 345699038131482986366171)
    ·
      refine ⟨518548557197224479549257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345699038131482986366171 518548557197224479549257)
      ·
        refine ⟨388911417897918359661943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518548557197224479549257 388911417897918359661943)
        ·
          refine ⟨583367126846877539492915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388911417897918359661943 583367126846877539492915)
          ·
            refine ⟨875050690270316309239373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583367126846877539492915 875050690270316309239373)
            ·
              refine ⟨328144008851368615964765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 875050690270316309239373 328144008851368615964765)
              ·
                refine ⟨123054003319263230986787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328144008851368615964765 123054003319263230986787)
                ·
                  refine ⟨184581004978894846480181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123054003319263230986787 184581004978894846480181)
                  ·
                    refine ⟨17304469216771391857517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184581004978894846480181 17304469216771391857517)
                    ·
                      rfl

theorem cell23_101101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_101101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101101 prefixEnd_101101 := by exact prefixLift 101101
  have htrace : WordTrace (prefixWord ++ tailWord_101101) baseStart_101101 baseEnd_101101 := by
    simpa [prefixWord, tailWord_101101, baseEnd_101101] using wordTrace_append hprefix tailTrace_101101
  have hstable : (prefixWord ++ tailWord_101101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101101).length < 2 ^ (prefixWord ++ tailWord_101101).sum := by decide
  have hdescent : baseEnd_101101 < baseStart_101101 := by decide
  rcases family_descends (prefixWord ++ tailWord_101101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101149 : List Nat := [1, 4, 2, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_101149 : Nat := 118140960795 + 101149 * 2 ^ 59
def prefixEnd_101149 : Nat := 4983230072969 + 3 ^ 40 * 101149 * 2
def baseEnd_101149 : Nat := 51938054721729987772331

theorem tailTrace_101149 : CollatzResearch.WordTrace tailWord_101149 prefixEnd_101149 51938054721729987772331 := by
  unfold tailWord_101149
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689207110561922718986501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2459471407041281812657667 3689207110561922718986501)
  ·
    refine ⟨691726333230360509809969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3689207110561922718986501 691726333230360509809969)
    ·
      refine ⟨518794749922770382357477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 691726333230360509809969 518794749922770382357477)
      ·
        refine ⟨97274015610519446692027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 518794749922770382357477 97274015610519446692027)
        ·
          refine ⟨145911023415779170038041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97274015610519446692027 145911023415779170038041)
          ·
            refine ⟨109433267561834377528531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145911023415779170038041 109433267561834377528531)
            ·
              refine ⟨164149901342751566292797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109433267561834377528531 164149901342751566292797)
              ·
                refine ⟨61556213003531837359799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 164149901342751566292797 61556213003531837359799)
                ·
                  refine ⟨92334319505297756039699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61556213003531837359799 92334319505297756039699)
                  ·
                    refine ⟨138501479257946634059549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92334319505297756039699 138501479257946634059549)
                    ·
                      refine ⟨51938054721729987772331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 138501479257946634059549 51938054721729987772331)
                      ·
                        rfl

theorem cell23_101149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_101149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101149 prefixEnd_101149 := by exact prefixLift 101149
  have htrace : WordTrace (prefixWord ++ tailWord_101149) baseStart_101149 baseEnd_101149 := by
    simpa [prefixWord, tailWord_101149, baseEnd_101149] using wordTrace_append hprefix tailTrace_101149
  have hstable : (prefixWord ++ tailWord_101149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101149).length < 2 ^ (prefixWord ++ tailWord_101149).sum := by decide
  have hdescent : baseEnd_101149 < baseStart_101149 := by decide
  rcases family_descends (prefixWord ++ tailWord_101149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101182 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_101182 : Nat := 118140960795 + 101182 * 2 ^ 59
def prefixEnd_101182 : Nat := 4983230072969 + 3 ^ 40 * 101182 * 2
def baseEnd_101182 : Nat := 17318333194442786219893

theorem tailTrace_101182 : CollatzResearch.WordTrace tailWord_101182 prefixEnd_101182 17318333194442786219893 := by
  unfold tailWord_101182
  simp only [CollatzResearch.WordTrace]
  refine ⟨461301339930296169367225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2460273812961579569958533 461301339930296169367225)
  ·
    refine ⟨345976004947722127025419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 461301339930296169367225 345976004947722127025419)
    ·
      refine ⟨518964007421583190538129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 345976004947722127025419 518964007421583190538129)
      ·
        refine ⟨389223005566187392903597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 518964007421583190538129 389223005566187392903597)
        ·
          refine ⟨145958627087320272338849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389223005566187392903597 145958627087320272338849)
          ·
            refine ⟨109468970315490204254137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145958627087320272338849 109468970315490204254137)
            ·
              refine ⟨82101727736617653190603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109468970315490204254137 82101727736617653190603)
              ·
                refine ⟨123152591604926479785905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82101727736617653190603 123152591604926479785905)
                ·
                  refine ⟨92364443703694859839429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123152591604926479785905 92364443703694859839429)
                  ·
                    refine ⟨17318333194442786219893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92364443703694859839429 17318333194442786219893)
                    ·
                      rfl

theorem cell23_101182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_101182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101182 prefixEnd_101182 := by exact prefixLift 101182
  have htrace : WordTrace (prefixWord ++ tailWord_101182) baseStart_101182 baseEnd_101182 := by
    simpa [prefixWord, tailWord_101182, baseEnd_101182] using wordTrace_append hprefix tailTrace_101182
  have hstable : (prefixWord ++ tailWord_101182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101182).length < 2 ^ (prefixWord ++ tailWord_101182).sum := by decide
  have hdescent : baseEnd_101182 < baseStart_101182 := by decide
  rcases family_descends (prefixWord ++ tailWord_101182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101194 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_101194 : Nat := 118140960795 + 101194 * 2 ^ 59
def prefixEnd_101194 : Nat := 4983230072969 + 3 ^ 40 * 101194 * 2
def baseEnd_101194 : Nat := 51961161351182311709623

theorem tailTrace_101194 : CollatzResearch.WordTrace tailWord_101194 prefixEnd_101194 51961161351182311709623 := by
  unfold tailWord_101194
  simp only [CollatzResearch.WordTrace]
  refine ⟨922712098849723851093659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2460565596932596936249757 922712098849723851093659)
  ·
    refine ⟨1384068148274585776640489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 922712098849723851093659 1384068148274585776640489)
    ·
      refine ⟨1038051111205939332480367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1384068148274585776640489 1038051111205939332480367)
      ·
        refine ⟨1557076666808908998720551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038051111205939332480367 1557076666808908998720551)
        ·
          refine ⟨2335615000213363498080827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557076666808908998720551 2335615000213363498080827)
          ·
            refine ⟨3503422500320045247121241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2335615000213363498080827 3503422500320045247121241)
            ·
              refine ⟨2627566875240033935340931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3503422500320045247121241 2627566875240033935340931)
              ·
                refine ⟨3941350312860050903011397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2627566875240033935340931 3941350312860050903011397)
                ·
                  refine ⟨739003183661259544314637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3941350312860050903011397 739003183661259544314637)
                  ·
                    refine ⟨277126193872972329117989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739003183661259544314637 277126193872972329117989)
                    ·
                      refine ⟨51961161351182311709623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 277126193872972329117989 51961161351182311709623)
                      ·
                        rfl

theorem cell23_101194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_101194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101194 prefixEnd_101194 := by exact prefixLift 101194
  have htrace : WordTrace (prefixWord ++ tailWord_101194) baseStart_101194 baseEnd_101194 := by
    simpa [prefixWord, tailWord_101194, baseEnd_101194] using wordTrace_append hprefix tailTrace_101194
  have hstable : (prefixWord ++ tailWord_101194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101194).length < 2 ^ (prefixWord ++ tailWord_101194).sum := by decide
  have hdescent : baseEnd_101194 < baseStart_101194 := by decide
  rcases family_descends (prefixWord ++ tailWord_101194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101215 : List Nat := [1, 1, 2, 3, 1, 3, 5, 1, 1, 3, 2]
def baseStart_101215 : Nat := 118140960795 + 101215 * 2 ^ 59
def prefixEnd_101215 : Nat := 4983230072969 + 3 ^ 40 * 101215 * 2
def baseEnd_101215 : Nat := 51971944444926729547027

theorem tailTrace_101215 : CollatzResearch.WordTrace tailWord_101215 prefixEnd_101215 51971944444926729547027 := by
  unfold tailWord_101215
  simp only [CollatzResearch.WordTrace]
  refine ⟨3691614328322815990889099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2461076218881877327259399 3691614328322815990889099)
  ·
    refine ⟨5537421492484223986333649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3691614328322815990889099 5537421492484223986333649)
    ·
      refine ⟨4153066119363167989750237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5537421492484223986333649 4153066119363167989750237)
      ·
        refine ⟨1557399794761187996156339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4153066119363167989750237 1557399794761187996156339)
        ·
          refine ⟨2336099692141781994234509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557399794761187996156339 2336099692141781994234509)
          ·
            refine ⟨876037384553168247837941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2336099692141781994234509 876037384553168247837941)
            ·
              refine ⟨82128504801859523234807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 876037384553168247837941 82128504801859523234807)
              ·
                refine ⟨123192757202789284852211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82128504801859523234807 123192757202789284852211)
                ·
                  refine ⟨184789135804183927278317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123192757202789284852211 184789135804183927278317)
                  ·
                    refine ⟨69295925926568972729369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184789135804183927278317 69295925926568972729369)
                    ·
                      refine ⟨51971944444926729547027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69295925926568972729369 51971944444926729547027)
                      ·
                        rfl

theorem cell23_101215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_101215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101215 prefixEnd_101215 := by exact prefixLift 101215
  have htrace : WordTrace (prefixWord ++ tailWord_101215) baseStart_101215 baseEnd_101215 := by
    simpa [prefixWord, tailWord_101215, baseEnd_101215] using wordTrace_append hprefix tailTrace_101215
  have hstable : (prefixWord ++ tailWord_101215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101215).length < 2 ^ (prefixWord ++ tailWord_101215).sum := by decide
  have hdescent : baseEnd_101215 < baseStart_101215 := by decide
  rcases family_descends (prefixWord ++ tailWord_101215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101238 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_101238 : Nat := 118140960795 + 101238 * 2 ^ 59
def prefixEnd_101238 : Nat := 4983230072969 + 3 ^ 40 * 101238 * 2
def baseEnd_101238 : Nat := 17327918166660046519807

theorem tailTrace_101238 : CollatzResearch.WordTrace tailWord_101238 prefixEnd_101238 17327918166660046519807 := by
  unfold tailWord_101238
  simp only [CollatzResearch.WordTrace]
  refine ⟨230778325452468182436023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2461635471492993945984245 230778325452468182436023)
  ·
    refine ⟨346167488178702273654035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 230778325452468182436023 346167488178702273654035)
    ·
      refine ⟨519251232268053410481053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 346167488178702273654035 519251232268053410481053)
      ·
        refine ⟨194719212100520028930395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 519251232268053410481053 194719212100520028930395)
        ·
          refine ⟨292078818150780043395593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194719212100520028930395 292078818150780043395593)
          ·
            refine ⟨219059113613085032546695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 292078818150780043395593 219059113613085032546695)
            ·
              refine ⟨328588670419627548820043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219059113613085032546695 328588670419627548820043)
              ·
                refine ⟨492883005629441323230065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328588670419627548820043 492883005629441323230065)
                ·
                  refine ⟨369662254222080992422549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492883005629441323230065 369662254222080992422549)
                  ·
                    refine ⟨17327918166660046519807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 369662254222080992422549 17327918166660046519807)
                    ·
                      rfl

theorem cell23_101238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_101238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101238 prefixEnd_101238 := by exact prefixLift 101238
  have htrace : WordTrace (prefixWord ++ tailWord_101238) baseStart_101238 baseEnd_101238 := by
    simpa [prefixWord, tailWord_101238, baseEnd_101238] using wordTrace_append hprefix tailTrace_101238
  have hstable : (prefixWord ++ tailWord_101238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101238).length < 2 ^ (prefixWord ++ tailWord_101238).sum := by decide
  have hdescent : baseEnd_101238 < baseStart_101238 := by decide
  rcases family_descends (prefixWord ++ tailWord_101238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101241 : List Nat := [1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 4]
def baseStart_101241 : Nat := 118140960795 + 101241 * 2 ^ 59
def prefixEnd_101241 : Nat := 4983230072969 + 3 ^ 40 * 101241 * 2
def baseEnd_101241 : Nat := 51985294941943627821907

theorem tailTrace_101241 : CollatzResearch.WordTrace tailWord_101241 prefixEnd_101241 51985294941943627821907 := by
  unfold tailWord_101241
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692562626228622431335577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2461708417485748287557051 3692562626228622431335577)
  ·
    refine ⟨2769421969671466823501683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3692562626228622431335577 2769421969671466823501683)
    ·
      refine ⟨4154132954507200235252525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769421969671466823501683 4154132954507200235252525)
      ·
        refine ⟨1557799857940200088219697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4154132954507200235252525 1557799857940200088219697)
        ·
          refine ⟨1168349893455150066164773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557799857940200088219697 1168349893455150066164773)
          ·
            refine ⟨219065605022840637405895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1168349893455150066164773 219065605022840637405895)
            ·
              refine ⟨328598407534260956108843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219065605022840637405895 328598407534260956108843)
              ·
                refine ⟨492897611301391434163265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 328598407534260956108843 492897611301391434163265)
                ·
                  refine ⟨369673208476043575622449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 492897611301391434163265 369673208476043575622449)
                  ·
                    refine ⟨277254906357032681716837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 369673208476043575622449 277254906357032681716837)
                    ·
                      refine ⟨51985294941943627821907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 277254906357032681716837 51985294941943627821907)
                      ·
                        rfl

theorem cell23_101241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_101241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101241 prefixEnd_101241 := by exact prefixLift 101241
  have htrace : WordTrace (prefixWord ++ tailWord_101241) baseStart_101241 baseEnd_101241 := by
    simpa [prefixWord, tailWord_101241, baseEnd_101241] using wordTrace_append hprefix tailTrace_101241
  have hstable : (prefixWord ++ tailWord_101241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101241).length < 2 ^ (prefixWord ++ tailWord_101241).sum := by decide
  have hdescent : baseEnd_101241 < baseStart_101241 := by decide
  rcases family_descends (prefixWord ++ tailWord_101241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101245 : List Nat := [1, 4, 1, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_101245 : Nat := 118140960795 + 101245 * 2 ^ 59
def prefixEnd_101245 : Nat := 4983230072969 + 3 ^ 40 * 101245 * 2
def baseEnd_101245 : Nat := 51987348864561612171889

theorem tailTrace_101245 : CollatzResearch.WordTrace tailWord_101245 prefixEnd_101245 51987348864561612171889 := by
  unfold tailWord_101245
  simp only [CollatzResearch.WordTrace]
  refine ⟨3692708518214131114481189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2461805678809420742987459 3692708518214131114481189)
  ·
    refine ⟨692382847165149583965223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3692708518214131114481189 692382847165149583965223)
    ·
      refine ⟨1038574270747724375947835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 692382847165149583965223 1038574270747724375947835)
      ·
        refine ⟨1557861406121586563921753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038574270747724375947835 1557861406121586563921753)
        ·
          refine ⟨1168396054591189922941315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557861406121586563921753 1168396054591189922941315)
          ·
            refine ⟨1752594081886784884411973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1168396054591189922941315 1752594081886784884411973)
            ·
              refine ⟨328611390353772165827245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1752594081886784884411973 328611390353772165827245)
              ·
                refine ⟨123229271382664562185217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328611390353772165827245 123229271382664562185217)
                ·
                  refine ⟨92421953536998421638913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123229271382664562185217 92421953536998421638913)
                  ·
                    refine ⟨69316465152748816229185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92421953536998421638913 69316465152748816229185)
                    ·
                      refine ⟨51987348864561612171889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69316465152748816229185 51987348864561612171889)
                      ·
                        rfl

theorem cell23_101245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_101245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101245 prefixEnd_101245 := by exact prefixLift 101245
  have htrace : WordTrace (prefixWord ++ tailWord_101245) baseStart_101245 baseEnd_101245 := by
    simpa [prefixWord, tailWord_101245, baseEnd_101245] using wordTrace_append hprefix tailTrace_101245
  have hstable : (prefixWord ++ tailWord_101245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101245).length < 2 ^ (prefixWord ++ tailWord_101245).sum := by decide
  have hdescent : baseEnd_101245 < baseStart_101245 := by decide
  rcases family_descends (prefixWord ++ tailWord_101245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101266 : List Nat := [3, 2, 3, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_101266 : Nat := 118140960795 + 101266 * 2 ^ 59
def prefixEnd_101266 : Nat := 4983230072969 + 3 ^ 40 * 101266 * 2
def baseEnd_101266 : Nat := 51998131958306030009293

theorem tailTrace_101266 : CollatzResearch.WordTrace tailWord_101266 prefixEnd_101266 51998131958306030009293 := by
  unfold tailWord_101266
  simp only [CollatzResearch.WordTrace]
  refine ⟨923368612784512925248913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2462316300758701133997101 923368612784512925248913)
  ·
    refine ⟨692526459588384693936685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 923368612784512925248913 692526459588384693936685)
    ·
      refine ⟨259697422345644260226257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 692526459588384693936685 259697422345644260226257)
      ·
        refine ⟨194773066759233195169693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259697422345644260226257 194773066759233195169693)
        ·
          refine ⟨73039900034712448188635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194773066759233195169693 73039900034712448188635)
          ·
            refine ⟨109559850052068672282953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73039900034712448188635 109559850052068672282953)
            ·
              refine ⟨82169887539051504212215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109559850052068672282953 82169887539051504212215)
              ·
                refine ⟨123254831308577256318323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82169887539051504212215 123254831308577256318323)
                ·
                  refine ⟨184882246962865884477485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123254831308577256318323 184882246962865884477485)
                  ·
                    refine ⟨69330842611074706679057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184882246962865884477485 69330842611074706679057)
                    ·
                      refine ⟨51998131958306030009293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69330842611074706679057 51998131958306030009293)
                      ·
                        rfl

theorem cell23_101266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_101266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101266 prefixEnd_101266 := by exact prefixLift 101266
  have htrace : WordTrace (prefixWord ++ tailWord_101266) baseStart_101266 baseEnd_101266 := by
    simpa [prefixWord, tailWord_101266, baseEnd_101266] using wordTrace_append hprefix tailTrace_101266
  have hstable : (prefixWord ++ tailWord_101266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101266).length < 2 ^ (prefixWord ++ tailWord_101266).sum := by decide
  have hdescent : baseEnd_101266 < baseStart_101266 := by decide
  rcases family_descends (prefixWord ++ tailWord_101266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101301 : List Nat := [1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 4]
def baseStart_101301 : Nat := 118140960795 + 101301 * 2 ^ 59
def prefixEnd_101301 : Nat := 4983230072969 + 3 ^ 40 * 101301 * 2
def baseEnd_101301 : Nat := 52016103781213393071631

theorem tailTrace_101301 : CollatzResearch.WordTrace tailWord_101301 prefixEnd_101301 52016103781213393071631 := by
  unfold tailWord_101301
  simp only [CollatzResearch.WordTrace]
  refine ⟨3694751006011252678519757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2463167337340835119013171 3694751006011252678519757)
  ·
    refine ⟨1385531627254219754444909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3694751006011252678519757 1385531627254219754444909)
    ·
      refine ⟨519574360220332407916841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1385531627254219754444909 519574360220332407916841)
      ·
        refine ⟨389680770165249305937631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519574360220332407916841 389680770165249305937631)
        ·
          refine ⟨584521155247873958906447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389680770165249305937631 584521155247873958906447)
          ·
            refine ⟨876781732871810938359671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584521155247873958906447 876781732871810938359671)
            ·
              refine ⟨1315172599307716407539507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 876781732871810938359671 1315172599307716407539507)
              ·
                refine ⟨1972758898961574611309261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1315172599307716407539507 1972758898961574611309261)
                ·
                  refine ⟨739784587110590479240973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1972758898961574611309261 739784587110590479240973)
                  ·
                    refine ⟨277419220166471429715365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 739784587110590479240973 277419220166471429715365)
                    ·
                      refine ⟨52016103781213393071631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 277419220166471429715365 52016103781213393071631)
                      ·
                        rfl

theorem cell23_101301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_101301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101301 prefixEnd_101301 := by exact prefixLift 101301
  have htrace : WordTrace (prefixWord ++ tailWord_101301) baseStart_101301 baseEnd_101301 := by
    simpa [prefixWord, tailWord_101301, baseEnd_101301] using wordTrace_append hprefix tailTrace_101301
  have hstable : (prefixWord ++ tailWord_101301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101301).length < 2 ^ (prefixWord ++ tailWord_101301).sum := by decide
  have hdescent : baseEnd_101301 < baseStart_101301 := by decide
  rcases family_descends (prefixWord ++ tailWord_101301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101311 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 5, 4]
def baseStart_101311 : Nat := 118140960795 + 101311 * 2 ^ 59
def prefixEnd_101311 : Nat := 4983230072969 + 3 ^ 40 * 101311 * 2
def baseEnd_101311 : Nat := 17340412862586117982195

theorem tailTrace_101311 : CollatzResearch.WordTrace tailWord_101311 prefixEnd_101311 17340412862586117982195 := by
  unfold tailWord_101311
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695115735975024386383787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2463410490650016257589191 3695115735975024386383787)
  ·
    refine ⟨5542673603962536579575681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3695115735975024386383787 5542673603962536579575681)
    ·
      refine ⟨4157005202971902434681761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5542673603962536579575681 4157005202971902434681761)
      ·
        refine ⟨3117753902228926826011321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4157005202971902434681761 3117753902228926826011321)
        ·
          refine ⟨2338315426671695119508491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3117753902228926826011321 2338315426671695119508491)
          ·
            refine ⟨3507473140007542679262737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338315426671695119508491 3507473140007542679262737)
            ·
              refine ⟨2630604855005657009447053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3507473140007542679262737 2630604855005657009447053)
              ·
                refine ⟨986476820627121378542645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2630604855005657009447053 986476820627121378542645)
                ·
                  refine ⟨92482201933792629238373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 986476820627121378542645 92482201933792629238373)
                  ·
                    refine ⟨17340412862586117982195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92482201933792629238373 17340412862586117982195)
                    ·
                      rfl

theorem cell23_101311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 5, 4].length) (baseStart_101311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101311 prefixEnd_101311 := by exact prefixLift 101311
  have htrace : WordTrace (prefixWord ++ tailWord_101311) baseStart_101311 baseEnd_101311 := by
    simpa [prefixWord, tailWord_101311, baseEnd_101311] using wordTrace_append hprefix tailTrace_101311
  have hstable : (prefixWord ++ tailWord_101311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101311).length < 2 ^ (prefixWord ++ tailWord_101311).sum := by decide
  have hdescent : baseEnd_101311 < baseStart_101311 := by decide
  rcases family_descends (prefixWord ++ tailWord_101311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101338 : List Nat := [3, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_101338 : Nat := 118140960795 + 101338 * 2 ^ 59
def prefixEnd_101338 : Nat := 4983230072969 + 3 ^ 40 * 101338 * 2
def baseEnd_101338 : Nat := 52035102565429748308961

theorem tailTrace_101338 : CollatzResearch.WordTrace tailWord_101338 prefixEnd_101338 52035102565429748308961 := by
  unfold tailWord_101338
  simp only [CollatzResearch.WordTrace]
  refine ⟨924025126719301999404167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2464067004584805331744445 924025126719301999404167)
  ·
    refine ⟨1386037690078952999106251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924025126719301999404167 1386037690078952999106251)
    ·
      refine ⟨2079056535118429498659377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386037690078952999106251 2079056535118429498659377)
      ·
        refine ⟨1559292401338822123994533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2079056535118429498659377 1559292401338822123994533)
        ·
          refine ⟨292367325251029148248975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1559292401338822123994533 292367325251029148248975)
          ·
            refine ⟨438550987876543722373463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292367325251029148248975 438550987876543722373463)
            ·
              refine ⟨657826481814815583560195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438550987876543722373463 657826481814815583560195)
              ·
                refine ⟨986739722722223375340293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 657826481814815583560195 986739722722223375340293)
                ·
                  refine ⟨185013698010416882876305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 986739722722223375340293 185013698010416882876305)
                  ·
                    refine ⟨138760273507812662157229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185013698010416882876305 138760273507812662157229)
                    ·
                      refine ⟨52035102565429748308961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 138760273507812662157229 52035102565429748308961)
                      ·
                        rfl

theorem cell23_101338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_101338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101338 prefixEnd_101338 := by exact prefixLift 101338
  have htrace : WordTrace (prefixWord ++ tailWord_101338) baseStart_101338 baseEnd_101338 := by
    simpa [prefixWord, tailWord_101338, baseEnd_101338] using wordTrace_append hprefix tailTrace_101338
  have hstable : (prefixWord ++ tailWord_101338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101338).length < 2 ^ (prefixWord ++ tailWord_101338).sum := by decide
  have hdescent : baseEnd_101338 < baseStart_101338 := by decide
  rcases family_descends (prefixWord ++ tailWord_101338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101368 : List Nat := [2, 1, 2, 1, 1, 3, 1, 3, 5, 1, 3]
def baseStart_101368 : Nat := 118140960795 + 101368 * 2 ^ 59
def prefixEnd_101368 : Nat := 4983230072969 + 3 ^ 40 * 101368 * 2
def baseEnd_101368 : Nat := 52050506985064630933823

theorem tailTrace_101368 : CollatzResearch.WordTrace tailWord_101368 prefixEnd_101368 52050506985064630933823 := by
  unfold tailWord_101368
  simp only [CollatzResearch.WordTrace]
  refine ⟨1848597348384261560604379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2464796464512348747472505 1848597348384261560604379)
  ·
    refine ⟨2772896022576392340906569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1848597348384261560604379 2772896022576392340906569)
    ·
      refine ⟨2079672016932294255679927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772896022576392340906569 2079672016932294255679927)
      ·
        refine ⟨3119508025398441383519891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079672016932294255679927 3119508025398441383519891)
        ·
          refine ⟨4679262038097662075279837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3119508025398441383519891 4679262038097662075279837)
          ·
            refine ⟨1754723264286623278229939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4679262038097662075279837 1754723264286623278229939)
            ·
              refine ⟨2632084896429934917344909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1754723264286623278229939 2632084896429934917344909)
              ·
                refine ⟨987031836161225594004341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2632084896429934917344909 987031836161225594004341)
                ·
                  refine ⟨92534234640114899437907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 987031836161225594004341 92534234640114899437907)
                  ·
                    refine ⟨138801351960172349156861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92534234640114899437907 138801351960172349156861)
                    ·
                      refine ⟨52050506985064630933823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 138801351960172349156861 52050506985064630933823)
                      ·
                        rfl

theorem cell23_101368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 1, 3].length) (baseStart_101368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101368 prefixEnd_101368 := by exact prefixLift 101368
  have htrace : WordTrace (prefixWord ++ tailWord_101368) baseStart_101368 baseEnd_101368 := by
    simpa [prefixWord, tailWord_101368, baseEnd_101368] using wordTrace_append hprefix tailTrace_101368
  have hstable : (prefixWord ++ tailWord_101368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101368).length < 2 ^ (prefixWord ++ tailWord_101368).sum := by decide
  have hdescent : baseEnd_101368 < baseStart_101368 := by decide
  rcases family_descends (prefixWord ++ tailWord_101368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101402 : List Nat := [3, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3]
def baseStart_101402 : Nat := 118140960795 + 101402 * 2 ^ 59
def prefixEnd_101402 : Nat := 4983230072969 + 3 ^ 40 * 101402 * 2
def baseEnd_101402 : Nat := 52067965327317497908667

theorem tailTrace_101402 : CollatzResearch.WordTrace tailWord_101402 prefixEnd_101402 52067965327317497908667 := by
  unfold tailWord_101402
  simp only [CollatzResearch.WordTrace]
  refine ⟨924608694661336731986615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2465623185763564618630973 924608694661336731986615)
  ·
    refine ⟨1386913041992005097979923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 924608694661336731986615 1386913041992005097979923)
    ·
      refine ⟨2080369562988007646969885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1386913041992005097979923 2080369562988007646969885)
      ·
        refine ⟨780138586120502867613707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2080369562988007646969885 780138586120502867613707)
        ·
          refine ⟨1170207879180754301420561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 780138586120502867613707 1170207879180754301420561)
          ·
            refine ⟨877655909385565726065421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1170207879180754301420561 877655909385565726065421)
            ·
              refine ⟨329120966019587147274533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 877655909385565726065421 329120966019587147274533)
              ·
                refine ⟨61710181128672590113975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 329120966019587147274533 61710181128672590113975)
                ·
                  refine ⟨92565271693008885170963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61710181128672590113975 92565271693008885170963)
                  ·
                    refine ⟨138847907539513327756445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92565271693008885170963 138847907539513327756445)
                    ·
                      refine ⟨52067965327317497908667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 138847907539513327756445 52067965327317497908667)
                      ·
                        rfl

theorem cell23_101402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_101402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101402 prefixEnd_101402 := by exact prefixLift 101402
  have htrace : WordTrace (prefixWord ++ tailWord_101402) baseStart_101402 baseEnd_101402 := by
    simpa [prefixWord, tailWord_101402, baseEnd_101402] using wordTrace_append hprefix tailTrace_101402
  have hstable : (prefixWord ++ tailWord_101402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101402).length < 2 ^ (prefixWord ++ tailWord_101402).sum := by decide
  have hdescent : baseEnd_101402 < baseStart_101402 := by decide
  rcases family_descends (prefixWord ++ tailWord_101402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101469 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 1, 6]
def baseStart_101469 : Nat := 118140960795 + 101469 * 2 ^ 59
def prefixEnd_101469 : Nat := 4983230072969 + 3 ^ 40 * 101469 * 2
def baseEnd_101469 : Nat := 17367456177056245256953

theorem tailTrace_101469 : CollatzResearch.WordTrace tailWord_101469 prefixEnd_101469 17367456177056245256953 := by
  unfold tailWord_101469
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700878469402617370635461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2467252312935078247090307 3700878469402617370635461)
  ·
    refine ⟨693914713012990756994149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3700878469402617370635461 693914713012990756994149)
    ·
      refine ⟨130109008689935766936403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 693914713012990756994149 130109008689935766936403)
      ·
        refine ⟨195163513034903650404605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130109008689935766936403 195163513034903650404605)
        ·
          refine ⟨73186317388088868901727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195163513034903650404605 73186317388088868901727)
          ·
            refine ⟨109779476082133303352591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73186317388088868901727 109779476082133303352591)
            ·
              refine ⟨164669214123199955028887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109779476082133303352591 164669214123199955028887)
              ·
                refine ⟨247003821184799932543331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164669214123199955028887 247003821184799932543331)
                ·
                  refine ⟨370505731777199898814997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247003821184799932543331 370505731777199898814997)
                  ·
                    refine ⟨17367456177056245256953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 370505731777199898814997 17367456177056245256953)
                    ·
                      rfl

theorem cell23_101469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_101469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101469 prefixEnd_101469 := by exact prefixLift 101469
  have htrace : WordTrace (prefixWord ++ tailWord_101469) baseStart_101469 baseEnd_101469 := by
    simpa [prefixWord, tailWord_101469, baseEnd_101469] using wordTrace_append hprefix tailTrace_101469
  have hstable : (prefixWord ++ tailWord_101469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101469).length < 2 ^ (prefixWord ++ tailWord_101469).sum := by decide
  have hdescent : baseEnd_101469 < baseStart_101469 := by decide
  rcases family_descends (prefixWord ++ tailWord_101469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101548 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 3]
def baseStart_101548 : Nat := 118140960795 + 101548 * 2 ^ 59
def prefixEnd_101548 : Nat := 4983230072969 + 3 ^ 40 * 101548 * 2
def baseEnd_101548 : Nat := 52142933502873926682995

theorem tailTrace_101548 : CollatzResearch.WordTrace tailWord_101548 prefixEnd_101548 52142933502873926682995 := by
  unfold tailWord_101548
  simp only [CollatzResearch.WordTrace]
  refine ⟨1851879918058206931380649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2469173224077609241840865 1851879918058206931380649)
  ·
    refine ⟨1388909938543655198535487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1851879918058206931380649 1388909938543655198535487)
    ·
      refine ⟨2083364907815482797803231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1388909938543655198535487 2083364907815482797803231)
      ·
        refine ⟨3125047361723224196704847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083364907815482797803231 3125047361723224196704847)
        ·
          refine ⟨4687571042584836295057271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125047361723224196704847 4687571042584836295057271)
          ·
            refine ⟨7031356563877254442585907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4687571042584836295057271 7031356563877254442585907)
            ·
              refine ⟨10547034845815881663878861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7031356563877254442585907 10547034845815881663878861)
              ·
                refine ⟨3955138067180955623954573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10547034845815881663878861 3955138067180955623954573)
                ·
                  refine ⟨1483176775192858358982965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3955138067180955623954573 1483176775192858358982965)
                  ·
                    refine ⟨139047822674330471154653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1483176775192858358982965 139047822674330471154653)
                    ·
                      refine ⟨52142933502873926682995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139047822674330471154653 52142933502873926682995)
                      ·
                        rfl

theorem cell23_101548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 3].length) (baseStart_101548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101548 prefixEnd_101548 := by exact prefixLift 101548
  have htrace : WordTrace (prefixWord ++ tailWord_101548) baseStart_101548 baseEnd_101548 := by
    simpa [prefixWord, tailWord_101548, baseEnd_101548] using wordTrace_append hprefix tailTrace_101548
  have hstable : (prefixWord ++ tailWord_101548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101548).length < 2 ^ (prefixWord ++ tailWord_101548).sum := by decide
  have hdescent : baseEnd_101548 < baseStart_101548 := by decide
  rcases family_descends (prefixWord ++ tailWord_101548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101549 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_101549 : Nat := 118140960795 + 101549 * 2 ^ 59
def prefixEnd_101549 : Nat := 4983230072969 + 3 ^ 40 * 101549 * 2
def baseEnd_101549 : Nat := 52143446983528422770491

theorem tailTrace_101549 : CollatzResearch.WordTrace tailWord_101549 prefixEnd_101549 52143446983528422770491 := by
  unfold tailWord_101549
  simp only [CollatzResearch.WordTrace]
  refine ⟨3703796309112791033547701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2469197539408527355698467 3703796309112791033547701)
  ·
    refine ⟨347230903979324159395097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3703796309112791033547701 347230903979324159395097)
    ·
      refine ⟨260423177984493119546323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 347230903979324159395097 260423177984493119546323)
      ·
        refine ⟨390634766976739679319485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 260423177984493119546323 390634766976739679319485)
        ·
          refine ⟨146488037616277379744807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 390634766976739679319485 146488037616277379744807)
          ·
            refine ⟨219732056424416069617211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146488037616277379744807 219732056424416069617211)
            ·
              refine ⟨329598084636624104425817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219732056424416069617211 329598084636624104425817)
              ·
                refine ⟨247198563477468078319363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 329598084636624104425817 247198563477468078319363)
                ·
                  refine ⟨370797845216202117479045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247198563477468078319363 370797845216202117479045)
                  ·
                    refine ⟨69524595978037897027321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 370797845216202117479045 69524595978037897027321)
                    ·
                      refine ⟨52143446983528422770491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69524595978037897027321 52143446983528422770491)
                      ·
                        rfl

theorem cell23_101549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_101549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101549 prefixEnd_101549 := by exact prefixLift 101549
  have htrace : WordTrace (prefixWord ++ tailWord_101549) baseStart_101549 baseEnd_101549 := by
    simpa [prefixWord, tailWord_101549, baseEnd_101549] using wordTrace_append hprefix tailTrace_101549
  have hstable : (prefixWord ++ tailWord_101549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101549).length < 2 ^ (prefixWord ++ tailWord_101549).sum := by decide
  have hdescent : baseEnd_101549 < baseStart_101549 := by decide
  rcases family_descends (prefixWord ++ tailWord_101549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101566 : List Nat := [4, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_101566 : Nat := 118140960795 + 101566 * 2 ^ 59
def prefixEnd_101566 : Nat := 4983230072969 + 3 ^ 40 * 101566 * 2
def baseEnd_101566 : Nat := 52152176154654856257913

theorem tailTrace_101566 : CollatzResearch.WordTrace tailWord_101566 prefixEnd_101566 52152176154654856257913 := by
  unfold tailWord_101566
  simp only [CollatzResearch.WordTrace]
  refine ⟨463052043756400367114569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2469610900034135291277701 463052043756400367114569)
  ·
    refine ⟨347289032817300275335927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 463052043756400367114569 347289032817300275335927)
    ·
      refine ⟨520933549225950413003891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 347289032817300275335927 520933549225950413003891)
      ·
        refine ⟨781400323838925619505837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 520933549225950413003891 781400323838925619505837)
        ·
          refine ⟨293025121439597107314689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 781400323838925619505837 293025121439597107314689)
          ·
            refine ⟨219768841079697830486017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293025121439597107314689 219768841079697830486017)
            ·
              refine ⟨164826630809773372864513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219768841079697830486017 164826630809773372864513)
              ·
                refine ⟨123619973107330029648385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 164826630809773372864513 123619973107330029648385)
                ·
                  refine ⟨92714979830497522236289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123619973107330029648385 92714979830497522236289)
                  ·
                    refine ⟨69536234872873141677217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92714979830497522236289 69536234872873141677217)
                    ·
                      refine ⟨52152176154654856257913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69536234872873141677217 52152176154654856257913)
                      ·
                        rfl

theorem cell23_101566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_101566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101566 prefixEnd_101566 := by exact prefixLift 101566
  have htrace : WordTrace (prefixWord ++ tailWord_101566) baseStart_101566 baseEnd_101566 := by
    simpa [prefixWord, tailWord_101566, baseEnd_101566] using wordTrace_append hprefix tailTrace_101566
  have hstable : (prefixWord ++ tailWord_101566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101566).length < 2 ^ (prefixWord ++ tailWord_101566).sum := by decide
  have hdescent : baseEnd_101566 < baseStart_101566 := by decide
  rcases family_descends (prefixWord ++ tailWord_101566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101582 : List Nat := [4, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_101582 : Nat := 118140960795 + 101582 * 2 ^ 59
def prefixEnd_101582 : Nat := 4983230072969 + 3 ^ 40 * 101582 * 2
def baseEnd_101582 : Nat := 52160391845126793657839

theorem tailTrace_101582 : CollatzResearch.WordTrace tailWord_101582 prefixEnd_101582 52160391845126793657839 := by
  unfold tailWord_101582
  simp only [CollatzResearch.WordTrace]
  refine ⟨463124989749154708687375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2469999945328825112999333 463124989749154708687375)
  ·
    refine ⟨694687484623732063031063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 463124989749154708687375 694687484623732063031063)
    ·
      refine ⟨1042031226935598094546595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694687484623732063031063 1042031226935598094546595)
      ·
        refine ⟨1563046840403397141819893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042031226935598094546595 1563046840403397141819893)
        ·
          refine ⟨146535641287818482045615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1563046840403397141819893 146535641287818482045615)
          ·
            refine ⟨219803461931727723068423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146535641287818482045615 219803461931727723068423)
            ·
              refine ⟨329705192897591584602635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 219803461931727723068423 329705192897591584602635)
              ·
                refine ⟨494557789346387376903953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 329705192897591584602635 494557789346387376903953)
                ·
                  refine ⟨370918342009790532677965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 494557789346387376903953 370918342009790532677965)
                  ·
                    refine ⟨139094378253671449754237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 370918342009790532677965 139094378253671449754237)
                    ·
                      refine ⟨52160391845126793657839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139094378253671449754237 52160391845126793657839)
                      ·
                        rfl

theorem cell23_101582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_101582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101582 prefixEnd_101582 := by exact prefixLift 101582
  have htrace : WordTrace (prefixWord ++ tailWord_101582) baseStart_101582 baseEnd_101582 := by
    simpa [prefixWord, tailWord_101582, baseEnd_101582] using wordTrace_append hprefix tailTrace_101582
  have hstable : (prefixWord ++ tailWord_101582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101582).length < 2 ^ (prefixWord ++ tailWord_101582).sum := by decide
  have hdescent : baseEnd_101582 < baseStart_101582 := by decide
  rcases family_descends (prefixWord ++ tailWord_101582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101625 : List Nat := [1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 3]
def baseStart_101625 : Nat := 118140960795 + 101625 * 2 ^ 59
def prefixEnd_101625 : Nat := 4983230072969 + 3 ^ 40 * 101625 * 2
def baseEnd_101625 : Nat := 52182471513270125420141

theorem tailTrace_101625 : CollatzResearch.WordTrace tailWord_101625 prefixEnd_101625 52182471513270125420141 := by
  unfold tailWord_101625
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706568256837456013314329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2471045504558304008876219 3706568256837456013314329)
  ·
    refine ⟨2779926192628092009985747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3706568256837456013314329 2779926192628092009985747)
    ·
      refine ⟨4169889288942138014978621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2779926192628092009985747 4169889288942138014978621)
      ·
        refine ⟨1563708483353301755616983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4169889288942138014978621 1563708483353301755616983)
        ·
          refine ⟨2345562725029952633425475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1563708483353301755616983 2345562725029952633425475)
          ·
            refine ⟨3518344087544928950138213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2345562725029952633425475 3518344087544928950138213)
            ·
              refine ⟨659689516414674178150915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3518344087544928950138213 659689516414674178150915)
              ·
                refine ⟨989534274622011267226373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 659689516414674178150915 989534274622011267226373)
                ·
                  refine ⟨185537676491627112604945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 989534274622011267226373 185537676491627112604945)
                  ·
                    refine ⟨139153257368720334453709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 185537676491627112604945 139153257368720334453709)
                    ·
                      refine ⟨52182471513270125420141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139153257368720334453709 52182471513270125420141)
                      ·
                        rfl

theorem cell23_101625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_101625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101625 prefixEnd_101625 := by exact prefixLift 101625
  have htrace : WordTrace (prefixWord ++ tailWord_101625) baseStart_101625 baseEnd_101625 := by
    simpa [prefixWord, tailWord_101625, baseEnd_101625] using wordTrace_append hprefix tailTrace_101625
  have hstable : (prefixWord ++ tailWord_101625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101625).length < 2 ^ (prefixWord ++ tailWord_101625).sum := by decide
  have hdescent : baseEnd_101625 < baseStart_101625 := by decide
  rcases family_descends (prefixWord ++ tailWord_101625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101655 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 3]
def baseStart_101655 : Nat := 118140960795 + 101655 * 2 ^ 59
def prefixEnd_101655 : Nat := 4983230072969 + 3 ^ 40 * 101655 * 2
def baseEnd_101655 : Nat := 52197875932905008045003

theorem tailTrace_101655 : CollatzResearch.WordTrace tailWord_101655 prefixEnd_101655 52197875932905008045003 := by
  unfold tailWord_101655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707662446728771136906419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2471774964485847424604279 3707662446728771136906419)
  ·
    refine ⟨5561493670093156705359629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707662446728771136906419 5561493670093156705359629)
    ·
      refine ⟨2085560126284933764509861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5561493670093156705359629 2085560126284933764509861)
      ·
        refine ⟨391042523678425080845599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2085560126284933764509861 391042523678425080845599)
        ·
          refine ⟨586563785517637621268399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391042523678425080845599 586563785517637621268399)
          ·
            refine ⟨879845678276456431902599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586563785517637621268399 879845678276456431902599)
            ·
              refine ⟨1319768517414684647853899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879845678276456431902599 1319768517414684647853899)
              ·
                refine ⟨1979652776122026971780849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1319768517414684647853899 1979652776122026971780849)
                ·
                  refine ⟨1484739582091520228835637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1979652776122026971780849 1484739582091520228835637)
                  ·
                    refine ⟨139194335821080021453341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1484739582091520228835637 139194335821080021453341)
                    ·
                      refine ⟨52197875932905008045003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139194335821080021453341 52197875932905008045003)
                      ·
                        rfl

theorem cell23_101655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_101655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101655 prefixEnd_101655 := by exact prefixLift 101655
  have htrace : WordTrace (prefixWord ++ tailWord_101655) baseStart_101655 baseEnd_101655 := by
    simpa [prefixWord, tailWord_101655, baseEnd_101655] using wordTrace_append hprefix tailTrace_101655
  have hstable : (prefixWord ++ tailWord_101655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101655).length < 2 ^ (prefixWord ++ tailWord_101655).sum := by decide
  have hdescent : baseEnd_101655 < baseStart_101655 := by decide
  rcases family_descends (prefixWord ++ tailWord_101655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101732 : List Nat := [2, 3, 1, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_101732 : Nat := 118140960795 + 101732 * 2 ^ 59
def prefixEnd_101732 : Nat := 4983230072969 + 3 ^ 40 * 101732 * 2
def baseEnd_101732 : Nat := 52237413943301206782149

theorem tailTrace_101732 : CollatzResearch.WordTrace tailWord_101732 prefixEnd_101732 52237413943301206782149 := by
  unfold tailWord_101732
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855235433724906643729725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2473647244966542191639633 1855235433724906643729725)
  ·
    refine ⟨695713287646839991398647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1855235433724906643729725 695713287646839991398647)
    ·
      refine ⟨1043569931470259987097971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 695713287646839991398647 1043569931470259987097971)
      ·
        refine ⟨1565354897205389980646957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043569931470259987097971 1565354897205389980646957)
        ·
          refine ⟨587008086452021242742609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1565354897205389980646957 587008086452021242742609)
          ·
            refine ⟨440256064839015932056957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587008086452021242742609 440256064839015932056957)
            ·
              refine ⟨165096024314630974521359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 440256064839015932056957 165096024314630974521359)
              ·
                refine ⟨247644036471946461782039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165096024314630974521359 247644036471946461782039)
                ·
                  refine ⟨371466054707919692673059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 247644036471946461782039 371466054707919692673059)
                  ·
                    refine ⟨557199082061879539009589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371466054707919692673059 557199082061879539009589)
                    ·
                      refine ⟨52237413943301206782149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 557199082061879539009589 52237413943301206782149)
                      ·
                        rfl

theorem cell23_101732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_101732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101732 prefixEnd_101732 := by exact prefixLift 101732
  have htrace : WordTrace (prefixWord ++ tailWord_101732) baseStart_101732 baseEnd_101732 := by
    simpa [prefixWord, tailWord_101732, baseEnd_101732] using wordTrace_append hprefix tailTrace_101732
  have hstable : (prefixWord ++ tailWord_101732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101732).length < 2 ^ (prefixWord ++ tailWord_101732).sum := by decide
  have hdescent : baseEnd_101732 < baseStart_101732 := by decide
  rcases family_descends (prefixWord ++ tailWord_101732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101735 : List Nat := [1, 1, 5, 1, 4, 11]
def baseStart_101735 : Nat := 118140960795 + 101735 * 2 ^ 59
def prefixEnd_101735 : Nat := 4983230072969 + 3 ^ 40 * 101735 * 2
def baseEnd_101735 : Nat := 214975120927015205945

theorem tailTrace_101735 : CollatzResearch.WordTrace tailWord_101735 prefixEnd_101735 214975120927015205945 := by
  unfold tailWord_101735
  simp only [CollatzResearch.WordTrace]
  refine ⟨3710580286438944799818659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2473720190959296533212439 3710580286438944799818659)
  ·
    refine ⟨5565870429658417199727989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3710580286438944799818659 5565870429658417199727989)
    ·
      refine ⟨521800352780476612474499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5565870429658417199727989 521800352780476612474499)
      ·
        refine ⟨782700529170714918711749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521800352780476612474499 782700529170714918711749)
        ·
          refine ⟨146756349219509047258453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 782700529170714918711749 146756349219509047258453)
          ·
            refine ⟨214975120927015205945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 146756349219509047258453 214975120927015205945)
            ·
              rfl

theorem cell23_101735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 11].length) (baseStart_101735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101735 prefixEnd_101735 := by exact prefixLift 101735
  have htrace : WordTrace (prefixWord ++ tailWord_101735) baseStart_101735 baseEnd_101735 := by
    simpa [prefixWord, tailWord_101735, baseEnd_101735] using wordTrace_append hprefix tailTrace_101735
  have hstable : (prefixWord ++ tailWord_101735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101735).length < 2 ^ (prefixWord ++ tailWord_101735).sum := by decide
  have hdescent : baseEnd_101735 < baseStart_101735 := by decide
  rcases family_descends (prefixWord ++ tailWord_101735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101780 : List Nat := [2, 4, 2, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_101780 : Nat := 118140960795 + 101780 * 2 ^ 59
def prefixEnd_101780 : Nat := 4983230072969 + 3 ^ 40 * 101780 * 2
def baseEnd_101780 : Nat := 52262061014717018981929

theorem tailTrace_101780 : CollatzResearch.WordTrace tailWord_101780 prefixEnd_101780 52262061014717018981929 := by
  unfold tailWord_101780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1856110785637958742603397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2474814380850611656804529 1856110785637958742603397)
  ·
    refine ⟨348020772307117264238137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1856110785637958742603397 348020772307117264238137)
    ·
      refine ⟨261015579230337948178603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348020772307117264238137 261015579230337948178603)
      ·
        refine ⟨391523368845506922267905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261015579230337948178603 391523368845506922267905)
        ·
          refine ⟨293642526634130191700929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391523368845506922267905 293642526634130191700929)
          ·
            refine ⟨220231894975597643775697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293642526634130191700929 220231894975597643775697)
            ·
              refine ⟨165173921231698232831773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220231894975597643775697 165173921231698232831773)
              ·
                refine ⟨61940220461886837311915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165173921231698232831773 61940220461886837311915)
                ·
                  refine ⟨92910330692830255967873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61940220461886837311915 92910330692830255967873)
                  ·
                    refine ⟨69682748019622691975905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92910330692830255967873 69682748019622691975905)
                    ·
                      refine ⟨52262061014717018981929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69682748019622691975905 52262061014717018981929)
                      ·
                        rfl

theorem cell23_101780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_101780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101780 prefixEnd_101780 := by exact prefixLift 101780
  have htrace : WordTrace (prefixWord ++ tailWord_101780) baseStart_101780 baseEnd_101780 := by
    simpa [prefixWord, tailWord_101780, baseEnd_101780] using wordTrace_append hprefix tailTrace_101780
  have hstable : (prefixWord ++ tailWord_101780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101780).length < 2 ^ (prefixWord ++ tailWord_101780).sum := by decide
  have hdescent : baseEnd_101780 < baseStart_101780 := by decide
  rcases family_descends (prefixWord ++ tailWord_101780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101790 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_101790 : Nat := 118140960795 + 101790 * 2 ^ 59
def prefixEnd_101790 : Nat := 4983230072969 + 3 ^ 40 * 101790 * 2
def baseEnd_101790 : Nat := 17422398607087326618961

theorem tailTrace_101790 : CollatzResearch.WordTrace tailWord_101790 prefixEnd_101790 17422398607087326618961 := by
  unfold tailWord_101790
  simp only [CollatzResearch.WordTrace]
  refine ⟨464073287654961149133853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2475057534159792795380549 464073287654961149133853)
  ·
    refine ⟨174027482870610430925195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 464073287654961149133853 174027482870610430925195)
    ·
      refine ⟨261041224305915646387793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174027482870610430925195 261041224305915646387793)
      ·
        refine ⟨195780918229436734790845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261041224305915646387793 195780918229436734790845)
        ·
          refine ⟨73417844336038775546567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 195780918229436734790845 73417844336038775546567)
          ·
            refine ⟨110126766504058163319851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73417844336038775546567 110126766504058163319851)
            ·
              refine ⟨165190149756087244979777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110126766504058163319851 165190149756087244979777)
              ·
                refine ⟨123892612317065433734833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 165190149756087244979777 123892612317065433734833)
                ·
                  refine ⟨92919459237799075301125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123892612317065433734833 92919459237799075301125)
                  ·
                    refine ⟨17422398607087326618961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92919459237799075301125 17422398607087326618961)
                    ·
                      rfl

theorem cell23_101790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_101790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101790 prefixEnd_101790 := by exact prefixLift 101790
  have htrace : WordTrace (prefixWord ++ tailWord_101790) baseStart_101790 baseEnd_101790 := by
    simpa [prefixWord, tailWord_101790, baseEnd_101790] using wordTrace_append hprefix tailTrace_101790
  have hstable : (prefixWord ++ tailWord_101790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101790).length < 2 ^ (prefixWord ++ tailWord_101790).sum := by decide
  have hdescent : baseEnd_101790 < baseStart_101790 := by decide
  rcases family_descends (prefixWord ++ tailWord_101790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101795 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 4, 6]
def baseStart_101795 : Nat := 118140960795 + 101795 * 2 ^ 59
def prefixEnd_101795 : Nat := 4983230072969 + 3 ^ 40 * 101795 * 2
def baseEnd_101795 : Nat := 17423254408178153431453

theorem tailTrace_101795 : CollatzResearch.WordTrace tailWord_101795 prefixEnd_101795 17423254408178153431453 := by
  unfold tailWord_101795
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712768666221575047002839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2475179110814383364668559 3712768666221575047002839)
  ·
    refine ⟨5569152999332362570504259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712768666221575047002839 5569152999332362570504259)
    ·
      refine ⟨8353729498998543855756389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5569152999332362570504259 8353729498998543855756389)
      ·
        refine ⟨1566324281062226972954323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8353729498998543855756389 1566324281062226972954323)
        ·
          refine ⟨2349486421593340459431485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1566324281062226972954323 2349486421593340459431485)
          ·
            refine ⟨881057408097502672286807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2349486421593340459431485 881057408097502672286807)
            ·
              refine ⟨1321586112146254008430211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881057408097502672286807 1321586112146254008430211)
              ·
                refine ⟨1982379168219381012645317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1321586112146254008430211 1982379168219381012645317)
                ·
                  refine ⟨371696094041133939870997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1982379168219381012645317 371696094041133939870997)
                  ·
                    refine ⟨17423254408178153431453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 371696094041133939870997 17423254408178153431453)
                    ·
                      rfl

theorem cell23_101795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 6].length) (baseStart_101795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101795 prefixEnd_101795 := by exact prefixLift 101795
  have htrace : WordTrace (prefixWord ++ tailWord_101795) baseStart_101795 baseEnd_101795 := by
    simpa [prefixWord, tailWord_101795, baseEnd_101795] using wordTrace_append hprefix tailTrace_101795
  have hstable : (prefixWord ++ tailWord_101795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101795).length < 2 ^ (prefixWord ++ tailWord_101795).sum := by decide
  have hdescent : baseEnd_101795 < baseStart_101795 := by decide
  rcases family_descends (prefixWord ++ tailWord_101795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101813 : List Nat := [1, 3, 3, 2, 2, 2, 3, 1, 2, 1, 3]
def baseStart_101813 : Nat := 118140960795 + 101813 * 2 ^ 59
def prefixEnd_101813 : Nat := 4983230072969 + 3 ^ 40 * 101813 * 2
def baseEnd_101813 : Nat := 52279005876315389869277

theorem tailTrace_101813 : CollatzResearch.WordTrace tailWord_101813 prefixEnd_101813 52279005876315389869277 := by
  unfold tailWord_101813
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713425180156364121158093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2475616786770909414105395 3713425180156364121158093)
  ·
    refine ⟨1392534442558636545434285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3713425180156364121158093 1392534442558636545434285)
    ·
      refine ⟨522200415959488704537857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1392534442558636545434285 522200415959488704537857)
      ·
        refine ⟨391650311969616528403393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 522200415959488704537857 391650311969616528403393)
        ·
          refine ⟨293737733977212396302545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391650311969616528403393 293737733977212396302545)
          ·
            refine ⟨220303300482909297226909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 293737733977212396302545 220303300482909297226909)
            ·
              refine ⟨82613737681090986460091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220303300482909297226909 82613737681090986460091)
              ·
                refine ⟨123920606521636479690137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82613737681090986460091 123920606521636479690137)
                ·
                  refine ⟨92940454891227359767603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 123920606521636479690137 92940454891227359767603)
                  ·
                    refine ⟨139410682336841039651405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92940454891227359767603 139410682336841039651405)
                    ·
                      refine ⟨52279005876315389869277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139410682336841039651405 52279005876315389869277)
                      ·
                        rfl

theorem cell23_101813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_101813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101813 prefixEnd_101813 := by exact prefixLift 101813
  have htrace : WordTrace (prefixWord ++ tailWord_101813) baseStart_101813 baseEnd_101813 := by
    simpa [prefixWord, tailWord_101813, baseEnd_101813] using wordTrace_append hprefix tailTrace_101813
  have hstable : (prefixWord ++ tailWord_101813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101813).length < 2 ^ (prefixWord ++ tailWord_101813).sum := by decide
  have hdescent : baseEnd_101813 < baseStart_101813 := by decide
  rcases family_descends (prefixWord ++ tailWord_101813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101822 : List Nat := [4, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_101822 : Nat := 118140960795 + 101822 * 2 ^ 59
def prefixEnd_101822 : Nat := 4983230072969 + 3 ^ 40 * 101822 * 2
def baseEnd_101822 : Nat := 52283627202205854656735

theorem tailTrace_101822 : CollatzResearch.WordTrace tailWord_101822 prefixEnd_101822 52283627202205854656735 := by
  unfold tailWord_101822
  simp only [CollatzResearch.WordTrace]
  refine ⟨464219179640469832279465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2475835624749172438823813 464219179640469832279465)
  ·
    refine ⟨348164384730352374209599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 464219179640469832279465 348164384730352374209599)
    ·
      refine ⟨522246577095528561314399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348164384730352374209599 522246577095528561314399)
      ·
        refine ⟨783369865643292841971599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522246577095528561314399 783369865643292841971599)
        ·
          refine ⟨1175054798464939262957399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783369865643292841971599 1175054798464939262957399)
          ·
            refine ⟨1762582197697408894436099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175054798464939262957399 1762582197697408894436099)
            ·
              refine ⟨2643873296546113341654149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1762582197697408894436099 2643873296546113341654149)
              ·
                refine ⟨495726243102396251560153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2643873296546113341654149 495726243102396251560153)
                ·
                  refine ⟨371794682326797188670115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 495726243102396251560153 371794682326797188670115)
                  ·
                    refine ⟨557692023490195783005173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 371794682326797188670115 557692023490195783005173)
                    ·
                      refine ⟨52283627202205854656735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 557692023490195783005173 52283627202205854656735)
                      ·
                        rfl

theorem cell23_101822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_101822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101822 prefixEnd_101822 := by exact prefixLift 101822
  have htrace : WordTrace (prefixWord ++ tailWord_101822) baseStart_101822 baseEnd_101822 := by
    simpa [prefixWord, tailWord_101822, baseEnd_101822] using wordTrace_append hprefix tailTrace_101822
  have hstable : (prefixWord ++ tailWord_101822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101822).length < 2 ^ (prefixWord ++ tailWord_101822).sum := by decide
  have hdescent : baseEnd_101822 < baseStart_101822 := by decide
  rcases family_descends (prefixWord ++ tailWord_101822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101836 : List Nat := [2, 2, 1, 4, 2, 1, 1, 2, 4, 2, 2]
def baseStart_101836 : Nat := 118140960795 + 101836 * 2 ^ 59
def prefixEnd_101836 : Nat := 4983230072969 + 3 ^ 40 * 101836 * 2
def baseEnd_101836 : Nat := 52290815931368799881671

theorem tailTrace_101836 : CollatzResearch.WordTrace tailWord_101836 prefixEnd_101836 52290815931368799881671 := by
  unfold tailWord_101836
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857132029536519524622681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2476176039382026032830241 1857132029536519524622681)
  ·
    refine ⟨1392849022152389643467011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1857132029536519524622681 1392849022152389643467011)
    ·
      refine ⟨2089273533228584465200517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1392849022152389643467011 2089273533228584465200517)
      ·
        refine ⟨391738787480359587225097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2089273533228584465200517 391738787480359587225097)
        ·
          refine ⟨293804090610269690418823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391738787480359587225097 293804090610269690418823)
          ·
            refine ⟨440706135915404535628235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 293804090610269690418823 440706135915404535628235)
            ·
              refine ⟨661059203873106803442353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440706135915404535628235 661059203873106803442353)
              ·
                refine ⟨495794402904830102581765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 661059203873106803442353 495794402904830102581765)
                ·
                  refine ⟨92961450544655644234081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 495794402904830102581765 92961450544655644234081)
                  ·
                    refine ⟨69721087908491733175561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92961450544655644234081 69721087908491733175561)
                    ·
                      refine ⟨52290815931368799881671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69721087908491733175561 52290815931368799881671)
                      ·
                        rfl

theorem cell23_101836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_101836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101836 prefixEnd_101836 := by exact prefixLift 101836
  have htrace : WordTrace (prefixWord ++ tailWord_101836) baseStart_101836 baseEnd_101836 := by
    simpa [prefixWord, tailWord_101836, baseEnd_101836] using wordTrace_append hprefix tailTrace_101836
  have hstable : (prefixWord ++ tailWord_101836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101836).length < 2 ^ (prefixWord ++ tailWord_101836).sum := by decide
  have hdescent : baseEnd_101836 < baseStart_101836 := by decide
  rcases family_descends (prefixWord ++ tailWord_101836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101859 : List Nat := [1, 1, 1, 6, 2, 3, 1, 1, 7]
def baseStart_101859 : Nat := 118140960795 + 101859 * 2 ^ 59
def prefixEnd_101859 : Nat := 4983230072969 + 3 ^ 40 * 101859 * 2
def baseEnd_101859 : Nat := 5811402887380245543785

theorem tailTrace_101859 : CollatzResearch.WordTrace tailWord_101859 prefixEnd_101859 5811402887380245543785 := by
  unfold tailWord_101859
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715102937989713977332631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2476735291993142651555087 3715102937989713977332631)
  ·
    refine ⟨5572654406984570965998947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3715102937989713977332631 5572654406984570965998947)
    ·
      refine ⟨8358981610476856448998421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572654406984570965998947 8358981610476856448998421)
      ·
        refine ⟨391827262991102646046801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8358981610476856448998421 391827262991102646046801)
        ·
          refine ⟨293870447243326984535101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 391827262991102646046801 293870447243326984535101)
          ·
            refine ⟨110201417716247619200663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 293870447243326984535101 110201417716247619200663)
            ·
              refine ⟨165302126574371428800995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110201417716247619200663 165302126574371428800995)
              ·
                refine ⟨247953189861557143201493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165302126574371428800995 247953189861557143201493)
                ·
                  refine ⟨5811402887380245543785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 247953189861557143201493 5811402887380245543785)
                  ·
                    rfl

theorem cell23_101859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 1, 7].length) (baseStart_101859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101859 prefixEnd_101859 := by exact prefixLift 101859
  have htrace : WordTrace (prefixWord ++ tailWord_101859) baseStart_101859 baseEnd_101859 := by
    simpa [prefixWord, tailWord_101859, baseEnd_101859] using wordTrace_append hprefix tailTrace_101859
  have hstable : (prefixWord ++ tailWord_101859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101859).length < 2 ^ (prefixWord ++ tailWord_101859).sum := by decide
  have hdescent : baseEnd_101859 < baseStart_101859 := by decide
  rcases family_descends (prefixWord ++ tailWord_101859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101909 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 4]
def baseStart_101909 : Nat := 118140960795 + 101909 * 2 ^ 59
def prefixEnd_101909 : Nat := 4983230072969 + 3 ^ 40 * 101909 * 2
def baseEnd_101909 : Nat := 52328300019147014268835

theorem tailTrace_101909 : CollatzResearch.WordTrace tailWord_101909 prefixEnd_101909 52328300019147014268835 := by
  unfold tailWord_101909
  simp only [CollatzResearch.WordTrace]
  refine ⟨3716926587808572516652781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2477951058539048344435187 3716926587808572516652781)
  ·
    refine ⟨1393847470428214693744793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3716926587808572516652781 1393847470428214693744793)
    ·
      refine ⟨1045385602821161020308595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1393847470428214693744793 1045385602821161020308595)
      ·
        refine ⟨1568078404231741530462893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045385602821161020308595 1568078404231741530462893)
        ·
          refine ⟨588029401586903073923585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1568078404231741530462893 588029401586903073923585)
          ·
            refine ⟨441022051190177305442689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588029401586903073923585 441022051190177305442689)
            ·
              refine ⟨330766538392632979082017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441022051190177305442689 330766538392632979082017)
              ·
                refine ⟨248074903794474734311513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 330766538392632979082017 248074903794474734311513)
                ·
                  refine ⟨186056177845856050733635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248074903794474734311513 186056177845856050733635)
                  ·
                    refine ⟨279084266768784076100453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 186056177845856050733635 279084266768784076100453)
                    ·
                      refine ⟨52328300019147014268835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 279084266768784076100453 52328300019147014268835)
                      ·
                        rfl

theorem cell23_101909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_101909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101909 prefixEnd_101909 := by exact prefixLift 101909
  have htrace : WordTrace (prefixWord ++ tailWord_101909) baseStart_101909 baseEnd_101909 := by
    simpa [prefixWord, tailWord_101909, baseEnd_101909] using wordTrace_append hprefix tailTrace_101909
  have hstable : (prefixWord ++ tailWord_101909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101909).length < 2 ^ (prefixWord ++ tailWord_101909).sum := by decide
  have hdescent : baseEnd_101909 < baseStart_101909 := by decide
  rcases family_descends (prefixWord ++ tailWord_101909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101953 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 1, 4]
def baseStart_101953 : Nat := 118140960795 + 101953 * 2 ^ 59
def prefixEnd_101953 : Nat := 4983230072969 + 3 ^ 40 * 101953 * 2
def baseEnd_101953 : Nat := 17450297722648280706211

theorem tailTrace_101953 : CollatzResearch.WordTrace tailWord_101953 prefixEnd_101953 17450297722648280706211 := by
  unfold tailWord_101953
  simp only [CollatzResearch.WordTrace]
  refine ⟨3718531399649168031254513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2479020933099445354169675 3718531399649168031254513)
  ·
    refine ⟨2788898549736876023440885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3718531399649168031254513 2788898549736876023440885)
    ·
      refine ⟨261459239037832127197583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2788898549736876023440885 261459239037832127197583)
      ·
        refine ⟨392188858556748190796375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261459239037832127197583 392188858556748190796375)
        ·
          refine ⟨588283287835122286194563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392188858556748190796375 588283287835122286194563)
          ·
            refine ⟨882424931752683429291845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588283287835122286194563 882424931752683429291845)
            ·
              refine ⟨165454674703628142992221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 882424931752683429291845 165454674703628142992221)
              ·
                refine ⟨62045503013860553622083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165454674703628142992221 62045503013860553622083)
                ·
                  refine ⟨93068254520790830433125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62045503013860553622083 93068254520790830433125)
                  ·
                    refine ⟨17450297722648280706211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93068254520790830433125 17450297722648280706211)
                    ·
                      rfl

theorem cell23_101953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_101953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101953 prefixEnd_101953 := by exact prefixLift 101953
  have htrace : WordTrace (prefixWord ++ tailWord_101953) baseStart_101953 baseEnd_101953 := by
    simpa [prefixWord, tailWord_101953, baseEnd_101953] using wordTrace_append hprefix tailTrace_101953
  have hstable : (prefixWord ++ tailWord_101953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101953).length < 2 ^ (prefixWord ++ tailWord_101953).sum := by decide
  have hdescent : baseEnd_101953 < baseStart_101953 := by decide
  rcases family_descends (prefixWord ++ tailWord_101953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_101999 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 1, 8, 2]
def baseStart_101999 : Nat := 118140960795 + 101999 * 2 ^ 59
def prefixEnd_101999 : Nat := 4983230072969 + 3 ^ 40 * 101999 * 2
def baseEnd_101999 : Nat := 52374513278051662143421

theorem tailTrace_101999 : CollatzResearch.WordTrace tailWord_101999 prefixEnd_101999 52374513278051662143421 := by
  unfold tailWord_101999
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720209157482517887429051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2480139438321678591619367 3720209157482517887429051)
  ·
    refine ⟨5580313736223776831143577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720209157482517887429051 5580313736223776831143577)
    ·
      refine ⟨4185235302167832623357683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5580313736223776831143577 4185235302167832623357683)
      ·
        refine ⟨6277852953251748935036525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4185235302167832623357683 6277852953251748935036525)
        ·
          refine ⟨2354194857469405850638697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6277852953251748935036525 2354194857469405850638697)
          ·
            refine ⟨1765646143102054387979023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2354194857469405850638697 1765646143102054387979023)
            ·
              refine ⟨2648469214653081581968535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765646143102054387979023 2648469214653081581968535)
              ·
                refine ⟨3972703821979622372952803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2648469214653081581968535 3972703821979622372952803)
                ·
                  refine ⟨5959055732969433559429205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3972703821979622372952803 5959055732969433559429205)
                  ·
                    refine ⟨69832684370735549524561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5959055732969433559429205 69832684370735549524561)
                    ·
                      refine ⟨52374513278051662143421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 69832684370735549524561 52374513278051662143421)
                      ·
                        rfl

theorem cell23_101999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 8, 2].length) (baseStart_101999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_101999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_101999 prefixEnd_101999 := by exact prefixLift 101999
  have htrace : WordTrace (prefixWord ++ tailWord_101999) baseStart_101999 baseEnd_101999 := by
    simpa [prefixWord, tailWord_101999, baseEnd_101999] using wordTrace_append hprefix tailTrace_101999
  have hstable : (prefixWord ++ tailWord_101999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_101999).length < 2 ^ (prefixWord ++ tailWord_101999).sum := by decide
  have hdescent : baseEnd_101999 < baseStart_101999 := by decide
  rcases family_descends (prefixWord ++ tailWord_101999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102009 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 6, 4]
def baseStart_102009 : Nat := 118140960795 + 102009 * 2 ^ 59
def prefixEnd_102009 : Nat := 4983230072969 + 3 ^ 40 * 102009 * 2
def baseEnd_102009 : Nat := 17459882694865541006125

theorem tailTrace_102009 : CollatzResearch.WordTrace tailWord_102009 prefixEnd_102009 17459882694865541006125 := by
  unfold tailWord_102009
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720573887446289595293081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2480382591630859730195387 3720573887446289595293081)
  ·
    refine ⟨2790430415584717196469811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3720573887446289595293081 2790430415584717196469811)
    ·
      refine ⟨4185645623377075794704717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2790430415584717196469811 4185645623377075794704717)
      ·
        refine ⟨1569617108766403423014269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4185645623377075794704717 1569617108766403423014269)
        ·
          refine ⟨588606415787401283630351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1569617108766403423014269 588606415787401283630351)
          ·
            refine ⟨882909623681101925445527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588606415787401283630351 882909623681101925445527)
            ·
              refine ⟨1324364435521652888168291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882909623681101925445527 1324364435521652888168291)
              ·
                refine ⟨1986546653282479332252437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1324364435521652888168291 1986546653282479332252437)
                ·
                  refine ⟨93119374372616218699333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1986546653282479332252437 93119374372616218699333)
                  ·
                    refine ⟨17459882694865541006125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93119374372616218699333 17459882694865541006125)
                    ·
                      rfl

theorem cell23_102009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 4].length) (baseStart_102009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102009 prefixEnd_102009 := by exact prefixLift 102009
  have htrace : WordTrace (prefixWord ++ tailWord_102009) baseStart_102009 baseEnd_102009 := by
    simpa [prefixWord, tailWord_102009, baseEnd_102009] using wordTrace_append hprefix tailTrace_102009
  have hstable : (prefixWord ++ tailWord_102009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102009).length < 2 ^ (prefixWord ++ tailWord_102009).sum := by decide
  have hdescent : baseEnd_102009 < baseStart_102009 := by decide
  rcases family_descends (prefixWord ++ tailWord_102009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102019 : List Nat := [1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 3]
def baseStart_102019 : Nat := 118140960795 + 102019 * 2 ^ 59
def prefixEnd_102019 : Nat := 4983230072969 + 3 ^ 40 * 102019 * 2
def baseEnd_102019 : Nat := 52384782891141583893329

theorem tailTrace_102019 : CollatzResearch.WordTrace tailWord_102019 prefixEnd_102019 52384782891141583893329 := by
  unfold tailWord_102019
  simp only [CollatzResearch.WordTrace]
  refine ⟨3720938617410061303157111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2480625744940040868771407 3720938617410061303157111)
  ·
    refine ⟨5581407926115091954735667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3720938617410061303157111 5581407926115091954735667)
    ·
      refine ⟨8372111889172637932103501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5581407926115091954735667 8372111889172637932103501)
      ·
        refine ⟨3139541958439739224538813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8372111889172637932103501 3139541958439739224538813)
        ·
          refine ⟨1177328234414902209202055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3139541958439739224538813 1177328234414902209202055)
          ·
            refine ⟨1765992351622353313803083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177328234414902209202055 1765992351622353313803083)
            ·
              refine ⟨2648988527433529970704625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765992351622353313803083 2648988527433529970704625)
              ·
                refine ⟨1986741395575147478028469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2648988527433529970704625 1986741395575147478028469)
                ·
                  refine ⟨186257005835170076065169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1986741395575147478028469 186257005835170076065169)
                  ·
                    refine ⟨139692754376377557048877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186257005835170076065169 139692754376377557048877)
                    ·
                      refine ⟨52384782891141583893329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139692754376377557048877 52384782891141583893329)
                      ·
                        rfl

theorem cell23_102019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_102019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102019 prefixEnd_102019 := by exact prefixLift 102019
  have htrace : WordTrace (prefixWord ++ tailWord_102019) baseStart_102019 baseEnd_102019 := by
    simpa [prefixWord, tailWord_102019, baseEnd_102019] using wordTrace_append hprefix tailTrace_102019
  have hstable : (prefixWord ++ tailWord_102019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102019).length < 2 ^ (prefixWord ++ tailWord_102019).sum := by decide
  have hdescent : baseEnd_102019 < baseStart_102019 := by decide
  rcases family_descends (prefixWord ++ tailWord_102019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102026 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 4, 4]
def baseStart_102026 : Nat := 118140960795 + 102026 * 2 ^ 59
def prefixEnd_102026 : Nat := 4983230072969 + 3 ^ 40 * 102026 * 2
def baseEnd_102026 : Nat := 17462792418574352168599

theorem tailTrace_102026 : CollatzResearch.WordTrace tailWord_102026 prefixEnd_102026 17462792418574352168599 := by
  unfold tailWord_102026
  simp only [CollatzResearch.WordTrace]
  refine ⟨930298482096175374665483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2480795952256467665774621 930298482096175374665483)
  ·
    refine ⟨1395447723144263061998225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 930298482096175374665483 1395447723144263061998225)
    ·
      refine ⟨1046585792358197296498669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1395447723144263061998225 1046585792358197296498669)
      ·
        refine ⟨392469672134323986187001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1046585792358197296498669 392469672134323986187001)
        ·
          refine ⟨294352254100742989640251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392469672134323986187001 294352254100742989640251)
          ·
            refine ⟨441528381151114484460377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294352254100742989640251 441528381151114484460377)
            ·
              refine ⟨331146285863335863345283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441528381151114484460377 331146285863335863345283)
              ·
                refine ⟨496719428795003795017925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331146285863335863345283 496719428795003795017925)
                ·
                  refine ⟨93134892899063211565861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 496719428795003795017925 93134892899063211565861)
                  ·
                    refine ⟨17462792418574352168599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93134892899063211565861 17462792418574352168599)
                    ·
                      rfl

theorem cell23_102026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_102026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102026 prefixEnd_102026 := by exact prefixLift 102026
  have htrace : WordTrace (prefixWord ++ tailWord_102026) baseStart_102026 baseEnd_102026 := by
    simpa [prefixWord, tailWord_102026, baseEnd_102026] using wordTrace_append hprefix tailTrace_102026
  have hstable : (prefixWord ++ tailWord_102026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102026).length < 2 ^ (prefixWord ++ tailWord_102026).sum := by decide
  have hdescent : baseEnd_102026 < baseStart_102026 := by decide
  rcases family_descends (prefixWord ++ tailWord_102026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102039 : List Nat := [1, 1, 3, 3, 2, 3, 2, 8]
def baseStart_102039 : Nat := 118140960795 + 102039 * 2 ^ 59
def prefixEnd_102039 : Nat := 4983230072969 + 3 ^ 40 * 102039 * 2
def baseEnd_102039 : Nat := 1940557500156722431231

theorem tailTrace_102039 : CollatzResearch.WordTrace tailWord_102039 prefixEnd_102039 1940557500156722431231 := by
  unfold tailWord_102039
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721668077337604718885171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2481112051558403145923447 3721668077337604718885171)
  ·
    refine ⟨5582502116006407078327757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721668077337604718885171 5582502116006407078327757)
    ·
      refine ⟨2093438293502402654372909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5582502116006407078327757 2093438293502402654372909)
      ·
        refine ⟨785039360063400995389841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2093438293502402654372909 785039360063400995389841)
        ·
          refine ⟨588779520047550746542381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785039360063400995389841 588779520047550746542381)
          ·
            refine ⟨220792320017831529953393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 588779520047550746542381 220792320017831529953393)
            ·
              refine ⟨165594240013373647465045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220792320017831529953393 165594240013373647465045)
              ·
                refine ⟨1940557500156722431231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 165594240013373647465045 1940557500156722431231)
                ·
                  rfl

theorem cell23_102039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 8].length) (baseStart_102039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102039 prefixEnd_102039 := by exact prefixLift 102039
  have htrace : WordTrace (prefixWord ++ tailWord_102039) baseStart_102039 baseEnd_102039 := by
    simpa [prefixWord, tailWord_102039, baseEnd_102039] using wordTrace_append hprefix tailTrace_102039
  have hstable : (prefixWord ++ tailWord_102039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102039).length < 2 ^ (prefixWord ++ tailWord_102039).sum := by decide
  have hdescent : baseEnd_102039 < baseStart_102039 := by decide
  rcases family_descends (prefixWord ++ tailWord_102039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102046 : List Nat := [4, 3, 1, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_102046 : Nat := 118140960795 + 102046 * 2 ^ 59
def prefixEnd_102046 : Nat := 4983230072969 + 3 ^ 40 * 102046 * 2
def baseEnd_102046 : Nat := 52398646868812978255705

theorem tailTrace_102046 : CollatzResearch.WordTrace tailWord_102046 prefixEnd_102046 52398646868812978255705 := by
  unfold tailWord_102046
  simp only [CollatzResearch.WordTrace]
  refine ⟨465240423539030614298749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2481282258874829942926661 465240423539030614298749)
  ·
    refine ⟨174465158827136480362031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 465240423539030614298749 174465158827136480362031)
    ·
      refine ⟨261697738240704720543047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174465158827136480362031 261697738240704720543047)
      ·
        refine ⟨392546607361057080814571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261697738240704720543047 392546607361057080814571)
        ·
          refine ⟨588819911041585621221857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392546607361057080814571 588819911041585621221857)
          ·
            refine ⟨441614933281189215916393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588819911041585621221857 441614933281189215916393)
            ·
              refine ⟨331211199960891911937295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441614933281189215916393 331211199960891911937295)
              ·
                refine ⟨496816799941337867905943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331211199960891911937295 496816799941337867905943)
                ·
                  refine ⟨745225199912006801858915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 496816799941337867905943 745225199912006801858915)
                  ·
                    refine ⟨1117837799868010202788373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 745225199912006801858915 1117837799868010202788373)
                    ·
                      refine ⟨52398646868812978255705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1117837799868010202788373 52398646868812978255705)
                      ·
                        rfl

theorem cell23_102046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_102046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102046 prefixEnd_102046 := by exact prefixLift 102046
  have htrace : WordTrace (prefixWord ++ tailWord_102046) baseStart_102046 baseEnd_102046 := by
    simpa [prefixWord, tailWord_102046, baseEnd_102046] using wordTrace_append hprefix tailTrace_102046
  have hstable : (prefixWord ++ tailWord_102046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102046).length < 2 ^ (prefixWord ++ tailWord_102046).sum := by decide
  have hdescent : baseEnd_102046 < baseStart_102046 := by decide
  rcases family_descends (prefixWord ++ tailWord_102046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102066 : List Nat := [3, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3]
def baseStart_102066 : Nat := 118140960795 + 102066 * 2 ^ 59
def prefixEnd_102066 : Nat := 4983230072969 + 3 ^ 40 * 102066 * 2
def baseEnd_102066 : Nat := 52408916481902900005613

theorem tailTrace_102066 : CollatzResearch.WordTrace tailWord_102066 prefixEnd_102066 52408916481902900005613 := by
  unfold tailWord_102066
  simp only [CollatzResearch.WordTrace]
  refine ⟨930663212059947082529513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2481768565493192220078701 930663212059947082529513)
  ·
    refine ⟨697997409044960311897135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 930663212059947082529513 697997409044960311897135)
    ·
      refine ⟨1046996113567440467845703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 697997409044960311897135 1046996113567440467845703)
      ·
        refine ⟨1570494170351160701768555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1046996113567440467845703 1570494170351160701768555)
        ·
          refine ⟨2355741255526741052652833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570494170351160701768555 2355741255526741052652833)
          ·
            refine ⟨1766805941645055789489625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355741255526741052652833 1766805941645055789489625)
            ·
              refine ⟨1325104456233791842117219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1766805941645055789489625 1325104456233791842117219)
              ·
                refine ⟨1987656684350687763175829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1325104456233791842117219 1987656684350687763175829)
                ·
                  refine ⟨93171407078938488898867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1987656684350687763175829 93171407078938488898867)
                  ·
                    refine ⟨139757110618407733348301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93171407078938488898867 139757110618407733348301)
                    ·
                      refine ⟨52408916481902900005613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139757110618407733348301 52408916481902900005613)
                      ·
                        rfl

theorem cell23_102066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_102066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102066 prefixEnd_102066 := by exact prefixLift 102066
  have htrace : WordTrace (prefixWord ++ tailWord_102066) baseStart_102066 baseEnd_102066 := by
    simpa [prefixWord, tailWord_102066, baseEnd_102066] using wordTrace_append hprefix tailTrace_102066
  have hstable : (prefixWord ++ tailWord_102066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102066).length < 2 ^ (prefixWord ++ tailWord_102066).sum := by decide
  have hdescent : baseEnd_102066 < baseStart_102066 := by decide
  rcases family_descends (prefixWord ++ tailWord_102066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102070 : List Nat := [5, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_102070 : Nat := 118140960795 + 102070 * 2 ^ 59
def prefixEnd_102070 : Nat := 4983230072969 + 3 ^ 40 * 102070 * 2
def baseEnd_102070 : Nat := 52410970404520884355595

theorem tailTrace_102070 : CollatzResearch.WordTrace tailWord_102070 prefixEnd_102070 52410970404520884355595 := by
  unfold tailWord_102070
  simp only [CollatzResearch.WordTrace]
  refine ⟨232674921264081063328979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2481865826816864675509109 232674921264081063328979)
  ·
    refine ⟨349012381896121594993469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 232674921264081063328979 349012381896121594993469)
    ·
      refine ⟨130879643211045598122551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349012381896121594993469 130879643211045598122551)
      ·
        refine ⟨196319464816568397183827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130879643211045598122551 196319464816568397183827)
        ·
          refine ⟨294479197224852595775741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196319464816568397183827 294479197224852595775741)
          ·
            refine ⟨110429698959319723415903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294479197224852595775741 110429698959319723415903)
            ·
              refine ⟨165644548438979585123855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110429698959319723415903 165644548438979585123855)
              ·
                refine ⟨248466822658469377685783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165644548438979585123855 248466822658469377685783)
                ·
                  refine ⟨372700233987704066528675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 248466822658469377685783 372700233987704066528675)
                  ·
                    refine ⟨559050350981556099793013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 372700233987704066528675 559050350981556099793013)
                    ·
                      refine ⟨52410970404520884355595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 559050350981556099793013 52410970404520884355595)
                      ·
                        rfl

theorem cell23_102070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_102070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102070 prefixEnd_102070 := by exact prefixLift 102070
  have htrace : WordTrace (prefixWord ++ tailWord_102070) baseStart_102070 baseEnd_102070 := by
    simpa [prefixWord, tailWord_102070, baseEnd_102070] using wordTrace_append hprefix tailTrace_102070
  have hstable : (prefixWord ++ tailWord_102070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102070).length < 2 ^ (prefixWord ++ tailWord_102070).sum := by decide
  have hdescent : baseEnd_102070 < baseStart_102070 := by decide
  rcases family_descends (prefixWord ++ tailWord_102070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102100 : List Nat := [2, 4, 1, 3, 1, 1, 2, 3, 2, 1, 3]
def baseStart_102100 : Nat := 118140960795 + 102100 * 2 ^ 59
def prefixEnd_102100 : Nat := 4983230072969 + 3 ^ 40 * 102100 * 2
def baseEnd_102100 : Nat := 52426374824155766980457

theorem tailTrace_102100 : CollatzResearch.WordTrace tailWord_102100 prefixEnd_102100 52426374824155766980457 := by
  unfold tailWord_102100
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861946465058306068427877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2482595286744408091237169 1861946465058306068427877)
  ·
    refine ⟨349114962198432387830227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1861946465058306068427877 349114962198432387830227)
    ·
      refine ⟨523672443297648581745341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 349114962198432387830227 523672443297648581745341)
      ·
        refine ⟨196377166236618218154503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 523672443297648581745341 196377166236618218154503)
        ·
          refine ⟨294565749354927327231755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196377166236618218154503 294565749354927327231755)
          ·
            refine ⟨441848624032390990847633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294565749354927327231755 441848624032390990847633)
            ·
              refine ⟨331386468024293243135725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441848624032390990847633 331386468024293243135725)
              ·
                refine ⟨124269925509109966175897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331386468024293243135725 124269925509109966175897)
                ·
                  refine ⟨93202444131832474631923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124269925509109966175897 93202444131832474631923)
                  ·
                    refine ⟨139803666197748711947885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93202444131832474631923 139803666197748711947885)
                    ·
                      refine ⟨52426374824155766980457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139803666197748711947885 52426374824155766980457)
                      ·
                        rfl

theorem cell23_102100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_102100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102100 prefixEnd_102100 := by exact prefixLift 102100
  have htrace : WordTrace (prefixWord ++ tailWord_102100) baseStart_102100 baseEnd_102100 := by
    simpa [prefixWord, tailWord_102100, baseEnd_102100] using wordTrace_append hprefix tailTrace_102100
  have hstable : (prefixWord ++ tailWord_102100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102100).length < 2 ^ (prefixWord ++ tailWord_102100).sum := by decide
  have hdescent : baseEnd_102100 < baseStart_102100 := by decide
  rcases family_descends (prefixWord ++ tailWord_102100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102156 : List Nat := [2, 2, 1, 2, 2, 1, 4, 1, 2, 3, 3]
def baseStart_102156 : Nat := 118140960795 + 102156 * 2 ^ 59
def prefixEnd_102156 : Nat := 4983230072969 + 3 ^ 40 * 102156 * 2
def baseEnd_102156 : Nat := 52455129740807547880199

theorem tailTrace_102156 : CollatzResearch.WordTrace tailWord_102156 prefixEnd_102156 52455129740807547880199 := by
  unfold tailWord_102156
  simp only [CollatzResearch.WordTrace]
  refine ⟨1862967708956866850447161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2483956945275822467262881 1862967708956866850447161)
  ·
    refine ⟨1397225781717650137835371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1862967708956866850447161 1397225781717650137835371)
    ·
      refine ⟨2095838672576475206753057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397225781717650137835371 2095838672576475206753057)
      ·
        refine ⟨1571879004432356405064793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2095838672576475206753057 1571879004432356405064793)
        ·
          refine ⟨1178909253324267303798595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1571879004432356405064793 1178909253324267303798595)
          ·
            refine ⟨1768363879986400955697893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178909253324267303798595 1768363879986400955697893)
            ·
              refine ⟨331568227497450179193355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1768363879986400955697893 331568227497450179193355)
              ·
                refine ⟨497352341246175268790033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331568227497450179193355 497352341246175268790033)
                ·
                  refine ⟨373014255934631451592525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 497352341246175268790033 373014255934631451592525)
                  ·
                    refine ⟨139880345975486794347197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 373014255934631451592525 139880345975486794347197)
                    ·
                      refine ⟨52455129740807547880199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139880345975486794347197 52455129740807547880199)
                      ·
                        rfl

theorem cell23_102156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_102156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102156 prefixEnd_102156 := by exact prefixLift 102156
  have htrace : WordTrace (prefixWord ++ tailWord_102156) baseStart_102156 baseEnd_102156 := by
    simpa [prefixWord, tailWord_102156, baseEnd_102156] using wordTrace_append hprefix tailTrace_102156
  have hstable : (prefixWord ++ tailWord_102156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102156).length < 2 ^ (prefixWord ++ tailWord_102156).sum := by decide
  have hdescent : baseEnd_102156 < baseStart_102156 := by decide
  rcases family_descends (prefixWord ++ tailWord_102156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102159 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 6, 5]
def baseStart_102159 : Nat := 118140960795 + 102159 * 2 ^ 59
def prefixEnd_102159 : Nat := 4983230072969 + 3 ^ 40 * 102159 * 2
def baseEnd_102159 : Nat := 17485556727590345380895

theorem tailTrace_102159 : CollatzResearch.WordTrace tailWord_102159 prefixEnd_102159 17485556727590345380895 := by
  unfold tailWord_102159
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726044836902865213253531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2484029891268576808835687 3726044836902865213253531)
  ·
    refine ⟨5589067255354297819880297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3726044836902865213253531 5589067255354297819880297)
    ·
      refine ⟨4191800441515723364910223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5589067255354297819880297 4191800441515723364910223)
      ·
        refine ⟨6287700662273585047365335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191800441515723364910223 6287700662273585047365335)
        ·
          refine ⟨9431550993410377571048003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287700662273585047365335 9431550993410377571048003)
          ·
            refine ⟨14147326490115566356572005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9431550993410377571048003 14147326490115566356572005)
            ·
              refine ⟨2652623716896668691857251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14147326490115566356572005 2652623716896668691857251)
              ·
                refine ⟨3978935575345003037785877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652623716896668691857251 3978935575345003037785877)
                ·
                  refine ⟨186512605094297017396213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3978935575345003037785877 186512605094297017396213)
                  ·
                    refine ⟨17485556727590345380895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186512605094297017396213 17485556727590345380895)
                    ·
                      rfl

theorem cell23_102159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 5].length) (baseStart_102159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102159 prefixEnd_102159 := by exact prefixLift 102159
  have htrace : WordTrace (prefixWord ++ tailWord_102159) baseStart_102159 baseEnd_102159 := by
    simpa [prefixWord, tailWord_102159, baseEnd_102159] using wordTrace_append hprefix tailTrace_102159
  have hstable : (prefixWord ++ tailWord_102159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102159).length < 2 ^ (prefixWord ++ tailWord_102159).sum := by decide
  have hdescent : baseEnd_102159 < baseStart_102159 := by decide
  rcases family_descends (prefixWord ++ tailWord_102159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102176 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 2, 5]
def baseStart_102176 : Nat := 118140960795 + 102176 * 2 ^ 59
def prefixEnd_102176 : Nat := 4983230072969 + 3 ^ 40 * 102176 * 2
def baseEnd_102176 : Nat := 17488466451299156543369

theorem tailTrace_102176 : CollatzResearch.WordTrace tailWord_102176 prefixEnd_102176 17488466451299156543369 := by
  unfold tailWord_102176
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863332438920638558311191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2484443251894184744414921 1863332438920638558311191)
  ·
    refine ⟨2794998658380957837466787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1863332438920638558311191 2794998658380957837466787)
    ·
      refine ⟨4192497987571436756200181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2794998658380957837466787 4192497987571436756200181)
      ·
        refine ⟨393046686334822195893767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4192497987571436756200181 393046686334822195893767)
        ·
          refine ⟨589570029502233293840651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393046686334822195893767 589570029502233293840651)
          ·
            refine ⟨884355044253349940760977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 589570029502233293840651 884355044253349940760977)
            ·
              refine ⟨663266283190012455570733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884355044253349940760977 663266283190012455570733)
              ·
                refine ⟨248724856196254670839025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 663266283190012455570733 248724856196254670839025)
                ·
                  refine ⟨186543642147191003129269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248724856196254670839025 186543642147191003129269)
                  ·
                    refine ⟨17488466451299156543369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186543642147191003129269 17488466451299156543369)
                    ·
                      rfl

theorem cell23_102176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_102176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102176 prefixEnd_102176 := by exact prefixLift 102176
  have htrace : WordTrace (prefixWord ++ tailWord_102176) baseStart_102176 baseEnd_102176 := by
    simpa [prefixWord, tailWord_102176, baseEnd_102176] using wordTrace_append hprefix tailTrace_102176
  have hstable : (prefixWord ++ tailWord_102176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102176).length < 2 ^ (prefixWord ++ tailWord_102176).sum := by decide
  have hdescent : baseEnd_102176 < baseStart_102176 := by decide
  rcases family_descends (prefixWord ++ tailWord_102176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102180 : List Nat := [2, 3, 1, 3, 2, 3, 1, 3, 5]
def baseStart_102180 : Nat := 118140960795 + 102180 * 2 ^ 59
def prefixEnd_102180 : Nat := 4983230072969 + 3 ^ 40 * 102180 * 2
def baseEnd_102180 : Nat := 5829717030723939331121

theorem tailTrace_102180 : CollatzResearch.WordTrace tailWord_102180 prefixEnd_102180 5829717030723939331121 := by
  unfold tailWord_102180
  simp only [CollatzResearch.WordTrace]
  refine ⟨1863405384913392899883997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2484540513217857199845329 1863405384913392899883997)
  ·
    refine ⟨698777019342522337456499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1863405384913392899883997 698777019342522337456499)
    ·
      refine ⟨1048165529013783506184749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 698777019342522337456499 1048165529013783506184749)
      ·
        refine ⟨393062073380168814819281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1048165529013783506184749 393062073380168814819281)
        ·
          refine ⟨294796555035126611114461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393062073380168814819281 294796555035126611114461)
          ·
            refine ⟨110548708138172479167923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294796555035126611114461 110548708138172479167923)
            ·
              refine ⟨165823062207258718751885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110548708138172479167923 165823062207258718751885)
              ·
                refine ⟨62183648327722019531957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165823062207258718751885 62183648327722019531957)
                ·
                  refine ⟨5829717030723939331121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62183648327722019531957 5829717030723939331121)
                  ·
                    rfl

theorem cell23_102180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 5].length) (baseStart_102180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102180 prefixEnd_102180 := by exact prefixLift 102180
  have htrace : WordTrace (prefixWord ++ tailWord_102180) baseStart_102180 baseEnd_102180 := by
    simpa [prefixWord, tailWord_102180, baseEnd_102180] using wordTrace_append hprefix tailTrace_102180
  have hstable : (prefixWord ++ tailWord_102180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102180).length < 2 ^ (prefixWord ++ tailWord_102180).sum := by decide
  have hdescent : baseEnd_102180 < baseStart_102180 := by decide
  rcases family_descends (prefixWord ++ tailWord_102180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102199 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 5]
def baseStart_102199 : Nat := 118140960795 + 102199 * 2 ^ 59
def prefixEnd_102199 : Nat := 4983230072969 + 3 ^ 40 * 102199 * 2
def baseEnd_102199 : Nat := 52477209408950879642501

theorem tailTrace_102199 : CollatzResearch.WordTrace tailWord_102199 prefixEnd_102199 52477209408950879642501 := by
  unfold tailWord_102199
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727503756757952044709651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2485002504505301363139767 3727503756757952044709651)
  ·
    refine ⟨5591255635136928067064477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3727503756757952044709651 5591255635136928067064477)
    ·
      refine ⟨2096720863176348025149179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5591255635136928067064477 2096720863176348025149179)
      ·
        refine ⟨3145081294764522037723769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2096720863176348025149179 3145081294764522037723769)
        ·
          refine ⟨2358810971073391528292827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3145081294764522037723769 2358810971073391528292827)
          ·
            refine ⟨3538216456610087292439241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358810971073391528292827 3538216456610087292439241)
            ·
              refine ⟨2653662342457565469329431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538216456610087292439241 2653662342457565469329431)
              ·
                refine ⟨3980493513686348203994147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653662342457565469329431 3980493513686348203994147)
                ·
                  refine ⟨5970740270529522305991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980493513686348203994147 5970740270529522305991221)
                  ·
                    refine ⟨559756900362142716186677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5970740270529522305991221 559756900362142716186677)
                    ·
                      refine ⟨52477209408950879642501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 559756900362142716186677 52477209408950879642501)
                      ·
                        rfl

theorem cell23_102199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_102199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102199 prefixEnd_102199 := by exact prefixLift 102199
  have htrace : WordTrace (prefixWord ++ tailWord_102199) baseStart_102199 baseEnd_102199 := by
    simpa [prefixWord, tailWord_102199, baseEnd_102199] using wordTrace_append hprefix tailTrace_102199
  have hstable : (prefixWord ++ tailWord_102199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102199).length < 2 ^ (prefixWord ++ tailWord_102199).sum := by decide
  have hdescent : baseEnd_102199 < baseStart_102199 := by decide
  rcases family_descends (prefixWord ++ tailWord_102199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102233 : List Nat := [1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 3]
def baseStart_102233 : Nat := 118140960795 + 102233 * 2 ^ 59
def prefixEnd_102233 : Nat := 4983230072969 + 3 ^ 40 * 102233 * 2
def baseEnd_102233 : Nat := 52494667751203746617345

theorem tailTrace_102233 : CollatzResearch.WordTrace tailWord_102233 prefixEnd_102233 52494667751203746617345 := by
  unfold tailWord_102233
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728743838634775851447353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2485829225756517234298235 3728743838634775851447353)
  ·
    refine ⟨2796557878976081888585515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3728743838634775851447353 2796557878976081888585515)
    ·
      refine ⟨4194836818464122832878273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796557878976081888585515 4194836818464122832878273)
      ·
        refine ⟨3146127613848092124658705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4194836818464122832878273 3146127613848092124658705)
        ·
          refine ⟨2359595710386069093494029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3146127613848092124658705 2359595710386069093494029)
          ·
            refine ⟨884848391394775910060261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2359595710386069093494029 884848391394775910060261)
            ·
              refine ⟨165909073386520483136299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 884848391394775910060261 165909073386520483136299)
              ·
                refine ⟨248863610079780724704449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165909073386520483136299 248863610079780724704449)
                ·
                  refine ⟨186647707559835543528337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 248863610079780724704449 186647707559835543528337)
                  ·
                    refine ⟨139985780669876657646253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186647707559835543528337 139985780669876657646253)
                    ·
                      refine ⟨52494667751203746617345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 139985780669876657646253 52494667751203746617345)
                      ·
                        rfl

theorem cell23_102233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 2, 3].length) (baseStart_102233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102233 prefixEnd_102233 := by exact prefixLift 102233
  have htrace : WordTrace (prefixWord ++ tailWord_102233) baseStart_102233 baseEnd_102233 := by
    simpa [prefixWord, tailWord_102233, baseEnd_102233] using wordTrace_append hprefix tailTrace_102233
  have hstable : (prefixWord ++ tailWord_102233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102233).length < 2 ^ (prefixWord ++ tailWord_102233).sum := by decide
  have hdescent : baseEnd_102233 < baseStart_102233 := by decide
  rcases family_descends (prefixWord ++ tailWord_102233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102266 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 3, 5]
def baseStart_102266 : Nat := 118140960795 + 102266 * 2 ^ 59
def prefixEnd_102266 : Nat := 4983230072969 + 3 ^ 40 * 102266 * 2
def baseEnd_102266 : Nat := 17503870870934039168231

theorem tailTrace_102266 : CollatzResearch.WordTrace tailWord_102266 prefixEnd_102266 17503870870934039168231 := by
  unfold tailWord_102266
  simp only [CollatzResearch.WordTrace]
  refine ⟨932486861878805621849663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2486631631676814991599101 932486861878805621849663)
  ·
    refine ⟨1398730292818208432774495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 932486861878805621849663 1398730292818208432774495)
    ·
      refine ⟨2098095439227312649161743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398730292818208432774495 2098095439227312649161743)
      ·
        refine ⟨3147143158840968973742615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098095439227312649161743 3147143158840968973742615)
        ·
          refine ⟨4720714738261453460613923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147143158840968973742615 4720714738261453460613923)
          ·
            refine ⟨7081072107392180190920885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720714738261453460613923 7081072107392180190920885)
            ·
              refine ⟨663850510068016892898833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7081072107392180190920885 663850510068016892898833)
              ·
                refine ⟨497887882551012669674125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 663850510068016892898833 497887882551012669674125)
                ·
                  refine ⟨186707955956629751127797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497887882551012669674125 186707955956629751127797)
                  ·
                    refine ⟨17503870870934039168231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186707955956629751127797 17503870870934039168231)
                    ·
                      rfl

theorem cell23_102266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_102266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102266 prefixEnd_102266 := by exact prefixLift 102266
  have htrace : WordTrace (prefixWord ++ tailWord_102266) baseStart_102266 baseEnd_102266 := by
    simpa [prefixWord, tailWord_102266, baseEnd_102266] using wordTrace_append hprefix tailTrace_102266
  have hstable : (prefixWord ++ tailWord_102266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102266).length < 2 ^ (prefixWord ++ tailWord_102266).sum := by decide
  have hdescent : baseEnd_102266 < baseStart_102266 := by decide
  rcases family_descends (prefixWord ++ tailWord_102266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102270 : List Nat := [4, 2, 3, 1, 1, 1, 2, 3, 6]
def baseStart_102270 : Nat := 118140960795 + 102270 * 2 ^ 59
def prefixEnd_102270 : Nat := 4983230072969 + 3 ^ 40 * 102270 * 2
def baseEnd_102270 : Nat := 5834851837268900206075

theorem tailTrace_102270 : CollatzResearch.WordTrace tailWord_102270 prefixEnd_102270 5834851837268900206075 := by
  unfold tailWord_102270
  simp only [CollatzResearch.WordTrace]
  refine ⟨466261667437591396318033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2486728893000487447029509 466261667437591396318033)
  ·
    refine ⟨349696250578193547238525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 466261667437591396318033 349696250578193547238525)
    ·
      refine ⟨131136093966822580214447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 349696250578193547238525 131136093966822580214447)
      ·
        refine ⟨196704140950233870321671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131136093966822580214447 196704140950233870321671)
        ·
          refine ⟨295056211425350805482507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196704140950233870321671 295056211425350805482507)
          ·
            refine ⟨442584317138026208223761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295056211425350805482507 442584317138026208223761)
            ·
              refine ⟨331938237853519656167821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442584317138026208223761 331938237853519656167821)
              ·
                refine ⟨124476839195069871062933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331938237853519656167821 124476839195069871062933)
                ·
                  refine ⟨5834851837268900206075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124476839195069871062933 5834851837268900206075)
                  ·
                    rfl

theorem cell23_102270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_102270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102270 prefixEnd_102270 := by exact prefixLift 102270
  have htrace : WordTrace (prefixWord ++ tailWord_102270) baseStart_102270 baseEnd_102270 := by
    simpa [prefixWord, tailWord_102270, baseEnd_102270] using wordTrace_append hprefix tailTrace_102270
  have hstable : (prefixWord ++ tailWord_102270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102270).length < 2 ^ (prefixWord ++ tailWord_102270).sum := by decide
  have hdescent : baseEnd_102270 < baseStart_102270 := by decide
  rcases family_descends (prefixWord ++ tailWord_102270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102300 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 1, 5]
def baseStart_102300 : Nat := 118140960795 + 102300 * 2 ^ 59
def prefixEnd_102300 : Nat := 4983230072969 + 3 ^ 40 * 102300 * 2
def baseEnd_102300 : Nat := 17509690318351661493179

theorem tailTrace_102300 : CollatzResearch.WordTrace tailWord_102300 prefixEnd_102300 17509690318351661493179 := by
  unfold tailWord_102300
  simp only [CollatzResearch.WordTrace]
  refine ⟨1865593764696023147068177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2487458352928030862757569 1865593764696023147068177)
  ·
    refine ⟨1399195323522017360301133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1865593764696023147068177 1399195323522017360301133)
    ·
      refine ⟨524698246320756510112925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1399195323522017360301133 524698246320756510112925)
      ·
        refine ⟨196761842370283691292347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 524698246320756510112925 196761842370283691292347)
        ·
          refine ⟨295142763555425536938521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196761842370283691292347 295142763555425536938521)
          ·
            refine ⟨221357072666569152703891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295142763555425536938521 221357072666569152703891)
            ·
              refine ⟨332035608999853729055837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221357072666569152703891 332035608999853729055837)
              ·
                refine ⟨124513353374945148395939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332035608999853729055837 124513353374945148395939)
                ·
                  refine ⟨186770030062417722593909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124513353374945148395939 186770030062417722593909)
                  ·
                    refine ⟨17509690318351661493179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186770030062417722593909 17509690318351661493179)
                    ·
                      rfl

theorem cell23_102300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_102300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102300 prefixEnd_102300 := by exact prefixLift 102300
  have htrace : WordTrace (prefixWord ++ tailWord_102300) baseStart_102300 baseEnd_102300 := by
    simpa [prefixWord, tailWord_102300, baseEnd_102300] using wordTrace_append hprefix tailTrace_102300
  have hstable : (prefixWord ++ tailWord_102300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102300).length < 2 ^ (prefixWord ++ tailWord_102300).sum := by decide
  have hdescent : baseEnd_102300 < baseStart_102300 := by decide
  rcases family_descends (prefixWord ++ tailWord_102300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102313 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 2, 4]
def baseStart_102313 : Nat := 118140960795 + 102313 * 2 ^ 59
def prefixEnd_102313 : Nat := 4983230072969 + 3 ^ 40 * 102313 * 2
def baseEnd_102313 : Nat := 17511915401187811205659

theorem tailTrace_102313 : CollatzResearch.WordTrace tailWord_102313 prefixEnd_102313 17511915401187811205659 := by
  unfold tailWord_102313
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731661678344949514359593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2487774452229966342906395 3731661678344949514359593)
  ·
    refine ⟨2798746258758712135769695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3731661678344949514359593 2798746258758712135769695)
    ·
      refine ⟨4198119388138068203654543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2798746258758712135769695 4198119388138068203654543)
      ·
        refine ⟨6297179082207102305481815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4198119388138068203654543 6297179082207102305481815)
        ·
          refine ⟨9445768623310653458222723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6297179082207102305481815 9445768623310653458222723)
          ·
            refine ⟨14168652934965980187334085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9445768623310653458222723 14168652934965980187334085)
            ·
              refine ⟨2656622425306121285125141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14168652934965980187334085 2656622425306121285125141)
              ·
                refine ⟨124529176186224435240241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2656622425306121285125141 124529176186224435240241)
                ·
                  refine ⟨93396882139668326430181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124529176186224435240241 93396882139668326430181)
                  ·
                    refine ⟨17511915401187811205659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93396882139668326430181 17511915401187811205659)
                    ·
                      rfl

theorem cell23_102313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 4].length) (baseStart_102313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102313 prefixEnd_102313 := by exact prefixLift 102313
  have htrace : WordTrace (prefixWord ++ tailWord_102313) baseStart_102313 baseEnd_102313 := by
    simpa [prefixWord, tailWord_102313, baseEnd_102313] using wordTrace_append hprefix tailTrace_102313
  have hstable : (prefixWord ++ tailWord_102313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102313).length < 2 ^ (prefixWord ++ tailWord_102313).sum := by decide
  have hdescent : baseEnd_102313 < baseStart_102313 := by decide
  rcases family_descends (prefixWord ++ tailWord_102313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102333 : List Nat := [1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_102333 : Nat := 118140960795 + 102333 * 2 ^ 59
def prefixEnd_102333 : Nat := 4983230072969 + 3 ^ 40 * 102333 * 2
def baseEnd_102333 : Nat := 52546015816653355366885

theorem tailTrace_102333 : CollatzResearch.WordTrace tailWord_102333 prefixEnd_102333 52546015816653355366885 := by
  unfold tailWord_102333
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732391138272492930087653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2488260758848328620058435 3732391138272492930087653)
  ·
    refine ⟨699823338426092424391435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3732391138272492930087653 699823338426092424391435)
    ·
      refine ⟨1049735007639138636587153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 699823338426092424391435 1049735007639138636587153)
      ·
        refine ⟨787301255729353977440365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1049735007639138636587153 787301255729353977440365)
        ·
          refine ⟨295237970898507741540137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787301255729353977440365 295237970898507741540137)
          ·
            refine ⟨221428478173880806155103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295237970898507741540137 221428478173880806155103)
            ·
              refine ⟨332142717260821209232655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221428478173880806155103 332142717260821209232655)
              ·
                refine ⟨498214075891231813848983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 332142717260821209232655 498214075891231813848983)
                ·
                  refine ⟨747321113836847720773475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 498214075891231813848983 747321113836847720773475)
                  ·
                    refine ⟨1120981670755271581160213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 747321113836847720773475 1120981670755271581160213)
                    ·
                      refine ⟨52546015816653355366885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1120981670755271581160213 52546015816653355366885)
                      ·
                        rfl

theorem cell23_102333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_102333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102333 prefixEnd_102333 := by exact prefixLift 102333
  have htrace : WordTrace (prefixWord ++ tailWord_102333) baseStart_102333 baseEnd_102333 := by
    simpa [prefixWord, tailWord_102333, baseEnd_102333] using wordTrace_append hprefix tailTrace_102333
  have hstable : (prefixWord ++ tailWord_102333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102333).length < 2 ^ (prefixWord ++ tailWord_102333).sum := by decide
  have hdescent : baseEnd_102333 < baseStart_102333 := by decide
  rcases family_descends (prefixWord ++ tailWord_102333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102371 : List Nat := [1, 1, 1, 6, 1, 3, 3, 2, 1, 2, 2]
def baseStart_102371 : Nat := 118140960795 + 102371 * 2 ^ 59
def prefixEnd_102371 : Nat := 4983230072969 + 3 ^ 40 * 102371 * 2
def baseEnd_102371 : Nat := 52565528081524206691711

theorem tailTrace_102371 : CollatzResearch.WordTrace tailWord_102371 prefixEnd_102371 52565528081524206691711 := by
  unfold tailWord_102371
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733777112134825419970967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2489184741423216946647311 3733777112134825419970967)
  ·
    refine ⟨5600665668202238129956451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733777112134825419970967 5600665668202238129956451)
    ·
      refine ⟨8400998502303357194934677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5600665668202238129956451 8400998502303357194934677)
      ·
        refine ⟨393796804795469868512563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8400998502303357194934677 393796804795469868512563)
        ·
          refine ⟨590695207193204802768845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393796804795469868512563 590695207193204802768845)
          ·
            refine ⟨221510702697451801038317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 590695207193204802768845 221510702697451801038317)
            ·
              refine ⟨83066513511544425389369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221510702697451801038317 83066513511544425389369)
              ·
                refine ⟨62299885133658319042027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83066513511544425389369 62299885133658319042027)
                ·
                  refine ⟨93449827700487478563041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62299885133658319042027 93449827700487478563041)
                  ·
                    refine ⟨70087370775365608922281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93449827700487478563041 70087370775365608922281)
                    ·
                      refine ⟨52565528081524206691711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70087370775365608922281 52565528081524206691711)
                      ·
                        rfl

theorem cell23_102371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_102371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102371 prefixEnd_102371 := by exact prefixLift 102371
  have htrace : WordTrace (prefixWord ++ tailWord_102371) baseStart_102371 baseEnd_102371 := by
    simpa [prefixWord, tailWord_102371, baseEnd_102371] using wordTrace_append hprefix tailTrace_102371
  have hstable : (prefixWord ++ tailWord_102371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102371).length < 2 ^ (prefixWord ++ tailWord_102371).sum := by decide
  have hdescent : baseEnd_102371 < baseStart_102371 := by decide
  rcases family_descends (prefixWord ++ tailWord_102371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102381 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_102381 : Nat := 118140960795 + 102381 * 2 ^ 59
def prefixEnd_102381 : Nat := 4983230072969 + 3 ^ 40 * 102381 * 2
def baseEnd_102381 : Nat := 17523554296023055855555

theorem tailTrace_102381 : CollatzResearch.WordTrace tailWord_102381 prefixEnd_102381 17523554296023055855555 := by
  unfold tailWord_102381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734141842098597127834997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2489427894732398085223331 3734141842098597127834997)
  ·
    refine ⟨350075797696743480734531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3734141842098597127834997 350075797696743480734531)
    ·
      refine ⟨525113696545115221101797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350075797696743480734531 525113696545115221101797)
      ·
        refine ⟨98458818102209103956587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 525113696545115221101797 98458818102209103956587)
        ·
          refine ⟨147688227153313655934881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98458818102209103956587 147688227153313655934881)
          ·
            refine ⟨110766170364985241951161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147688227153313655934881 110766170364985241951161)
            ·
              refine ⟨83074627773738931463371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110766170364985241951161 83074627773738931463371)
              ·
                refine ⟨124611941660608397195057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83074627773738931463371 124611941660608397195057)
                ·
                  refine ⟨93458956245456297896293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124611941660608397195057 93458956245456297896293)
                  ·
                    refine ⟨17523554296023055855555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93458956245456297896293 17523554296023055855555)
                    ·
                      rfl

theorem cell23_102381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_102381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102381 prefixEnd_102381 := by exact prefixLift 102381
  have htrace : WordTrace (prefixWord ++ tailWord_102381) baseStart_102381 baseEnd_102381 := by
    simpa [prefixWord, tailWord_102381, baseEnd_102381] using wordTrace_append hprefix tailTrace_102381
  have hstable : (prefixWord ++ tailWord_102381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102381).length < 2 ^ (prefixWord ++ tailWord_102381).sum := by decide
  have hdescent : baseEnd_102381 < baseStart_102381 := by decide
  rcases family_descends (prefixWord ++ tailWord_102381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102397 : List Nat := [1, 4, 1, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_102397 : Nat := 118140960795 + 102397 * 2 ^ 59
def prefixEnd_102397 : Nat := 4983230072969 + 3 ^ 40 * 102397 * 2
def baseEnd_102397 : Nat := 52578878578541104966591

theorem tailTrace_102397 : CollatzResearch.WordTrace tailWord_102397 prefixEnd_102397 52578878578541104966591 := by
  unfold tailWord_102397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3734725410040631860417445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2489816940027087906944963 3734725410040631860417445)
  ·
    refine ⟨700261014382618473828271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3734725410040631860417445 700261014382618473828271)
    ·
      refine ⟨1050391521573927710742407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700261014382618473828271 1050391521573927710742407)
      ·
        refine ⟨1575587282360891566113611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1050391521573927710742407 1575587282360891566113611)
        ·
          refine ⟨2363380923541337349170417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1575587282360891566113611 2363380923541337349170417)
          ·
            refine ⟨1772535692656003011877813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2363380923541337349170417 1772535692656003011877813)
            ·
              refine ⟨166175221186500282363545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1772535692656003011877813 166175221186500282363545)
              ·
                refine ⟨124631415889875211772659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166175221186500282363545 124631415889875211772659)
                ·
                  refine ⟨186947123834812817658989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124631415889875211772659 186947123834812817658989)
                  ·
                    refine ⟨70105171438054806622121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186947123834812817658989 70105171438054806622121)
                    ·
                      refine ⟨52578878578541104966591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70105171438054806622121 52578878578541104966591)
                      ·
                        rfl

theorem cell23_102397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_102397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102397 prefixEnd_102397 := by exact prefixLift 102397
  have htrace : WordTrace (prefixWord ++ tailWord_102397) baseStart_102397 baseEnd_102397 := by
    simpa [prefixWord, tailWord_102397, baseEnd_102397] using wordTrace_append hprefix tailTrace_102397
  have hstable : (prefixWord ++ tailWord_102397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102397).length < 2 ^ (prefixWord ++ tailWord_102397).sum := by decide
  have hdescent : baseEnd_102397 < baseStart_102397 := by decide
  rcases family_descends (prefixWord ++ tailWord_102397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102414 : List Nat := [4, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_102414 : Nat := 118140960795 + 102414 * 2 ^ 59
def prefixEnd_102414 : Nat := 4983230072969 + 3 ^ 40 * 102414 * 2
def baseEnd_102414 : Nat := 52587607749667538454013

theorem tailTrace_102414 : CollatzResearch.WordTrace tailWord_102414 prefixEnd_102414 52587607749667538454013 := by
  unfold tailWord_102414
  simp only [CollatzResearch.WordTrace]
  refine ⟨466918181372380470473287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2490230300652695842524197 466918181372380470473287)
  ·
    refine ⟨700377272058570705709931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 466918181372380470473287 700377272058570705709931)
    ·
      refine ⟨1050565908087856058564897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700377272058570705709931 1050565908087856058564897)
      ·
        refine ⟨787924431065892043923673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050565908087856058564897 787924431065892043923673)
        ·
          refine ⟨590943323299419032942755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 787924431065892043923673 590943323299419032942755)
          ·
            refine ⟨886414984949128549414133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590943323299419032942755 886414984949128549414133)
            ·
              refine ⟨83101404838980801507575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 886414984949128549414133 83101404838980801507575)
              ·
                refine ⟨124652107258471202261363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83101404838980801507575 124652107258471202261363)
                ·
                  refine ⟨186978160887706803392045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124652107258471202261363 186978160887706803392045)
                  ·
                    refine ⟨70116810332890051272017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186978160887706803392045 70116810332890051272017)
                    ·
                      refine ⟨52587607749667538454013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70116810332890051272017 52587607749667538454013)
                      ·
                        rfl

theorem cell23_102414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_102414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102414 prefixEnd_102414 := by exact prefixLift 102414
  have htrace : WordTrace (prefixWord ++ tailWord_102414) baseStart_102414 baseEnd_102414 := by
    simpa [prefixWord, tailWord_102414, baseEnd_102414] using wordTrace_append hprefix tailTrace_102414
  have hstable : (prefixWord ++ tailWord_102414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102414).length < 2 ^ (prefixWord ++ tailWord_102414).sum := by decide
  have hdescent : baseEnd_102414 < baseStart_102414 := by decide
  rcases family_descends (prefixWord ++ tailWord_102414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102416 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 9]
def baseStart_102416 : Nat := 118140960795 + 102416 * 2 ^ 59
def prefixEnd_102416 : Nat := 4983230072969 + 3 ^ 40 * 102416 * 2
def baseEnd_102416 : Nat := 5843181634552947847667

theorem tailTrace_102416 : CollatzResearch.WordTrace tailWord_102416 prefixEnd_102416 5843181634552947847667 := by
  unfold tailWord_102416
  simp only [CollatzResearch.WordTrace]
  refine ⟨1867709198485899052679551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2490278931314532070239401 1867709198485899052679551)
  ·
    refine ⟨2801563797728848579019327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1867709198485899052679551 2801563797728848579019327)
    ·
      refine ⟨4202345696593272868528991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2801563797728848579019327 4202345696593272868528991)
      ·
        refine ⟨6303518544889909302793487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4202345696593272868528991 6303518544889909302793487)
        ·
          refine ⟨9455277817334863954190231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6303518544889909302793487 9455277817334863954190231)
          ·
            refine ⟨14182916726002295931285347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9455277817334863954190231 14182916726002295931285347)
            ·
              refine ⟨21274375089003443896928021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14182916726002295931285347 21274375089003443896928021)
              ·
                refine ⟨997236332297036432668501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21274375089003443896928021 997236332297036432668501)
                ·
                  refine ⟨5843181634552947847667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 997236332297036432668501 5843181634552947847667)
                  ·
                    rfl

theorem cell23_102416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 9].length) (baseStart_102416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102416 prefixEnd_102416 := by exact prefixLift 102416
  have htrace : WordTrace (prefixWord ++ tailWord_102416) baseStart_102416 baseEnd_102416 := by
    simpa [prefixWord, tailWord_102416, baseEnd_102416] using wordTrace_append hprefix tailTrace_102416
  have hstable : (prefixWord ++ tailWord_102416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102416).length < 2 ^ (prefixWord ++ tailWord_102416).sum := by decide
  have hdescent : baseEnd_102416 < baseStart_102416 := by decide
  rcases family_descends (prefixWord ++ tailWord_102416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102513 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 4]
def baseStart_102513 : Nat := 118140960795 + 102513 * 2 ^ 59
def prefixEnd_102513 : Nat := 4983230072969 + 3 ^ 40 * 102513 * 2
def baseEnd_102513 : Nat := 52638442334462651116057

theorem tailTrace_102513 : CollatzResearch.WordTrace tailWord_102513 prefixEnd_102513 52638442334462651116057 := by
  unfold tailWord_102513
  simp only [CollatzResearch.WordTrace]
  refine ⟨3738956277620383671640193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2492637518413589114426795 3738956277620383671640193)
  ·
    refine ⟨2804217208215287753730145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3738956277620383671640193 2804217208215287753730145)
    ·
      refine ⟨2103162906161465815297609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804217208215287753730145 2103162906161465815297609)
      ·
        refine ⟨1577372179621099361473207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2103162906161465815297609 1577372179621099361473207)
        ·
          refine ⟨2366058269431649042209811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1577372179621099361473207 2366058269431649042209811)
          ·
            refine ⟨3549087404147473563314717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2366058269431649042209811 3549087404147473563314717)
            ·
              refine ⟨1330907776555302586243019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3549087404147473563314717 1330907776555302586243019)
              ·
                refine ⟨1996361664832953879364529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1330907776555302586243019 1996361664832953879364529)
                ·
                  refine ⟨1497271248624715409523397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1996361664832953879364529 1497271248624715409523397)
                  ·
                    refine ⟨280738359117134139285637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1497271248624715409523397 280738359117134139285637)
                    ·
                      refine ⟨52638442334462651116057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 280738359117134139285637 52638442334462651116057)
                      ·
                        rfl

theorem cell23_102513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_102513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102513 prefixEnd_102513 := by exact prefixLift 102513
  have htrace : WordTrace (prefixWord ++ tailWord_102513) baseStart_102513 baseEnd_102513 := by
    simpa [prefixWord, tailWord_102513, baseEnd_102513] using wordTrace_append hprefix tailTrace_102513
  have hstable : (prefixWord ++ tailWord_102513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102513).length < 2 ^ (prefixWord ++ tailWord_102513).sum := by decide
  have hdescent : baseEnd_102513 < baseStart_102513 := by decide
  rcases family_descends (prefixWord ++ tailWord_102513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102520 : List Nat := [2, 1, 2, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_102520 : Nat := 118140960795 + 102520 * 2 ^ 59
def prefixEnd_102520 : Nat := 4983230072969 + 3 ^ 40 * 102520 * 2
def baseEnd_102520 : Nat := 52642036699044123728525

theorem tailTrace_102520 : CollatzResearch.WordTrace tailWord_102520 prefixEnd_102520 52642036699044123728525 := by
  unfold tailWord_102520
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869605794297511933572507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2492807725730015911430009 1869605794297511933572507)
  ·
    refine ⟨2804408691446267900358761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1869605794297511933572507 2804408691446267900358761)
    ·
      refine ⟨2103306518584700925269071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2804408691446267900358761 2103306518584700925269071)
      ·
        refine ⟨3154959777877051387903607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2103306518584700925269071 3154959777877051387903607)
        ·
          refine ⟨4732439666815577081855411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3154959777877051387903607 4732439666815577081855411)
          ·
            refine ⟨7098659500223365622783117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4732439666815577081855411 7098659500223365622783117)
            ·
              refine ⟨2661997312583762108543669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7098659500223365622783117 2661997312583762108543669)
              ·
                refine ⟨249562248054727697675969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2661997312583762108543669 249562248054727697675969)
                ·
                  refine ⟨187171686041045773256977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 249562248054727697675969 187171686041045773256977)
                  ·
                    refine ⟨140378764530784329942733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187171686041045773256977 140378764530784329942733)
                    ·
                      refine ⟨52642036699044123728525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 140378764530784329942733 52642036699044123728525)
                      ·
                        rfl

theorem cell23_102520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_102520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102520 prefixEnd_102520 := by exact prefixLift 102520
  have htrace : WordTrace (prefixWord ++ tailWord_102520) baseStart_102520 baseEnd_102520 := by
    simpa [prefixWord, tailWord_102520, baseEnd_102520] using wordTrace_append hprefix tailTrace_102520
  have hstable : (prefixWord ++ tailWord_102520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102520).length < 2 ^ (prefixWord ++ tailWord_102520).sum := by decide
  have hdescent : baseEnd_102520 < baseStart_102520 := by decide
  rcases family_descends (prefixWord ++ tailWord_102520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102544 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 1, 4]
def baseStart_102544 : Nat := 118140960795 + 102544 * 2 ^ 59
def prefixEnd_102544 : Nat := 4983230072969 + 3 ^ 40 * 102544 * 2
def baseEnd_102544 : Nat := 17551453411584009942805

theorem tailTrace_102544 : CollatzResearch.WordTrace tailWord_102544 prefixEnd_102544 17551453411584009942805 := by
  unfold tailWord_102544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870043470254037983009343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2493391293672050644012457 1870043470254037983009343)
  ·
    refine ⟨2805065205381056974514015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1870043470254037983009343 2805065205381056974514015)
    ·
      refine ⟨4207597808071585461771023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805065205381056974514015 4207597808071585461771023)
      ·
        refine ⟨6311396712107378192656535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4207597808071585461771023 6311396712107378192656535)
        ·
          refine ⟨9467095068161067288984803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6311396712107378192656535 9467095068161067288984803)
          ·
            refine ⟨14200642602241600933477205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9467095068161067288984803 14200642602241600933477205)
            ·
              refine ⟨83206890247509380469593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 14200642602241600933477205 83206890247509380469593)
              ·
                refine ⟨62405167685632035352195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83206890247509380469593 62405167685632035352195)
                ·
                  refine ⟨93607751528448053028293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62405167685632035352195 93607751528448053028293)
                  ·
                    refine ⟨17551453411584009942805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93607751528448053028293 17551453411584009942805)
                    ·
                      rfl

theorem cell23_102544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 4].length) (baseStart_102544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102544 prefixEnd_102544 := by exact prefixLift 102544
  have htrace : WordTrace (prefixWord ++ tailWord_102544) baseStart_102544 baseEnd_102544 := by
    simpa [prefixWord, tailWord_102544, baseEnd_102544] using wordTrace_append hprefix tailTrace_102544
  have hstable : (prefixWord ++ tailWord_102544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102544).length < 2 ^ (prefixWord ++ tailWord_102544).sum := by decide
  have hdescent : baseEnd_102544 < baseStart_102544 := by decide
  rcases family_descends (prefixWord ++ tailWord_102544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102557 : List Nat := [1, 4, 2, 1, 1, 3, 4, 1, 6]
def baseStart_102557 : Nat := 118140960795 + 102557 * 2 ^ 59
def prefixEnd_102557 : Nat := 4983230072969 + 3 ^ 40 * 102557 * 2
def baseEnd_102557 : Nat := 5851226164806719885095

theorem tailTrace_102557 : CollatzResearch.WordTrace tailWord_102557 prefixEnd_102557 5851226164806719885095 := by
  unfold tailWord_102557
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740561089460979186241925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2493707392973986124161283 3740561089460979186241925)
  ·
    refine ⟨701355204273933597420361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3740561089460979186241925 701355204273933597420361)
    ·
      refine ⟨526016403205450198065271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 701355204273933597420361 526016403205450198065271)
      ·
        refine ⟨789024604808175297097907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526016403205450198065271 789024604808175297097907)
        ·
          refine ⟨1183536907212262945646861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789024604808175297097907 1183536907212262945646861)
          ·
            refine ⟨443826340204598604617573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1183536907212262945646861 443826340204598604617573)
            ·
              refine ⟨83217438788362238365795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 443826340204598604617573 83217438788362238365795)
              ·
                refine ⟨124826158182543357548693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83217438788362238365795 124826158182543357548693)
                ·
                  refine ⟨5851226164806719885095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124826158182543357548693 5851226164806719885095)
                  ·
                    rfl

theorem cell23_102557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_102557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102557 prefixEnd_102557 := by exact prefixLift 102557
  have htrace : WordTrace (prefixWord ++ tailWord_102557) baseStart_102557 baseEnd_102557 := by
    simpa [prefixWord, tailWord_102557, baseEnd_102557] using wordTrace_append hprefix tailTrace_102557
  have hstable : (prefixWord ++ tailWord_102557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102557).length < 2 ^ (prefixWord ++ tailWord_102557).sum := by decide
  have hdescent : baseEnd_102557 < baseStart_102557 := by decide
  rcases family_descends (prefixWord ++ tailWord_102557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102584 : List Nat := [2, 1, 2, 1, 2, 1, 4, 5, 1, 1, 3]
def baseStart_102584 : Nat := 118140960795 + 102584 * 2 ^ 59
def prefixEnd_102584 : Nat := 4983230072969 + 3 ^ 40 * 102584 * 2
def baseEnd_102584 : Nat := 52674899460931873328231

theorem tailTrace_102584 : CollatzResearch.WordTrace tailWord_102584 prefixEnd_102584 52674899460931873328231 := by
  unfold tailWord_102584
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870772930181581398737403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2494363906908775198316537 1870772930181581398737403)
  ·
    refine ⟨2806159395272372098106105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1870772930181581398737403 2806159395272372098106105)
    ·
      refine ⟨2104619546454279073579579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2806159395272372098106105 2104619546454279073579579)
      ·
        refine ⟨3156929319681418610369369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104619546454279073579579 3156929319681418610369369)
        ·
          refine ⟨2367696989761063957777027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3156929319681418610369369 2367696989761063957777027)
          ·
            refine ⟨3551545484641595936665541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367696989761063957777027 3551545484641595936665541)
            ·
              refine ⟨665914778370299238124789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3551545484641595936665541 665914778370299238124789)
              ·
                refine ⟨62429510472215553574199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 665914778370299238124789 62429510472215553574199)
                ·
                  refine ⟨93644265708323330361299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62429510472215553574199 93644265708323330361299)
                  ·
                    refine ⟨140466398562484995541949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93644265708323330361299 140466398562484995541949)
                    ·
                      refine ⟨52674899460931873328231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 140466398562484995541949 52674899460931873328231)
                      ·
                        rfl

theorem cell23_102584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 1, 1, 3].length) (baseStart_102584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102584 prefixEnd_102584 := by exact prefixLift 102584
  have htrace : WordTrace (prefixWord ++ tailWord_102584) baseStart_102584 baseEnd_102584 := by
    simpa [prefixWord, tailWord_102584, baseEnd_102584] using wordTrace_append hprefix tailTrace_102584
  have hstable : (prefixWord ++ tailWord_102584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102584).length < 2 ^ (prefixWord ++ tailWord_102584).sum := by decide
  have hdescent : baseEnd_102584 < baseStart_102584 := by decide
  rcases family_descends (prefixWord ++ tailWord_102584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102587 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 1, 5]
def baseStart_102587 : Nat := 118140960795 + 102587 * 2 ^ 59
def prefixEnd_102587 : Nat := 4983230072969 + 3 ^ 40 * 102587 * 2
def baseEnd_102587 : Nat := 17558813300965120530239

theorem tailTrace_102587 : CollatzResearch.WordTrace tailWord_102587 prefixEnd_102587 17558813300965120530239 := by
  unfold tailWord_102587
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741655279352294309834015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2494436852901529539889343 3741655279352294309834015)
  ·
    refine ⟨5612482919028441464751023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3741655279352294309834015 5612482919028441464751023)
    ·
      refine ⟨8418724378542662197126535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5612482919028441464751023 8418724378542662197126535)
      ·
        refine ⟨12628086567813993295689803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8418724378542662197126535 12628086567813993295689803)
        ·
          refine ⟨18942129851720989943534705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12628086567813993295689803 18942129851720989943534705)
          ·
            refine ⟨14206597388790742457651029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18942129851720989943534705 14206597388790742457651029)
            ·
              refine ⟨83241781574945756587799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 14206597388790742457651029 83241781574945756587799)
              ·
                refine ⟨124862672362418634881699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83241781574945756587799 124862672362418634881699)
                ·
                  refine ⟨187294008543627952322549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124862672362418634881699 187294008543627952322549)
                  ·
                    refine ⟨17558813300965120530239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187294008543627952322549 17558813300965120530239)
                    ·
                      rfl

theorem cell23_102587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 5].length) (baseStart_102587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102587 prefixEnd_102587 := by exact prefixLift 102587
  have htrace : WordTrace (prefixWord ++ tailWord_102587) baseStart_102587 baseEnd_102587 := by
    simpa [prefixWord, tailWord_102587, baseEnd_102587] using wordTrace_append hprefix tailTrace_102587
  have hstable : (prefixWord ++ tailWord_102587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102587).length < 2 ^ (prefixWord ++ tailWord_102587).sum := by decide
  have hdescent : baseEnd_102587 < baseStart_102587 := by decide
  rcases family_descends (prefixWord ++ tailWord_102587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102617 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 2, 4]
def baseStart_102617 : Nat := 118140960795 + 102617 * 2 ^ 59
def prefixEnd_102617 : Nat := 4983230072969 + 3 ^ 40 * 102617 * 2
def baseEnd_102617 : Nat := 17563948107510081405193

theorem tailTrace_102617 : CollatzResearch.WordTrace tailWord_102617 prefixEnd_102617 17563948107510081405193 := by
  unfold tailWord_102617
  simp only [CollatzResearch.WordTrace]
  refine ⟨3742749469243609433426105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2495166312829072955617403 3742749469243609433426105)
  ·
    refine ⟨2807062101932707075069579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3742749469243609433426105 2807062101932707075069579)
    ·
      refine ⟨4210593152899060612604369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2807062101932707075069579 4210593152899060612604369)
      ·
        refine ⟨3157944864674295459453277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4210593152899060612604369 3157944864674295459453277)
        ·
          refine ⟨1184229324252860797294979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3157944864674295459453277 1184229324252860797294979)
          ·
            refine ⟨1776343986379291195942469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184229324252860797294979 1776343986379291195942469)
            ·
              refine ⟨333064497446117099239213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1776343986379291195942469 333064497446117099239213)
              ·
                refine ⟨124899186542293912214705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333064497446117099239213 124899186542293912214705)
                ·
                  refine ⟨93674389906720434161029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124899186542293912214705 93674389906720434161029)
                  ·
                    refine ⟨17563948107510081405193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93674389906720434161029 17563948107510081405193)
                    ·
                      rfl

theorem cell23_102617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 4].length) (baseStart_102617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102617 prefixEnd_102617 := by exact prefixLift 102617
  have htrace : WordTrace (prefixWord ++ tailWord_102617) baseStart_102617 baseEnd_102617 := by
    simpa [prefixWord, tailWord_102617, baseEnd_102617] using wordTrace_append hprefix tailTrace_102617
  have hstable : (prefixWord ++ tailWord_102617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102617).length < 2 ^ (prefixWord ++ tailWord_102617).sum := by decide
  have hdescent : baseEnd_102617 < baseStart_102617 := by decide
  rcases family_descends (prefixWord ++ tailWord_102617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102624 : List Nat := [2, 1, 1, 3, 1, 3, 3, 2, 3, 2, 2]
def baseStart_102624 : Nat := 118140960795 + 102624 * 2 ^ 59
def prefixEnd_102624 : Nat := 4983230072969 + 3 ^ 40 * 102624 * 2
def baseEnd_102624 : Nat := 52695438687111716828047

theorem tailTrace_102624 : CollatzResearch.WordTrace tailWord_102624 prefixEnd_102624 52695438687111716828047 := by
  unfold tailWord_102624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1871502390109124814465463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2495336520145499752620617 1871502390109124814465463)
  ·
    refine ⟨2807253585163687221698195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1871502390109124814465463 2807253585163687221698195)
    ·
      refine ⟨4210880377745530832547293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2807253585163687221698195 4210880377745530832547293)
      ·
        refine ⟨1579080141654574062205235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4210880377745530832547293 1579080141654574062205235)
        ·
          refine ⟨2368620212481861093307853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579080141654574062205235 2368620212481861093307853)
          ·
            refine ⟨888232579680697909990445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2368620212481861093307853 888232579680697909990445)
            ·
              refine ⟨333087217380261716246417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 888232579680697909990445 333087217380261716246417)
              ·
                refine ⟨249815413035196287184813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333087217380261716246417 249815413035196287184813)
                ·
                  refine ⟨93680779888198607694305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249815413035196287184813 93680779888198607694305)
                  ·
                    refine ⟨70260584916148955770729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93680779888198607694305 70260584916148955770729)
                    ·
                      refine ⟨52695438687111716828047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70260584916148955770729 52695438687111716828047)
                      ·
                        rfl

theorem cell23_102624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 2, 3, 2, 2].length) (baseStart_102624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102624 prefixEnd_102624 := by exact prefixLift 102624
  have htrace : WordTrace (prefixWord ++ tailWord_102624) baseStart_102624 baseEnd_102624 := by
    simpa [prefixWord, tailWord_102624, baseEnd_102624] using wordTrace_append hprefix tailTrace_102624
  have hstable : (prefixWord ++ tailWord_102624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102624).length < 2 ^ (prefixWord ++ tailWord_102624).sum := by decide
  have hdescent : baseEnd_102624 < baseStart_102624 := by decide
  rcases family_descends (prefixWord ++ tailWord_102624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102641 : List Nat := [1, 2, 2, 2, 2, 1, 3, 5, 1, 2, 2]
def baseStart_102641 : Nat := 118140960795 + 102641 * 2 ^ 59
def prefixEnd_102641 : Nat := 4983230072969 + 3 ^ 40 * 102641 * 2
def baseEnd_102641 : Nat := 52704167858238150315469

theorem tailTrace_102641 : CollatzResearch.WordTrace tailWord_102641 prefixEnd_102641 52704167858238150315469 := by
  unfold tailWord_102641
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743624821156661532299777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2495749880771107688199851 3743624821156661532299777)
  ·
    refine ⟨2807718615867496149224833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3743624821156661532299777 2807718615867496149224833)
    ·
      refine ⟨2105788961900622111918625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2807718615867496149224833 2105788961900622111918625)
      ·
        refine ⟨1579341721425466583938969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105788961900622111918625 1579341721425466583938969)
        ·
          refine ⟨1184506291069099937954227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1579341721425466583938969 1184506291069099937954227)
          ·
            refine ⟨1776759436603649906931341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184506291069099937954227 1776759436603649906931341)
            ·
              refine ⟨666284788726368715099253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1776759436603649906931341 666284788726368715099253)
              ·
                refine ⟨62464198943097067040555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 666284788726368715099253 62464198943097067040555)
                ·
                  refine ⟨93696298414645600560833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62464198943097067040555 93696298414645600560833)
                  ·
                    refine ⟨70272223810984200420625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93696298414645600560833 70272223810984200420625)
                    ·
                      refine ⟨52704167858238150315469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70272223810984200420625 52704167858238150315469)
                      ·
                        rfl

theorem cell23_102641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_102641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102641 prefixEnd_102641 := by exact prefixLift 102641
  have htrace : WordTrace (prefixWord ++ tailWord_102641) baseStart_102641 baseEnd_102641 := by
    simpa [prefixWord, tailWord_102641, baseEnd_102641] using wordTrace_append hprefix tailTrace_102641
  have hstable : (prefixWord ++ tailWord_102641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102641).length < 2 ^ (prefixWord ++ tailWord_102641).sum := by decide
  have hdescent : baseEnd_102641 < baseStart_102641 := by decide
  rcases family_descends (prefixWord ++ tailWord_102641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102658 : List Nat := [3, 4, 1, 1, 2, 2, 2, 1, 3, 2, 2]
def baseStart_102658 : Nat := 118140960795 + 102658 * 2 ^ 59
def prefixEnd_102658 : Nat := 4983230072969 + 3 ^ 40 * 102658 * 2
def baseEnd_102658 : Nat := 52712897029364583802891

theorem tailTrace_102658 : CollatzResearch.WordTrace tailWord_102658 prefixEnd_102658 52712897029364583802891 := by
  unfold tailWord_102658
  simp only [CollatzResearch.WordTrace]
  refine ⟨936061215523768358917157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2496163241396715623779085 936061215523768358917157)
  ·
    refine ⟨175511477910706567296967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 936061215523768358917157 175511477910706567296967)
    ·
      refine ⟨263267216866059850945451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175511477910706567296967 263267216866059850945451)
      ·
        refine ⟨394900825299089776418177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263267216866059850945451 394900825299089776418177)
        ·
          refine ⟨296175618974317332313633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394900825299089776418177 296175618974317332313633)
          ·
            refine ⟨222131714230737999235225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296175618974317332313633 222131714230737999235225)
            ·
              refine ⟨166598785673053499426419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222131714230737999235225 166598785673053499426419)
              ·
                refine ⟨249898178509580249139629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166598785673053499426419 249898178509580249139629)
                ·
                  refine ⟨93711816941092593427361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 249898178509580249139629 93711816941092593427361)
                  ·
                    refine ⟨70283862705819445070521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93711816941092593427361 70283862705819445070521)
                    ·
                      refine ⟨52712897029364583802891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70283862705819445070521 52712897029364583802891)
                      ·
                        rfl

theorem cell23_102658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_102658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102658 prefixEnd_102658 := by exact prefixLift 102658
  have htrace : WordTrace (prefixWord ++ tailWord_102658) baseStart_102658 baseEnd_102658 := by
    simpa [prefixWord, tailWord_102658, baseEnd_102658] using wordTrace_append hprefix tailTrace_102658
  have hstable : (prefixWord ++ tailWord_102658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102658).length < 2 ^ (prefixWord ++ tailWord_102658).sum := by decide
  have hdescent : baseEnd_102658 < baseStart_102658 := by decide
  rcases family_descends (prefixWord ++ tailWord_102658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102700 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 5]
def baseStart_102700 : Nat := 118140960795 + 102700 * 2 ^ 59
def prefixEnd_102700 : Nat := 4983230072969 + 3 ^ 40 * 102700 * 2
def baseEnd_102700 : Nat := 52734463216853419477697

theorem tailTrace_102700 : CollatzResearch.WordTrace tailWord_102700 prefixEnd_102700 52734463216853419477697 := by
  unfold tailWord_102700
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872888363971457304348777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2497184485295276405798369 1872888363971457304348777)
  ·
    refine ⟨1404666272978592978261583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1872888363971457304348777 1404666272978592978261583)
    ·
      refine ⟨2106999409467889467392375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1404666272978592978261583 2106999409467889467392375)
      ·
        refine ⟨3160499114201834201088563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106999409467889467392375 3160499114201834201088563)
        ·
          refine ⟨4740748671302751301632845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3160499114201834201088563 4740748671302751301632845)
          ·
            refine ⟨1777780751738531738112317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4740748671302751301632845 1777780751738531738112317)
            ·
              refine ⟨666667781901949401792119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1777780751738531738112317 666667781901949401792119)
              ·
                refine ⟨1000001672852924102688179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 666667781901949401792119 1000001672852924102688179)
                ·
                  refine ⟨1500002509279386154032269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1000001672852924102688179 1500002509279386154032269)
                  ·
                    refine ⟨562500940979769807762101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1500002509279386154032269 562500940979769807762101)
                    ·
                      refine ⟨52734463216853419477697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 562500940979769807762101 52734463216853419477697)
                      ·
                        rfl

theorem cell23_102700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 5].length) (baseStart_102700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102700 prefixEnd_102700 := by exact prefixLift 102700
  have htrace : WordTrace (prefixWord ++ tailWord_102700) baseStart_102700 baseEnd_102700 := by
    simpa [prefixWord, tailWord_102700, baseEnd_102700] using wordTrace_append hprefix tailTrace_102700
  have hstable : (prefixWord ++ tailWord_102700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102700).length < 2 ^ (prefixWord ++ tailWord_102700).sum := by decide
  have hdescent : baseEnd_102700 < baseStart_102700 := by decide
  rcases family_descends (prefixWord ++ tailWord_102700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102720 : List Nat := [2, 1, 1, 2, 2, 1, 2, 5, 7]
def baseStart_102720 : Nat := 118140960795 + 102720 * 2 ^ 59
def prefixEnd_102720 : Nat := 4983230072969 + 3 ^ 40 * 102720 * 2
def baseEnd_102720 : Nat := 5860525869993704580845

theorem tailTrace_102720 : CollatzResearch.WordTrace tailWord_102720 prefixEnd_102720 5860525869993704580845 := by
  unfold tailWord_102720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873253093935229012212807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2497670791913638682950409 1873253093935229012212807)
  ·
    refine ⟨2809879640902843518319211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1873253093935229012212807 2809879640902843518319211)
    ·
      refine ⟨4214819461354265277478817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2809879640902843518319211 4214819461354265277478817)
      ·
        refine ⟨3161114596015698958109113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4214819461354265277478817 3161114596015698958109113)
        ·
          refine ⟨2370835947011774218581835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3161114596015698958109113 2370835947011774218581835)
          ·
            refine ⟨3556253920517661327872753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2370835947011774218581835 3556253920517661327872753)
            ·
              refine ⟨2667190440388245995904565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3556253920517661327872753 2667190440388245995904565)
              ·
                refine ⟨250049103786398062116053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2667190440388245995904565 250049103786398062116053)
                ·
                  refine ⟨5860525869993704580845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250049103786398062116053 5860525869993704580845)
                  ·
                    rfl

theorem cell23_102720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 7].length) (baseStart_102720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102720 prefixEnd_102720 := by exact prefixLift 102720
  have htrace : WordTrace (prefixWord ++ tailWord_102720) baseStart_102720 baseEnd_102720 := by
    simpa [prefixWord, tailWord_102720, baseEnd_102720] using wordTrace_append hprefix tailTrace_102720
  have hstable : (prefixWord ++ tailWord_102720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102720).length < 2 ^ (prefixWord ++ tailWord_102720).sum := by decide
  have hdescent : baseEnd_102720 < baseStart_102720 := by decide
  rcases family_descends (prefixWord ++ tailWord_102720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102748 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 1, 4, 2]
def baseStart_102748 : Nat := 118140960795 + 102748 * 2 ^ 59
def prefixEnd_102748 : Nat := 4983230072969 + 3 ^ 40 * 102748 * 2
def baseEnd_102748 : Nat := 52759110288269231677477

theorem tailTrace_102748 : CollatzResearch.WordTrace tailWord_102748 prefixEnd_102748 52759110288269231677477 := by
  unfold tailWord_102748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1873763715884509403222449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2498351621179345870963265 1873763715884509403222449)
  ·
    refine ⟨1405322786913382052416837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1873763715884509403222449 1405322786913382052416837)
    ·
      refine ⟨263498022546259134828157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1405322786913382052416837 263498022546259134828157)
      ·
        refine ⟨98811758454847175560559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263498022546259134828157 98811758454847175560559)
        ·
          refine ⟨148217637682270763340839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98811758454847175560559 148217637682270763340839)
          ·
            refine ⟨222326456523406145011259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148217637682270763340839 222326456523406145011259)
            ·
              refine ⟨333489684785109217516889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222326456523406145011259 333489684785109217516889)
              ·
                refine ⟨250117263588831913137667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333489684785109217516889 250117263588831913137667)
                ·
                  refine ⟨375175895383247869706501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250117263588831913137667 375175895383247869706501)
                  ·
                    refine ⟨70345480384358975569969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 375175895383247869706501 70345480384358975569969)
                    ·
                      refine ⟨52759110288269231677477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70345480384358975569969 52759110288269231677477)
                      ·
                        rfl

theorem cell23_102748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_102748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102748 prefixEnd_102748 := by exact prefixLift 102748
  have htrace : WordTrace (prefixWord ++ tailWord_102748) baseStart_102748 baseEnd_102748 := by
    simpa [prefixWord, tailWord_102748, baseEnd_102748] using wordTrace_append hprefix tailTrace_102748
  have hstable : (prefixWord ++ tailWord_102748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102748).length < 2 ^ (prefixWord ++ tailWord_102748).sum := by decide
  have hdescent : baseEnd_102748 < baseStart_102748 := by decide
  rcases family_descends (prefixWord ++ tailWord_102748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102857 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 3, 5]
def baseStart_102857 : Nat := 118140960795 + 102857 * 2 ^ 59
def prefixEnd_102857 : Nat := 4983230072969 + 3 ^ 40 * 102857 * 2
def baseEnd_102857 : Nat := 17605026559869768404825

theorem tailTrace_102857 : CollatzResearch.WordTrace tailWord_102857 prefixEnd_102857 17605026559869768404825 := by
  unfold tailWord_102857
  simp only [CollatzResearch.WordTrace]
  refine ⟨3751502988374130422162825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2501001992249420281441883 3751502988374130422162825)
  ·
    refine ⟨2813627241280597816622119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3751502988374130422162825 2813627241280597816622119)
    ·
      refine ⟨4220440861920896724933179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2813627241280597816622119 4220440861920896724933179)
      ·
        refine ⟨6330661292881345087399769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4220440861920896724933179 6330661292881345087399769)
        ·
          refine ⟨4747995969661008815549827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6330661292881345087399769 4747995969661008815549827)
          ·
            refine ⟨7121993954491513223324741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4747995969661008815549827 7121993954491513223324741)
            ·
              refine ⟨1335373866467158729373389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7121993954491513223324741 1335373866467158729373389)
              ·
                refine ⟨500765199925184523515021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1335373866467158729373389 500765199925184523515021)
                ·
                  refine ⟨187786949971944196318133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500765199925184523515021 187786949971944196318133)
                  ·
                    refine ⟨17605026559869768404825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187786949971944196318133 17605026559869768404825)
                    ·
                      rfl

theorem cell23_102857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 5].length) (baseStart_102857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102857 prefixEnd_102857 := by exact prefixLift 102857
  have htrace : WordTrace (prefixWord ++ tailWord_102857) baseStart_102857 baseEnd_102857 := by
    simpa [prefixWord, tailWord_102857, baseEnd_102857] using wordTrace_append hprefix tailTrace_102857
  have hstable : (prefixWord ++ tailWord_102857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102857).length < 2 ^ (prefixWord ++ tailWord_102857).sum := by decide
  have hdescent : baseEnd_102857 < baseStart_102857 := by decide
  rcases family_descends (prefixWord ++ tailWord_102857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102874 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_102874 : Nat := 118140960795 + 102874 * 2 ^ 59
def prefixEnd_102874 : Nat := 4983230072969 + 3 ^ 40 * 102874 * 2
def baseEnd_102874 : Nat := 17607936283578579567299

theorem tailTrace_102874 : CollatzResearch.WordTrace tailWord_102874 prefixEnd_102874 17607936283578579567299 := by
  unfold tailWord_102874
  simp only [CollatzResearch.WordTrace]
  refine ⟨938030757328135581382919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2501415352875028217021117 938030757328135581382919)
  ·
    refine ⟨1407046135992203372074379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 938030757328135581382919 1407046135992203372074379)
    ·
      refine ⟨2110569203988305058111569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407046135992203372074379 2110569203988305058111569)
      ·
        refine ⟨1582926902991228793583677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2110569203988305058111569 1582926902991228793583677)
        ·
          refine ⟨593597588621710797593879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1582926902991228793583677 593597588621710797593879)
          ·
            refine ⟨890396382932566196390819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593597588621710797593879 890396382932566196390819)
            ·
              refine ⟨1335594574398849294586229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 890396382932566196390819 1335594574398849294586229)
              ·
                refine ⟨125211991349892121367459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1335594574398849294586229 125211991349892121367459)
                ·
                  refine ⟨187817987024838182051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125211991349892121367459 187817987024838182051189)
                  ·
                    refine ⟨17607936283578579567299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187817987024838182051189 17607936283578579567299)
                    ·
                      rfl

theorem cell23_102874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_102874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102874 prefixEnd_102874 := by exact prefixLift 102874
  have htrace : WordTrace (prefixWord ++ tailWord_102874) baseStart_102874 baseEnd_102874 := by
    simpa [prefixWord, tailWord_102874, baseEnd_102874] using wordTrace_append hprefix tailTrace_102874
  have hstable : (prefixWord ++ tailWord_102874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102874).length < 2 ^ (prefixWord ++ tailWord_102874).sum := by decide
  have hdescent : baseEnd_102874 < baseStart_102874 := by decide
  rcases family_descends (prefixWord ++ tailWord_102874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102881 : List Nat := [1, 2, 3, 1, 2, 2, 3, 2, 2, 3, 2]
def baseStart_102881 : Nat := 118140960795 + 102881 * 2 ^ 59
def prefixEnd_102881 : Nat := 4983230072969 + 3 ^ 40 * 102881 * 2
def baseEnd_102881 : Nat := 52827403215317211314365

theorem tailTrace_102881 : CollatzResearch.WordTrace tailWord_102881 prefixEnd_102881 52827403215317211314365 := by
  unfold tailWord_102881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3752378340287182521036497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2501585560191455014024331 3752378340287182521036497)
  ·
    refine ⟨2814283755215386890777373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3752378340287182521036497 2814283755215386890777373)
    ·
      refine ⟨1055356408205770084041515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2814283755215386890777373 1055356408205770084041515)
      ·
        refine ⟨1583034612308655126062273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1055356408205770084041515 1583034612308655126062273)
        ·
          refine ⟨1187275959231491344546705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1583034612308655126062273 1187275959231491344546705)
          ·
            refine ⟨890456969423618508410029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1187275959231491344546705 890456969423618508410029)
            ·
              refine ⟨333921363533856940653761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 890456969423618508410029 333921363533856940653761)
              ·
                refine ⟨250441022650392705490321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333921363533856940653761 250441022650392705490321)
                ·
                  refine ⟨187830766987794529117741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250441022650392705490321 187830766987794529117741)
                  ·
                    refine ⟨70436537620422948419153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187830766987794529117741 70436537620422948419153)
                    ·
                      refine ⟨52827403215317211314365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70436537620422948419153 52827403215317211314365)
                      ·
                        rfl

theorem cell23_102881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_102881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102881 prefixEnd_102881 := by exact prefixLift 102881
  have htrace : WordTrace (prefixWord ++ tailWord_102881) baseStart_102881 baseEnd_102881 := by
    simpa [prefixWord, tailWord_102881, baseEnd_102881] using wordTrace_append hprefix tailTrace_102881
  have hstable : (prefixWord ++ tailWord_102881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102881).length < 2 ^ (prefixWord ++ tailWord_102881).sum := by decide
  have hdescent : baseEnd_102881 < baseStart_102881 := by decide
  rcases family_descends (prefixWord ++ tailWord_102881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102882 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_102882 : Nat := 118140960795 + 102882 * 2 ^ 59
def prefixEnd_102882 : Nat := 4983230072969 + 3 ^ 40 * 102882 * 2
def baseEnd_102882 : Nat := 17609305565323902467287

theorem tailTrace_102882 : CollatzResearch.WordTrace tailWord_102882 prefixEnd_102882 17609305565323902467287 := by
  unfold tailWord_102882
  simp only [CollatzResearch.WordTrace]
  refine ⟨938103703320889922955725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2501609875522373127881933 938103703320889922955725)
  ·
    refine ⟨351788888745333721108397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 938103703320889922955725 351788888745333721108397)
    ·
      refine ⟨131920833279500145415649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351788888745333721108397 131920833279500145415649)
      ·
        refine ⟨98940624959625109061737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131920833279500145415649 98940624959625109061737)
        ·
          refine ⟨74205468719718831796303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98940624959625109061737 74205468719718831796303)
          ·
            refine ⟨111308203079578247694455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74205468719718831796303 111308203079578247694455)
            ·
              refine ⟨166962304619367371541683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111308203079578247694455 166962304619367371541683)
              ·
                refine ⟨250443456929051057312525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166962304619367371541683 250443456929051057312525)
                ·
                  refine ⟨93916296348394146492197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250443456929051057312525 93916296348394146492197)
                  ·
                    refine ⟨17609305565323902467287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93916296348394146492197 17609305565323902467287)
                    ·
                      rfl

theorem cell23_102882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_102882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102882 prefixEnd_102882 := by exact prefixLift 102882
  have htrace : WordTrace (prefixWord ++ tailWord_102882) baseStart_102882 baseEnd_102882 := by
    simpa [prefixWord, tailWord_102882, baseEnd_102882] using wordTrace_append hprefix tailTrace_102882
  have hstable : (prefixWord ++ tailWord_102882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102882).length < 2 ^ (prefixWord ++ tailWord_102882).sum := by decide
  have hdescent : baseEnd_102882 < baseStart_102882 := by decide
  rcases family_descends (prefixWord ++ tailWord_102882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102888 : List Nat := [2, 1, 4, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_102888 : Nat := 118140960795 + 102888 * 2 ^ 59
def prefixEnd_102888 : Nat := 4983230072969 + 3 ^ 40 * 102888 * 2
def baseEnd_102888 : Nat := 52830997579898683926833

theorem tailTrace_102888 : CollatzResearch.WordTrace tailWord_102888 prefixEnd_102888 52830997579898683926833 := by
  unfold tailWord_102888
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876316825630911358270659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2501755767507881811027545 1876316825630911358270659)
  ·
    refine ⟨2814475238446367037405989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1876316825630911358270659 2814475238446367037405989)
    ·
      refine ⟨527714107208693819513623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2814475238446367037405989 527714107208693819513623)
      ·
        refine ⟨791571160813040729270435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527714107208693819513623 791571160813040729270435)
        ·
          refine ⟨1187356741219561093905653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 791571160813040729270435 1187356741219561093905653)
          ·
            refine ⟨111314694489333852553655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1187356741219561093905653 111314694489333852553655)
            ·
              refine ⟨166972041734000778830483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111314694489333852553655 166972041734000778830483)
              ·
                refine ⟨250458062601001168245725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166972041734000778830483 250458062601001168245725)
                ·
                  refine ⟨93921773475375438092147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250458062601001168245725 93921773475375438092147)
                  ·
                    refine ⟨140882660213063157138221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93921773475375438092147 140882660213063157138221)
                    ·
                      refine ⟨52830997579898683926833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 140882660213063157138221 52830997579898683926833)
                      ·
                        rfl

theorem cell23_102888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_102888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102888 prefixEnd_102888 := by exact prefixLift 102888
  have htrace : WordTrace (prefixWord ++ tailWord_102888) baseStart_102888 baseEnd_102888 := by
    simpa [prefixWord, tailWord_102888, baseEnd_102888] using wordTrace_append hprefix tailTrace_102888
  have hstable : (prefixWord ++ tailWord_102888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102888).length < 2 ^ (prefixWord ++ tailWord_102888).sum := by decide
  have hdescent : baseEnd_102888 < baseStart_102888 := by decide
  rcases family_descends (prefixWord ++ tailWord_102888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102911 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 5, 2, 2]
def baseStart_102911 : Nat := 118140960795 + 102911 * 2 ^ 59
def prefixEnd_102911 : Nat := 4983230072969 + 3 ^ 40 * 102911 * 2
def baseEnd_102911 : Nat := 52842807634952093939227

theorem tailTrace_102911 : CollatzResearch.WordTrace tailWord_102911 prefixEnd_102911 52842807634952093939227 := by
  unfold tailWord_102911
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753472530178497644628587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2502315020118998429752391 3753472530178497644628587)
  ·
    refine ⟨5630208795267746466942881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3753472530178497644628587 5630208795267746466942881)
    ·
      refine ⟨4222656596450809850207161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5630208795267746466942881 4222656596450809850207161)
      ·
        refine ⟨3166992447338107387655371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4222656596450809850207161 3166992447338107387655371)
        ·
          refine ⟨4750488671007161081483057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3166992447338107387655371 4750488671007161081483057)
          ·
            refine ⟨3562866503255370811112293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4750488671007161081483057 3562866503255370811112293)
            ·
              refine ⟨668037469360382027083555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3562866503255370811112293 668037469360382027083555)
              ·
                refine ⟨1002056204040573040625333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668037469360382027083555 1002056204040573040625333)
                ·
                  refine ⟨93942769128803722558625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1002056204040573040625333 93942769128803722558625)
                  ·
                    refine ⟨70457076846602791918969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93942769128803722558625 70457076846602791918969)
                    ·
                      refine ⟨52842807634952093939227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70457076846602791918969 52842807634952093939227)
                      ·
                        rfl

theorem cell23_102911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 5, 2, 2].length) (baseStart_102911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102911 prefixEnd_102911 := by exact prefixLift 102911
  have htrace : WordTrace (prefixWord ++ tailWord_102911) baseStart_102911 baseEnd_102911 := by
    simpa [prefixWord, tailWord_102911, baseEnd_102911] using wordTrace_append hprefix tailTrace_102911
  have hstable : (prefixWord ++ tailWord_102911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102911).length < 2 ^ (prefixWord ++ tailWord_102911).sum := by decide
  have hdescent : baseEnd_102911 < baseStart_102911 := by decide
  rcases family_descends (prefixWord ++ tailWord_102911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102917 : List Nat := [1, 3, 1, 1, 2, 2, 4, 9]
def baseStart_102917 : Nat := 118140960795 + 102917 * 2 ^ 59
def prefixEnd_102917 : Nat := 4983230072969 + 3 ^ 40 * 102917 * 2
def baseEnd_102917 : Nat := 1957255130328854461637

theorem tailTrace_102917 : CollatzResearch.WordTrace tailWord_102917 prefixEnd_102917 1957255130328854461637 := by
  unfold tailWord_102917
  simp only [CollatzResearch.WordTrace]
  refine ⟨3753691368156760669347005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2502460912104507112898003 3753691368156760669347005)
  ·
    refine ⟨1407634263058785251005127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3753691368156760669347005 1407634263058785251005127)
    ·
      refine ⟨2111451394588177876507691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407634263058785251005127 2111451394588177876507691)
      ·
        refine ⟨3167177091882266814761537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2111451394588177876507691 3167177091882266814761537)
        ·
          refine ⟨2375382818911700111071153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3167177091882266814761537 2375382818911700111071153)
          ·
            refine ⟨1781537114183775083303365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2375382818911700111071153 1781537114183775083303365)
            ·
              refine ⟨334038208909457828119381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1781537114183775083303365 334038208909457828119381)
              ·
                refine ⟨1957255130328854461637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 334038208909457828119381 1957255130328854461637)
                ·
                  rfl

theorem cell23_102917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 9].length) (baseStart_102917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102917 prefixEnd_102917 := by exact prefixLift 102917
  have htrace : WordTrace (prefixWord ++ tailWord_102917) baseStart_102917 baseEnd_102917 := by
    simpa [prefixWord, tailWord_102917, baseEnd_102917] using wordTrace_append hprefix tailTrace_102917
  have hstable : (prefixWord ++ tailWord_102917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102917).length < 2 ^ (prefixWord ++ tailWord_102917).sum := by decide
  have hdescent : baseEnd_102917 < baseStart_102917 := by decide
  rcases family_descends (prefixWord ++ tailWord_102917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102924 : List Nat := [2, 2, 1, 2, 4, 1, 1, 1, 3, 2, 4]
def baseStart_102924 : Nat := 118140960795 + 102924 * 2 ^ 59
def prefixEnd_102924 : Nat := 4983230072969 + 3 ^ 40 * 102924 * 2
def baseEnd_102924 : Nat := 52849482883460543076667

theorem tailTrace_102924 : CollatzResearch.WordTrace tailWord_102924 prefixEnd_102924 52849482883460543076667 := by
  unfold tailWord_102924
  simp only [CollatzResearch.WordTrace]
  refine ⟨1876973339565700432425913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2502631119420933909901217 1876973339565700432425913)
  ·
    refine ⟨1407730004674275324319435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1876973339565700432425913 1407730004674275324319435)
    ·
      refine ⟨2111595007011412986479153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1407730004674275324319435 2111595007011412986479153)
      ·
        refine ⟨1583696255258559739859365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2111595007011412986479153 1583696255258559739859365)
        ·
          refine ⟨296943047860979951223631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1583696255258559739859365 296943047860979951223631)
          ·
            refine ⟨445414571791469926835447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296943047860979951223631 445414571791469926835447)
            ·
              refine ⟨668121857687204890253171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 445414571791469926835447 668121857687204890253171)
              ·
                refine ⟨1002182786530807335379757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 668121857687204890253171 1002182786530807335379757)
                ·
                  refine ⟨375818544949052750767409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1002182786530807335379757 375818544949052750767409)
                  ·
                    refine ⟨281863908711789563075557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 375818544949052750767409 281863908711789563075557)
                    ·
                      refine ⟨52849482883460543076667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 281863908711789563075557 52849482883460543076667)
                      ·
                        rfl

theorem cell23_102924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_102924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102924 prefixEnd_102924 := by exact prefixLift 102924
  have htrace : WordTrace (prefixWord ++ tailWord_102924) baseStart_102924 baseEnd_102924 := by
    simpa [prefixWord, tailWord_102924, baseEnd_102924] using wordTrace_append hprefix tailTrace_102924
  have hstable : (prefixWord ++ tailWord_102924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102924).length < 2 ^ (prefixWord ++ tailWord_102924).sum := by decide
  have hdescent : baseEnd_102924 < baseStart_102924 := by decide
  rcases family_descends (prefixWord ++ tailWord_102924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102945 : List Nat := [1, 2, 3, 2, 2, 1, 3, 4, 1, 2, 2]
def baseStart_102945 : Nat := 118140960795 + 102945 * 2 ^ 59
def prefixEnd_102945 : Nat := 4983230072969 + 3 ^ 40 * 102945 * 2
def baseEnd_102945 : Nat := 52860265977204960914071

theorem tailTrace_102945 : CollatzResearch.WordTrace tailWord_102945 prefixEnd_102945 52860265977204960914071 := by
  unfold tailWord_102945
  simp only [CollatzResearch.WordTrace]
  refine ⟨3754712612055321451366289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2503141741370214300910859 3754712612055321451366289)
  ·
    refine ⟨2816034459041491088524717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3754712612055321451366289 2816034459041491088524717)
    ·
      refine ⟨1056012922140559158196769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2816034459041491088524717 1056012922140559158196769)
      ·
        refine ⟨792009691605419368647577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1056012922140559158196769 792009691605419368647577)
        ·
          refine ⟨594007268704064526485683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792009691605419368647577 594007268704064526485683)
          ·
            refine ⟨891010903056096789728525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594007268704064526485683 891010903056096789728525)
            ·
              refine ⟨334129088646036296148197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891010903056096789728525 334129088646036296148197)
              ·
                refine ⟨62649204121131805527787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 334129088646036296148197 62649204121131805527787)
                ·
                  refine ⟨93973806181697708291681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62649204121131805527787 93973806181697708291681)
                  ·
                    refine ⟨70480354636273281218761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93973806181697708291681 70480354636273281218761)
                    ·
                      refine ⟨52860265977204960914071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70480354636273281218761 52860265977204960914071)
                      ·
                        rfl

theorem cell23_102945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_102945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102945 prefixEnd_102945 := by exact prefixLift 102945
  have htrace : WordTrace (prefixWord ++ tailWord_102945) baseStart_102945 baseEnd_102945 := by
    simpa [prefixWord, tailWord_102945, baseEnd_102945] using wordTrace_append hprefix tailTrace_102945
  have hstable : (prefixWord ++ tailWord_102945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102945).length < 2 ^ (prefixWord ++ tailWord_102945).sum := by decide
  have hdescent : baseEnd_102945 < baseStart_102945 := by decide
  rcases family_descends (prefixWord ++ tailWord_102945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102958 : List Nat := [4, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_102958 : Nat := 118140960795 + 102958 * 2 ^ 59
def prefixEnd_102958 : Nat := 4983230072969 + 3 ^ 40 * 102958 * 2
def baseEnd_102958 : Nat := 52866941225713410051511

theorem tailTrace_102958 : CollatzResearch.WordTrace tailWord_102958 prefixEnd_102958 52866941225713410051511 := by
  unfold tailWord_102958
  simp only [CollatzResearch.WordTrace]
  refine ⟨469398345126028083948691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2503457840672149781059685 469398345126028083948691)
  ·
    refine ⟨704097517689042125923037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 469398345126028083948691 704097517689042125923037)
    ·
      refine ⟨264036569133390797221139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 704097517689042125923037 264036569133390797221139)
      ·
        refine ⟨396054853700086195831709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264036569133390797221139 396054853700086195831709)
        ·
          refine ⟨148520570137532323436891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 396054853700086195831709 148520570137532323436891)
          ·
            refine ⟨222780855206298485155337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148520570137532323436891 222780855206298485155337)
            ·
              refine ⟨167085641404723863866503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222780855206298485155337 167085641404723863866503)
              ·
                refine ⟨250628462107085795799755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167085641404723863866503 250628462107085795799755)
                ·
                  refine ⟨375942693160628693699633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250628462107085795799755 375942693160628693699633)
                  ·
                    refine ⟨281957019870471520274725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 375942693160628693699633 281957019870471520274725)
                    ·
                      refine ⟨52866941225713410051511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 281957019870471520274725 52866941225713410051511)
                      ·
                        rfl

theorem cell23_102958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_102958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102958 prefixEnd_102958 := by exact prefixLift 102958
  have htrace : WordTrace (prefixWord ++ tailWord_102958) baseStart_102958 baseEnd_102958 := by
    simpa [prefixWord, tailWord_102958, baseEnd_102958] using wordTrace_append hprefix tailTrace_102958
  have hstable : (prefixWord ++ tailWord_102958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102958).length < 2 ^ (prefixWord ++ tailWord_102958).sum := by decide
  have hdescent : baseEnd_102958 < baseStart_102958 := by decide
  rcases family_descends (prefixWord ++ tailWord_102958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102982 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_102982 : Nat := 118140960795 + 102982 * 2 ^ 59
def prefixEnd_102982 : Nat := 4983230072969 + 3 ^ 40 * 102982 * 2
def baseEnd_102982 : Nat := 52879264761421316151401

theorem tailTrace_102982 : CollatzResearch.WordTrace tailWord_102982 prefixEnd_102982 52879264761421316151401 := by
  unfold tailWord_102982
  simp only [CollatzResearch.WordTrace]
  refine ⟨117376941028789899076975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2504041408614184513642133 117376941028789899076975)
  ·
    refine ⟨176065411543184848615463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117376941028789899076975 176065411543184848615463)
    ·
      refine ⟨264098117314777272923195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 176065411543184848615463 264098117314777272923195)
      ·
        refine ⟨396147175972165909384793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264098117314777272923195 396147175972165909384793)
        ·
          refine ⟨297110381979124432038595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396147175972165909384793 297110381979124432038595)
          ·
            refine ⟨445665572968686648057893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297110381979124432038595 445665572968686648057893)
            ·
              refine ⟨83562294931628746510855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 445665572968686648057893 83562294931628746510855)
              ·
                refine ⟨125343442397443119766283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83562294931628746510855 125343442397443119766283)
                ·
                  refine ⟨188015163596164679649425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125343442397443119766283 188015163596164679649425)
                  ·
                    refine ⟨141011372697123509737069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188015163596164679649425 141011372697123509737069)
                    ·
                      refine ⟨52879264761421316151401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 141011372697123509737069 52879264761421316151401)
                      ·
                        rfl

theorem cell23_102982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_102982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102982 prefixEnd_102982 := by exact prefixLift 102982
  have htrace : WordTrace (prefixWord ++ tailWord_102982) baseStart_102982 baseEnd_102982 := by
    simpa [prefixWord, tailWord_102982, baseEnd_102982] using wordTrace_append hprefix tailTrace_102982
  have hstable : (prefixWord ++ tailWord_102982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102982).length < 2 ^ (prefixWord ++ tailWord_102982).sum := by decide
  have hdescent : baseEnd_102982 < baseStart_102982 := by decide
  rcases family_descends (prefixWord ++ tailWord_102982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102988 : List Nat := [2, 2, 1, 3, 1, 2, 3, 3, 1, 3, 2]
def baseStart_102988 : Nat := 118140960795 + 102988 * 2 ^ 59
def prefixEnd_102988 : Nat := 4983230072969 + 3 ^ 40 * 102988 * 2
def baseEnd_102988 : Nat := 52882345645348292676373

theorem tailTrace_102988 : CollatzResearch.WordTrace tailWord_102988 prefixEnd_102988 52882345645348292676373 := by
  unfold tailWord_102988
  simp only [CollatzResearch.WordTrace]
  refine ⟨1878140475449769897590809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2504187300599693196787745 1878140475449769897590809)
  ·
    refine ⟨1408605356587327423193107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1878140475449769897590809 1408605356587327423193107)
    ·
      refine ⟨2112908034880991134789661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1408605356587327423193107 2112908034880991134789661)
      ·
        refine ⟨792340513080371675546123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2112908034880991134789661 792340513080371675546123)
        ·
          refine ⟨1188510769620557513319185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 792340513080371675546123 1188510769620557513319185)
          ·
            refine ⟨891383077215418134989389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1188510769620557513319185 891383077215418134989389)
            ·
              refine ⟨334268653955781800621021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 891383077215418134989389 334268653955781800621021)
              ·
                refine ⟨125350745233418175232883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 334268653955781800621021 125350745233418175232883)
                ·
                  refine ⟨188026117850127262849325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125350745233418175232883 188026117850127262849325)
                  ·
                    refine ⟨70509794193797723568497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188026117850127262849325 70509794193797723568497)
                    ·
                      refine ⟨52882345645348292676373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70509794193797723568497 52882345645348292676373)
                      ·
                        rfl

theorem cell23_102988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_102988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102988 prefixEnd_102988 := by exact prefixLift 102988
  have htrace : WordTrace (prefixWord ++ tailWord_102988) baseStart_102988 baseEnd_102988 := by
    simpa [prefixWord, tailWord_102988, baseEnd_102988] using wordTrace_append hprefix tailTrace_102988
  have hstable : (prefixWord ++ tailWord_102988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102988).length < 2 ^ (prefixWord ++ tailWord_102988).sum := by decide
  have hdescent : baseEnd_102988 < baseStart_102988 := by decide
  rcases family_descends (prefixWord ++ tailWord_102988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_102994 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_102994 : Nat := 118140960795 + 102994 * 2 ^ 59
def prefixEnd_102994 : Nat := 4983230072969 + 3 ^ 40 * 102994 * 2
def baseEnd_102994 : Nat := 17628475509758423067115

theorem tailTrace_102994 : CollatzResearch.WordTrace tailWord_102994 prefixEnd_102994 17628475509758423067115 := by
  unfold tailWord_102994
  simp only [CollatzResearch.WordTrace]
  refine ⟨939124947219450704975009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2504333192585201879933357 939124947219450704975009)
  ·
    refine ⟨704343710414588028731257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 939124947219450704975009 704343710414588028731257)
    ·
      refine ⟨528257782810941021548443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 704343710414588028731257 528257782810941021548443)
      ·
        refine ⟨792386674216411532322665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 528257782810941021548443 792386674216411532322665)
        ·
          refine ⟨594290005662308649241999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 792386674216411532322665 594290005662308649241999)
          ·
            refine ⟨891435008493462973862999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 594290005662308649241999 891435008493462973862999)
            ·
              refine ⟨1337152512740194460794499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 891435008493462973862999 1337152512740194460794499)
              ·
                refine ⟨2005728769110291691191749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1337152512740194460794499 2005728769110291691191749)
                ·
                  refine ⟨376074144208179692098453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2005728769110291691191749 376074144208179692098453)
                  ·
                    refine ⟨17628475509758423067115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 376074144208179692098453 17628475509758423067115)
                    ·
                      rfl

theorem cell23_102994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_102994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_102994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_102994 prefixEnd_102994 := by exact prefixLift 102994
  have htrace : WordTrace (prefixWord ++ tailWord_102994) baseStart_102994 baseEnd_102994 := by
    simpa [prefixWord, tailWord_102994, baseEnd_102994] using wordTrace_append hprefix tailTrace_102994
  have hstable : (prefixWord ++ tailWord_102994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_102994).length < 2 ^ (prefixWord ++ tailWord_102994).sum := by decide
  have hdescent : baseEnd_102994 < baseStart_102994 := by decide
  rcases family_descends (prefixWord ++ tailWord_102994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103058 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 7]
def baseStart_103058 : Nat := 118140960795 + 103058 * 2 ^ 59
def prefixEnd_103058 : Nat := 4983230072969 + 3 ^ 40 * 103058 * 2
def baseEnd_103058 : Nat := 5879809921240335422339

theorem tailTrace_103058 : CollatzResearch.WordTrace tailWord_103058 prefixEnd_103058 5879809921240335422339 := by
  unfold tailWord_103058
  simp only [CollatzResearch.WordTrace]
  refine ⟨939708515161485437557457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2505889373763961166819885 939708515161485437557457)
  ·
    refine ⟨704781386371114078168093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 939708515161485437557457 704781386371114078168093)
    ·
      refine ⟨264293019889167779313035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 704781386371114078168093 264293019889167779313035)
      ·
        refine ⟨396439529833751668969553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264293019889167779313035 396439529833751668969553)
        ·
          refine ⟨297329647375313751727165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 396439529833751668969553 297329647375313751727165)
          ·
            refine ⟨111498617765742656897687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 297329647375313751727165 111498617765742656897687)
            ·
              refine ⟨167247926648613985346531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111498617765742656897687 167247926648613985346531)
              ·
                refine ⟨250871889972920978019797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167247926648613985346531 250871889972920978019797)
                ·
                  refine ⟨5879809921240335422339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 250871889972920978019797 5879809921240335422339)
                  ·
                    rfl

theorem cell23_103058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 7].length) (baseStart_103058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103058 prefixEnd_103058 := by exact prefixLift 103058
  have htrace : WordTrace (prefixWord ++ tailWord_103058) baseStart_103058 baseEnd_103058 := by
    simpa [prefixWord, tailWord_103058, baseEnd_103058] using wordTrace_append hprefix tailTrace_103058
  have hstable : (prefixWord ++ tailWord_103058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103058).length < 2 ^ (prefixWord ++ tailWord_103058).sum := by decide
  have hdescent : baseEnd_103058 < baseStart_103058 := by decide
  rcases family_descends (prefixWord ++ tailWord_103058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103091 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 4]
def baseStart_103091 : Nat := 118140960795 + 103091 * 2 ^ 59
def prefixEnd_103091 : Nat := 4983230072969 + 3 ^ 40 * 103091 * 2
def baseEnd_103091 : Nat := 52935234152761389688399

theorem tailTrace_103091 : CollatzResearch.WordTrace tailWord_103091 prefixEnd_103091 52935234152761389688399 := by
  unfold tailWord_103091
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760037669526388386181127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2506691779684258924120751 3760037669526388386181127)
  ·
    refine ⟨5640056504289582579271691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760037669526388386181127 5640056504289582579271691)
    ·
      refine ⟨8460084756434373868907537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5640056504289582579271691 8460084756434373868907537)
      ·
        refine ⟨6345063567325780401680653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8460084756434373868907537 6345063567325780401680653)
        ·
          refine ⟨2379398837747167650630245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6345063567325780401680653 2379398837747167650630245)
          ·
            refine ⟨446137282077593934493171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2379398837747167650630245 446137282077593934493171)
            ·
              refine ⟨669205923116390901739757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446137282077593934493171 669205923116390901739757)
              ·
                refine ⟨250952221168646588152409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669205923116390901739757 250952221168646588152409)
                ·
                  refine ⟨188214165876484941114307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250952221168646588152409 188214165876484941114307)
                  ·
                    refine ⟨282321248814727411671461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188214165876484941114307 282321248814727411671461)
                    ·
                      refine ⟨52935234152761389688399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 282321248814727411671461 52935234152761389688399)
                      ·
                        rfl

theorem cell23_103091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_103091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103091 prefixEnd_103091 := by exact prefixLift 103091
  have htrace : WordTrace (prefixWord ++ tailWord_103091) baseStart_103091 baseEnd_103091 := by
    simpa [prefixWord, tailWord_103091, baseEnd_103091] using wordTrace_append hprefix tailTrace_103091
  have hstable : (prefixWord ++ tailWord_103091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103091).length < 2 ^ (prefixWord ++ tailWord_103091).sum := by decide
  have hdescent : baseEnd_103091 < baseStart_103091 := by decide
  rcases family_descends (prefixWord ++ tailWord_103091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103108 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_103108 : Nat := 118140960795 + 103108 * 2 ^ 59
def prefixEnd_103108 : Nat := 4983230072969 + 3 ^ 40 * 103108 * 2
def baseEnd_103108 : Nat := 52943963323887823175821

theorem tailTrace_103108 : CollatzResearch.WordTrace tailWord_103108 prefixEnd_103108 52943963323887823175821 := by
  unfold tailWord_103108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1880328855232400144774989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2507105140309866859699985 1880328855232400144774989)
  ·
    refine ⟨705123320712150054290621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1880328855232400144774989 705123320712150054290621)
    ·
      refine ⟨264421245267056270358983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 705123320712150054290621 264421245267056270358983)
      ·
        refine ⟨396631867900584405538475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264421245267056270358983 396631867900584405538475)
        ·
          refine ⟨594947801850876608307713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396631867900584405538475 594947801850876608307713)
          ·
            refine ⟨446210851388157456230785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 594947801850876608307713 446210851388157456230785)
            ·
              refine ⟨334658138541118092173089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 446210851388157456230785 334658138541118092173089)
              ·
                refine ⟨250993603905838569129817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 334658138541118092173089 250993603905838569129817)
                ·
                  refine ⟨188245202929378926847363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250993603905838569129817 188245202929378926847363)
                  ·
                    refine ⟨282367804394068390271045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188245202929378926847363 282367804394068390271045)
                    ·
                      refine ⟨52943963323887823175821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 282367804394068390271045 52943963323887823175821)
                      ·
                        rfl

theorem cell23_103108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_103108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103108 prefixEnd_103108 := by exact prefixLift 103108
  have htrace : WordTrace (prefixWord ++ tailWord_103108) baseStart_103108 baseEnd_103108 := by
    simpa [prefixWord, tailWord_103108, baseEnd_103108] using wordTrace_append hprefix tailTrace_103108
  have hstable : (prefixWord ++ tailWord_103108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103108).length < 2 ^ (prefixWord ++ tailWord_103108).sum := by decide
  have hdescent : baseEnd_103108 < baseStart_103108 := by decide
  rcases family_descends (prefixWord ++ tailWord_103108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103111 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 3]
def baseStart_103111 : Nat := 118140960795 + 103111 * 2 ^ 59
def prefixEnd_103111 : Nat := 4983230072969 + 3 ^ 40 * 103111 * 2
def baseEnd_103111 : Nat := 52945503765851311438307

theorem tailTrace_103111 : CollatzResearch.WordTrace tailWord_103111 prefixEnd_103111 52945503765851311438307 := by
  unfold tailWord_103111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760767129453931801909187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2507178086302621201272791 3760767129453931801909187)
  ·
    refine ⟨5641150694180897702863781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760767129453931801909187 5641150694180897702863781)
    ·
      refine ⟨1057715755158918319286959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5641150694180897702863781 1057715755158918319286959)
      ·
        refine ⟨1586573632738377478930439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1057715755158918319286959 1586573632738377478930439)
        ·
          refine ⟨2379860449107566218395659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1586573632738377478930439 2379860449107566218395659)
          ·
            refine ⟨3569790673661349327593489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2379860449107566218395659 3569790673661349327593489)
            ·
              refine ⟨2677343005246011995695117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569790673661349327593489 2677343005246011995695117)
              ·
                refine ⟨1004003626967254498385669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2677343005246011995695117 1004003626967254498385669)
                ·
                  refine ⟨188250680056360218447313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1004003626967254498385669 188250680056360218447313)
                  ·
                    refine ⟨141188010042270163835485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188250680056360218447313 141188010042270163835485)
                    ·
                      refine ⟨52945503765851311438307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 141188010042270163835485 52945503765851311438307)
                      ·
                        rfl

theorem cell23_103111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 2, 3].length) (baseStart_103111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103111 prefixEnd_103111 := by exact prefixLift 103111
  have htrace : WordTrace (prefixWord ++ tailWord_103111) baseStart_103111 baseEnd_103111 := by
    simpa [prefixWord, tailWord_103111, baseEnd_103111] using wordTrace_append hprefix tailTrace_103111
  have hstable : (prefixWord ++ tailWord_103111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103111).length < 2 ^ (prefixWord ++ tailWord_103111).sum := by decide
  have hdescent : baseEnd_103111 < baseStart_103111 := by decide
  rcases family_descends (prefixWord ++ tailWord_103111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103175 : List Nat := [1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 3]
def baseStart_103175 : Nat := 118140960795 + 103175 * 2 ^ 59
def prefixEnd_103175 : Nat := 4983230072969 + 3 ^ 40 * 103175 * 2
def baseEnd_103175 : Nat := 52978366527739061038013

theorem tailTrace_103175 : CollatzResearch.WordTrace tailWord_103175 prefixEnd_103175 52978366527739061038013 := by
  unfold tailWord_103175
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763101401222070732238979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2508734267481380488159319 3763101401222070732238979)
  ·
    refine ⟨5644652101833106098358469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3763101401222070732238979 5644652101833106098358469)
    ·
      refine ⟨1058372269093707393442213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5644652101833106098358469 1058372269093707393442213)
      ·
        refine ⟨198444800455070136270415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1058372269093707393442213 198444800455070136270415)
        ·
          refine ⟨297667200682605204405623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 198444800455070136270415 297667200682605204405623)
          ·
            refine ⟨446500801023907806608435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297667200682605204405623 446500801023907806608435)
            ·
              refine ⟨669751201535861709912653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446500801023907806608435 669751201535861709912653)
              ·
                refine ⟨251156700575948141217245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 669751201535861709912653 251156700575948141217245)
                ·
                  refine ⟨94183762715980552956467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251156700575948141217245 94183762715980552956467)
                  ·
                    refine ⟨141275644073970829434701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94183762715980552956467 141275644073970829434701)
                    ·
                      refine ⟨52978366527739061038013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 141275644073970829434701 52978366527739061038013)
                      ·
                        rfl

theorem cell23_103175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_103175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103175 prefixEnd_103175 := by exact prefixLift 103175
  have htrace : WordTrace (prefixWord ++ tailWord_103175) baseStart_103175 baseEnd_103175 := by
    simpa [prefixWord, tailWord_103175, baseEnd_103175] using wordTrace_append hprefix tailTrace_103175
  have hstable : (prefixWord ++ tailWord_103175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103175).length < 2 ^ (prefixWord ++ tailWord_103175).sum := by decide
  have hdescent : baseEnd_103175 < baseStart_103175 := by decide
  rcases family_descends (prefixWord ++ tailWord_103175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103201 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 5]
def baseStart_103201 : Nat := 118140960795 + 103201 * 2 ^ 59
def prefixEnd_103201 : Nat := 4983230072969 + 3 ^ 40 * 103201 * 2
def baseEnd_103201 : Nat := 52991717024755959312893

theorem tailTrace_103201 : CollatzResearch.WordTrace tailWord_103201 prefixEnd_103201 52991717024755959312893 := by
  unfold tailWord_103201
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764049699127877172685457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2509366466085251448456971 3764049699127877172685457)
  ·
    refine ⟨2823037274345907879514093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3764049699127877172685457 2823037274345907879514093)
    ·
      refine ⟨1058638977879715454817785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2823037274345907879514093 1058638977879715454817785)
      ·
        refine ⟨793979233409786591113339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1058638977879715454817785 793979233409786591113339)
        ·
          refine ⟨1190968850114679886670009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 793979233409786591113339 1190968850114679886670009)
          ·
            refine ⟨893226637586009915002507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190968850114679886670009 893226637586009915002507)
            ·
              refine ⟨1339839956379014872503761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893226637586009915002507 1339839956379014872503761)
              ·
                refine ⟨1004879967284261154377821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339839956379014872503761 1004879967284261154377821)
                ·
                  refine ⟨376829987731597932891683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004879967284261154377821 376829987731597932891683)
                  ·
                    refine ⟨565244981597396899337525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 376829987731597932891683 565244981597396899337525)
                    ·
                      refine ⟨52991717024755959312893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 565244981597396899337525 52991717024755959312893)
                      ·
                        rfl

theorem cell23_103201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_103201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103201 prefixEnd_103201 := by exact prefixLift 103201
  have htrace : WordTrace (prefixWord ++ tailWord_103201) baseStart_103201 baseEnd_103201 := by
    simpa [prefixWord, tailWord_103201, baseEnd_103201] using wordTrace_append hprefix tailTrace_103201
  have hstable : (prefixWord ++ tailWord_103201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103201).length < 2 ^ (prefixWord ++ tailWord_103201).sum := by decide
  have hdescent : baseEnd_103201 < baseStart_103201 := by decide
  rcases family_descends (prefixWord ++ tailWord_103201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103208 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 6, 4]
def baseStart_103208 : Nat := 118140960795 + 103208 * 2 ^ 59
def prefixEnd_103208 : Nat := 4983230072969 + 3 ^ 40 * 103208 * 2
def baseEnd_103208 : Nat := 17665103796445810641787

theorem tailTrace_103208 : CollatzResearch.WordTrace tailWord_103208 prefixEnd_103208 17665103796445810641787 := by
  unfold tailWord_103208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882152505051258684095139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2509536673401678245460185 1882152505051258684095139)
  ·
    refine ⟨2823228757576888026142709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882152505051258684095139 2823228757576888026142709)
    ·
      refine ⟨264677696022833252450879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2823228757576888026142709 264677696022833252450879)
      ·
        refine ⟨397016544034249878676319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264677696022833252450879 397016544034249878676319)
        ·
          refine ⟨595524816051374818014479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397016544034249878676319 595524816051374818014479)
          ·
            refine ⟨893287224077062227021719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595524816051374818014479 893287224077062227021719)
            ·
              refine ⟨1339930836115593340532579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893287224077062227021719 1339930836115593340532579)
              ·
                refine ⟨2009896254173390010798869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339930836115593340532579 2009896254173390010798869)
                ·
                  refine ⟨94213886914377656756197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2009896254173390010798869 94213886914377656756197)
                  ·
                    refine ⟨17665103796445810641787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94213886914377656756197 17665103796445810641787)
                    ·
                      rfl

theorem cell23_103208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_103208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103208 prefixEnd_103208 := by exact prefixLift 103208
  have htrace : WordTrace (prefixWord ++ tailWord_103208) baseStart_103208 baseEnd_103208 := by
    simpa [prefixWord, tailWord_103208, baseEnd_103208] using wordTrace_append hprefix tailTrace_103208
  have hstable : (prefixWord ++ tailWord_103208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103208).length < 2 ^ (prefixWord ++ tailWord_103208).sum := by decide
  have hdescent : baseEnd_103208 < baseStart_103208 := by decide
  rcases family_descends (prefixWord ++ tailWord_103208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103218 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5]
def baseStart_103218 : Nat := 118140960795 + 103218 * 2 ^ 59
def prefixEnd_103218 : Nat := 4983230072969 + 3 ^ 40 * 103218 * 2
def baseEnd_103218 : Nat := 53000446195882392800315

theorem tailTrace_103218 : CollatzResearch.WordTrace tailWord_103218 prefixEnd_103218 53000446195882392800315 := by
  unfold tailWord_103218
  simp only [CollatzResearch.WordTrace]
  refine ⟨941167435016572269013577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2509779826710859384036205 941167435016572269013577)
  ·
    refine ⟨705875576262429201760183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 941167435016572269013577 705875576262429201760183)
    ·
      refine ⟨1058813364393643802640275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 705875576262429201760183 1058813364393643802640275)
      ·
        refine ⟨1588220046590465703960413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058813364393643802640275 1588220046590465703960413)
        ·
          refine ⟨595582517471424638985155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1588220046590465703960413 595582517471424638985155)
          ·
            refine ⟨893373776207136958477733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595582517471424638985155 893373776207136958477733)
            ·
              refine ⟨167507583038838179714575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 893373776207136958477733 167507583038838179714575)
              ·
                refine ⟨251261374558257269571863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167507583038838179714575 251261374558257269571863)
                ·
                  refine ⟨376892061837385904357795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251261374558257269571863 376892061837385904357795)
                  ·
                    refine ⟨565338092756078856536693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 376892061837385904357795 565338092756078856536693)
                    ·
                      refine ⟨53000446195882392800315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 565338092756078856536693 53000446195882392800315)
                      ·
                        rfl

theorem cell23_103218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_103218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103218 prefixEnd_103218 := by exact prefixLift 103218
  have htrace : WordTrace (prefixWord ++ tailWord_103218) baseStart_103218 baseEnd_103218 := by
    simpa [prefixWord, tailWord_103218, baseEnd_103218] using wordTrace_append hprefix tailTrace_103218
  have hstable : (prefixWord ++ tailWord_103218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103218).length < 2 ^ (prefixWord ++ tailWord_103218).sum := by decide
  have hdescent : baseEnd_103218 < baseStart_103218 := by decide
  rcases family_descends (prefixWord ++ tailWord_103218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103221 : List Nat := [1, 3, 3, 1, 3, 1, 11]
def baseStart_103221 : Nat := 118140960795 + 103221 * 2 ^ 59
def prefixEnd_103221 : Nat := 4983230072969 + 3 ^ 40 * 103221 * 2
def baseEnd_103221 : Nat := 654345514047480013121

theorem tailTrace_103221 : CollatzResearch.WordTrace tailWord_103221 prefixEnd_103221 654345514047480013121 := by
  unfold tailWord_103221
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764779159055420588413517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2509852772703613725609011 3764779159055420588413517)
  ·
    refine ⟨1411792184645782720655069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3764779159055420588413517 1411792184645782720655069)
    ·
      refine ⟨529422069242168520245651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1411792184645782720655069 529422069242168520245651)
      ·
        refine ⟨794133103863252780368477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529422069242168520245651 794133103863252780368477)
        ·
          refine ⟨297799913948719792638179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794133103863252780368477 297799913948719792638179)
          ·
            refine ⟨446699870923079688957269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297799913948719792638179 446699870923079688957269)
            ·
              refine ⟨654345514047480013121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 446699870923079688957269 654345514047480013121)
              ·
                rfl

theorem cell23_103221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 11].length) (baseStart_103221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103221 prefixEnd_103221 := by exact prefixLift 103221
  have htrace : WordTrace (prefixWord ++ tailWord_103221) baseStart_103221 baseEnd_103221 := by
    simpa [prefixWord, tailWord_103221, baseEnd_103221] using wordTrace_append hprefix tailTrace_103221
  have hstable : (prefixWord ++ tailWord_103221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103221).length < 2 ^ (prefixWord ++ tailWord_103221).sum := by decide
  have hdescent : baseEnd_103221 < baseStart_103221 := by decide
  rcases family_descends (prefixWord ++ tailWord_103221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103232 : List Nat := [2, 1, 1, 2, 2, 1, 1, 8, 1, 2, 2]
def baseStart_103232 : Nat := 118140960795 + 103232 * 2 ^ 59
def prefixEnd_103232 : Nat := 4983230072969 + 3 ^ 40 * 103232 * 2
def baseEnd_103232 : Nat := 53007634925045338025251

theorem tailTrace_103232 : CollatzResearch.WordTrace tailWord_103232 prefixEnd_103232 53007634925045338025251 := by
  unfold tailWord_103232
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882590181007784733531975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2510120241343712978042633 1882590181007784733531975)
  ·
    refine ⟨2823885271511677100297963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882590181007784733531975 2823885271511677100297963)
    ·
      refine ⟨4235827907267515650446945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823885271511677100297963 4235827907267515650446945)
      ·
        refine ⟨3176870930450636737835209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4235827907267515650446945 3176870930450636737835209)
        ·
          refine ⟨2382653197837977553376407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3176870930450636737835209 2382653197837977553376407)
          ·
            refine ⟨3573979796756966330064611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382653197837977553376407 3573979796756966330064611)
            ·
              refine ⟨5360969695135449495096917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573979796756966330064611 5360969695135449495096917)
              ·
                refine ⟨62823863614868548770667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5360969695135449495096917 62823863614868548770667)
                ·
                  refine ⟨94235795422302823156001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62823863614868548770667 94235795422302823156001)
                  ·
                    refine ⟨70676846566727117367001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94235795422302823156001 70676846566727117367001)
                    ·
                      refine ⟨53007634925045338025251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70676846566727117367001 53007634925045338025251)
                      ·
                        rfl

theorem cell23_103232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 8, 1, 2, 2].length) (baseStart_103232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103232 prefixEnd_103232 := by exact prefixLift 103232
  have htrace : WordTrace (prefixWord ++ tailWord_103232) baseStart_103232 baseEnd_103232 := by
    simpa [prefixWord, tailWord_103232, baseEnd_103232] using wordTrace_append hprefix tailTrace_103232
  have hstable : (prefixWord ++ tailWord_103232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103232).length < 2 ^ (prefixWord ++ tailWord_103232).sum := by decide
  have hdescent : baseEnd_103232 < baseStart_103232 := by decide
  rcases family_descends (prefixWord ++ tailWord_103232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103275 : List Nat := [1, 1, 1, 1, 2, 2, 4, 5, 1, 3, 2]
def baseStart_103275 : Nat := 118140960795 + 103275 * 2 ^ 59
def prefixEnd_103275 : Nat := 4983230072969 + 3 ^ 40 * 103275 * 2
def baseEnd_103275 : Nat := 53029714593188669787553

theorem tailTrace_103275 : CollatzResearch.WordTrace tailWord_103275 prefixEnd_103275 53029714593188669787553 := by
  unfold tailWord_103275
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766748700859787810879279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2511165800573191873919519 3766748700859787810879279)
  ·
    refine ⟨5650123051289681716318919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3766748700859787810879279 5650123051289681716318919)
    ·
      refine ⟨8475184576934522574478379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650123051289681716318919 8475184576934522574478379)
      ·
        refine ⟨12712776865401783861717569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8475184576934522574478379 12712776865401783861717569)
        ·
          refine ⟨9534582649051337896288177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12712776865401783861717569 9534582649051337896288177)
          ·
            refine ⟨7150936986788503422216133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9534582649051337896288177 7150936986788503422216133)
            ·
              refine ⟨1340800685022844391665525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7150936986788503422216133 1340800685022844391665525)
              ·
                refine ⟨125700064220891661718643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1340800685022844391665525 125700064220891661718643)
                ·
                  refine ⟨188550096331337492577965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125700064220891661718643 188550096331337492577965)
                  ·
                    refine ⟨70706286124251559716737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 188550096331337492577965 70706286124251559716737)
                    ·
                      refine ⟨53029714593188669787553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70706286124251559716737 53029714593188669787553)
                      ·
                        rfl

theorem cell23_103275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 3, 2].length) (baseStart_103275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103275 prefixEnd_103275 := by exact prefixLift 103275
  have htrace : WordTrace (prefixWord ++ tailWord_103275) baseStart_103275 baseEnd_103275 := by
    simpa [prefixWord, tailWord_103275, baseEnd_103275] using wordTrace_append hprefix tailTrace_103275
  have hstable : (prefixWord ++ tailWord_103275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103275).length < 2 ^ (prefixWord ++ tailWord_103275).sum := by decide
  have hdescent : baseEnd_103275 < baseStart_103275 := by decide
  rcases family_descends (prefixWord ++ tailWord_103275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103291 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5]
def baseStart_103291 : Nat := 118140960795 + 103291 * 2 ^ 59
def prefixEnd_103291 : Nat := 4983230072969 + 3 ^ 40 * 103291 * 2
def baseEnd_103291 : Nat := 53037930283660607187479

theorem tailTrace_103291 : CollatzResearch.WordTrace tailWord_103291 prefixEnd_103291 53037930283660607187479 := by
  unfold tailWord_103291
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767332268801822543461727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2511554845867881695641151 3767332268801822543461727)
  ·
    refine ⟨5650998403202733815192591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3767332268801822543461727 5650998403202733815192591)
    ·
      refine ⟨8476497604804100722788887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5650998403202733815192591 8476497604804100722788887)
      ·
        refine ⟨12714746407206151084183331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476497604804100722788887 12714746407206151084183331)
        ·
          refine ⟨19072119610809226626274997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12714746407206151084183331 19072119610809226626274997)
          ·
            refine ⟨1788011213513364996213281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19072119610809226626274997 1788011213513364996213281)
            ·
              refine ⟨1341008410135023747159961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788011213513364996213281 1341008410135023747159961)
              ·
                refine ⟨1005756307601267810369971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341008410135023747159961 1005756307601267810369971)
                ·
                  refine ⟨1508634461401901715554957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005756307601267810369971 1508634461401901715554957)
                  ·
                    refine ⟨565737923025713143333109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1508634461401901715554957 565737923025713143333109)
                    ·
                      refine ⟨53037930283660607187479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 565737923025713143333109 53037930283660607187479)
                      ·
                        rfl

theorem cell23_103291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 3, 5].length) (baseStart_103291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103291 prefixEnd_103291 := by exact prefixLift 103291
  have htrace : WordTrace (prefixWord ++ tailWord_103291) baseStart_103291 baseEnd_103291 := by
    simpa [prefixWord, tailWord_103291, baseEnd_103291] using wordTrace_append hprefix tailTrace_103291
  have hstable : (prefixWord ++ tailWord_103291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103291).length < 2 ^ (prefixWord ++ tailWord_103291).sum := by decide
  have hdescent : baseEnd_103291 < baseStart_103291 := by decide
  rcases family_descends (prefixWord ++ tailWord_103291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103305 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 1, 4, 2]
def baseStart_103305 : Nat := 118140960795 + 103305 * 2 ^ 59
def prefixEnd_103305 : Nat := 4983230072969 + 3 ^ 40 * 103305 * 2
def baseEnd_103305 : Nat := 53045119012823552412415

theorem tailTrace_103305 : CollatzResearch.WordTrace tailWord_103305 prefixEnd_103305 53045119012823552412415 := by
  unfold tailWord_103305
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767842890751102934471369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2511895260500735289647579 3767842890751102934471369)
  ·
    refine ⟨2825882168063327200853527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3767842890751102934471369 2825882168063327200853527)
    ·
      refine ⟨4238823252094990801280291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2825882168063327200853527 4238823252094990801280291)
      ·
        refine ⟨6358234878142486201920437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238823252094990801280291 6358234878142486201920437)
        ·
          refine ⟨596084519825858081430041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6358234878142486201920437 596084519825858081430041)
          ·
            refine ⟨447063389869393561072531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596084519825858081430041 447063389869393561072531)
            ·
              refine ⟨670595084804090341608797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447063389869393561072531 670595084804090341608797)
              ·
                refine ⟨251473156801533878103299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670595084804090341608797 251473156801533878103299)
                ·
                  refine ⟨377209735202300817154949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251473156801533878103299 377209735202300817154949)
                  ·
                    refine ⟨70726825350431403216553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 377209735202300817154949 70726825350431403216553)
                    ·
                      refine ⟨53045119012823552412415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70726825350431403216553 53045119012823552412415)
                      ·
                        rfl

theorem cell23_103305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 4, 2].length) (baseStart_103305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103305 prefixEnd_103305 := by exact prefixLift 103305
  have htrace : WordTrace (prefixWord ++ tailWord_103305) baseStart_103305 baseEnd_103305 := by
    simpa [prefixWord, tailWord_103305, baseEnd_103305] using wordTrace_append hprefix tailTrace_103305
  have hstable : (prefixWord ++ tailWord_103305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103305).length < 2 ^ (prefixWord ++ tailWord_103305).sum := by decide
  have hdescent : baseEnd_103305 < baseStart_103305 := by decide
  rcases family_descends (prefixWord ++ tailWord_103305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103321 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 7]
def baseStart_103321 : Nat := 118140960795 + 103321 * 2 ^ 59
def prefixEnd_103321 : Nat := 4983230072969 + 3 ^ 40 * 103321 * 2
def baseEnd_103321 : Nat := 53053334703295489812341

theorem tailTrace_103321 : CollatzResearch.WordTrace tailWord_103321 prefixEnd_103321 53053334703295489812341 := by
  unfold tailWord_103321
  simp only [CollatzResearch.WordTrace]
  refine ⟨3768426458693137667053817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2512284305795425111369211 3768426458693137667053817)
  ·
    refine ⟨2826319844019853250290363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3768426458693137667053817 2826319844019853250290363)
    ·
      refine ⟨4239479766029779875435545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2826319844019853250290363 4239479766029779875435545)
      ·
        refine ⟨3179609824522334906576659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4239479766029779875435545 3179609824522334906576659)
        ·
          refine ⟨4769414736783502359864989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179609824522334906576659 4769414736783502359864989)
          ·
            refine ⟨1788530526293813384949371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4769414736783502359864989 1788530526293813384949371)
            ·
              refine ⟨2682795789440720077424057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788530526293813384949371 2682795789440720077424057)
              ·
                refine ⟨2012096842080540058068043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682795789440720077424057 2012096842080540058068043)
                ·
                  refine ⟨3018145263120810087102065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012096842080540058068043 3018145263120810087102065)
                  ·
                    refine ⟨2263608947340607565326549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018145263120810087102065 2263608947340607565326549)
                    ·
                      refine ⟨53053334703295489812341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2263608947340607565326549 53053334703295489812341)
                      ·
                        rfl

theorem cell23_103321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_103321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103321 prefixEnd_103321 := by exact prefixLift 103321
  have htrace : WordTrace (prefixWord ++ tailWord_103321) baseStart_103321 baseEnd_103321 := by
    simpa [prefixWord, tailWord_103321, baseEnd_103321] using wordTrace_append hprefix tailTrace_103321
  have hstable : (prefixWord ++ tailWord_103321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103321).length < 2 ^ (prefixWord ++ tailWord_103321).sum := by decide
  have hdescent : baseEnd_103321 < baseStart_103321 := by decide
  rcases family_descends (prefixWord ++ tailWord_103321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103345 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 7]
def baseStart_103345 : Nat := 118140960795 + 103345 * 2 ^ 59
def prefixEnd_103345 : Nat := 4983230072969 + 3 ^ 40 * 103345 * 2
def baseEnd_103345 : Nat := 5896184248778155101359

theorem tailTrace_103345 : CollatzResearch.WordTrace tailWord_103345 prefixEnd_103345 5896184248778155101359 := by
  unfold tailWord_103345
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769301810606189765927489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2512867873737459843951659 3769301810606189765927489)
  ·
    refine ⟨2826976357954642324445617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3769301810606189765927489 2826976357954642324445617)
    ·
      refine ⟨2120232268465981743334213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2826976357954642324445617 2120232268465981743334213)
      ·
        refine ⟨397543550337371576875165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2120232268465981743334213 397543550337371576875165)
        ·
          refine ⟨149078831376514341328187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 397543550337371576875165 149078831376514341328187)
          ·
            refine ⟨223618247064771511992281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149078831376514341328187 223618247064771511992281)
            ·
              refine ⟨167713685298578633994211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223618247064771511992281 167713685298578633994211)
              ·
                refine ⟨251570527947867950991317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167713685298578633994211 251570527947867950991317)
                ·
                  refine ⟨5896184248778155101359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 251570527947867950991317 5896184248778155101359)
                  ·
                    rfl

theorem cell23_103345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 7].length) (baseStart_103345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103345 prefixEnd_103345 := by exact prefixLift 103345
  have htrace : WordTrace (prefixWord ++ tailWord_103345) baseStart_103345 baseEnd_103345 := by
    simpa [prefixWord, tailWord_103345, baseEnd_103345] using wordTrace_append hprefix tailTrace_103345
  have hstable : (prefixWord ++ tailWord_103345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103345).length < 2 ^ (prefixWord ++ tailWord_103345).sum := by decide
  have hdescent : baseEnd_103345 < baseStart_103345 := by decide
  rcases family_descends (prefixWord ++ tailWord_103345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103350 : List Nat := [5, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3]
def baseStart_103350 : Nat := 118140960795 + 103350 * 2 ^ 59
def prefixEnd_103350 : Nat := 4983230072969 + 3 ^ 40 * 103350 * 2
def baseEnd_103350 : Nat := 53068225642275876349709

theorem tailTrace_103350 : CollatzResearch.WordTrace tailWord_103350 prefixEnd_103350 53068225642275876349709 := by
  unfold tailWord_103350
  simp only [CollatzResearch.WordTrace]
  refine ⟨235592760974254726241219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2512989450392050413239669 235592760974254726241219)
  ·
    refine ⟨353389141461382089361829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 235592760974254726241219 353389141461382089361829)
    ·
      refine ⟨66260464024009141755343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 353389141461382089361829 66260464024009141755343)
      ·
        refine ⟨99390696036013712633015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66260464024009141755343 99390696036013712633015)
        ·
          refine ⟨149086044054020568949523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99390696036013712633015 149086044054020568949523)
          ·
            refine ⟨223629066081030853424285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149086044054020568949523 223629066081030853424285)
            ·
              refine ⟨83860899780386570034107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 223629066081030853424285 83860899780386570034107)
              ·
                refine ⟨125791349670579855051161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83860899780386570034107 125791349670579855051161)
                ·
                  refine ⟨94343512252934891288371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125791349670579855051161 94343512252934891288371)
                  ·
                    refine ⟨141515268379402336932557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94343512252934891288371 141515268379402336932557)
                    ·
                      refine ⟨53068225642275876349709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 141515268379402336932557 53068225642275876349709)
                      ·
                        rfl

theorem cell23_103350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_103350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103350 prefixEnd_103350 := by exact prefixLift 103350
  have htrace : WordTrace (prefixWord ++ tailWord_103350) baseStart_103350 baseEnd_103350 := by
    simpa [prefixWord, tailWord_103350, baseEnd_103350] using wordTrace_append hprefix tailTrace_103350
  have hstable : (prefixWord ++ tailWord_103350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103350).length < 2 ^ (prefixWord ++ tailWord_103350).sum := by decide
  have hdescent : baseEnd_103350 < baseStart_103350 := by decide
  rcases family_descends (prefixWord ++ tailWord_103350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103358 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_103358 : Nat := 118140960795 + 103358 * 2 ^ 59
def prefixEnd_103358 : Nat := 4983230072969 + 3 ^ 40 * 103358 * 2
def baseEnd_103358 : Nat := 17690777829170615016557

theorem tailTrace_103358 : CollatzResearch.WordTrace tailWord_103358 prefixEnd_103358 17690777829170615016557 := by
  unfold tailWord_103358
  simp only [CollatzResearch.WordTrace]
  refine ⟨471221994944886623268841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2513183973039395324100485 471221994944886623268841)
  ·
    refine ⟨353416496208664967451631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 471221994944886623268841 353416496208664967451631)
    ·
      refine ⟨530124744312997451177447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353416496208664967451631 530124744312997451177447)
      ·
        refine ⟨795187116469496176766171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530124744312997451177447 795187116469496176766171)
        ·
          refine ⟨1192780674704244265149257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795187116469496176766171 1192780674704244265149257)
          ·
            refine ⟨894585506028183198861943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192780674704244265149257 894585506028183198861943)
            ·
              refine ⟨1341878259042274798292915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894585506028183198861943 1341878259042274798292915)
              ·
                refine ⟨2012817388563412197439373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341878259042274798292915 2012817388563412197439373)
                ·
                  refine ⟨754806520711279574039765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2012817388563412197439373 754806520711279574039765)
                  ·
                    refine ⟨17690777829170615016557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 754806520711279574039765 17690777829170615016557)
                    ·
                      rfl

theorem cell23_103358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_103358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103358 prefixEnd_103358 := by exact prefixLift 103358
  have htrace : WordTrace (prefixWord ++ tailWord_103358) baseStart_103358 baseEnd_103358 := by
    simpa [prefixWord, tailWord_103358, baseEnd_103358] using wordTrace_append hprefix tailTrace_103358
  have hstable : (prefixWord ++ tailWord_103358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103358).length < 2 ^ (prefixWord ++ tailWord_103358).sum := by decide
  have hdescent : baseEnd_103358 < baseStart_103358 := by decide
  rcases family_descends (prefixWord ++ tailWord_103358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103395 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 4]
def baseStart_103395 : Nat := 118140960795 + 103395 * 2 ^ 59
def prefixEnd_103395 : Nat := 4983230072969 + 3 ^ 40 * 103395 * 2
def baseEnd_103395 : Nat := 53091332271728200287001

theorem tailTrace_103395 : CollatzResearch.WordTrace tailWord_103395 prefixEnd_103395 53091332271728200287001 := by
  unfold tailWord_103395
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771125460425048305247639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2514083640283365536831759 3771125460425048305247639)
  ·
    refine ⟨5656688190637572457871459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3771125460425048305247639 5656688190637572457871459)
    ·
      refine ⟨8485032285956358686807189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5656688190637572457871459 8485032285956358686807189)
      ·
        refine ⟨397735888404204313444087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8485032285956358686807189 397735888404204313444087)
        ·
          refine ⟨596603832606306470166131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397735888404204313444087 596603832606306470166131)
          ·
            refine ⟨894905748909459705249197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596603832606306470166131 894905748909459705249197)
            ·
              refine ⟨335589655841047389468449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 894905748909459705249197 335589655841047389468449)
              ·
                refine ⟨251692241880785542101337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335589655841047389468449 251692241880785542101337)
                ·
                  refine ⟨188769181410589156576003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251692241880785542101337 188769181410589156576003)
                  ·
                    refine ⟨283153772115883734864005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188769181410589156576003 283153772115883734864005)
                    ·
                      refine ⟨53091332271728200287001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 283153772115883734864005 53091332271728200287001)
                      ·
                        rfl

theorem cell23_103395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_103395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103395 prefixEnd_103395 := by exact prefixLift 103395
  have htrace : WordTrace (prefixWord ++ tailWord_103395) baseStart_103395 baseEnd_103395 := by
    simpa [prefixWord, tailWord_103395, baseEnd_103395] using wordTrace_append hprefix tailTrace_103395
  have hstable : (prefixWord ++ tailWord_103395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103395).length < 2 ^ (prefixWord ++ tailWord_103395).sum := by decide
  have hdescent : baseEnd_103395 < baseStart_103395 := by decide
  rcases family_descends (prefixWord ++ tailWord_103395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103432 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 2, 2, 3]
def baseStart_103432 : Nat := 118140960795 + 103432 * 2 ^ 59
def prefixEnd_103432 : Nat := 4983230072969 + 3 ^ 40 * 103432 * 2
def baseEnd_103432 : Nat := 53110331055944555524331

theorem tailTrace_103432 : CollatzResearch.WordTrace tailWord_103432 prefixEnd_103432 53110331055944555524331 := by
  unfold tailWord_103432
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886237480645501812172275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2514983307527335749563033 1886237480645501812172275)
  ·
    refine ⟨2829356220968252718258413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1886237480645501812172275 2829356220968252718258413)
    ·
      refine ⟨1061008582863094769346905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2829356220968252718258413 1061008582863094769346905)
      ·
        refine ⟨795756437147321077010179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061008582863094769346905 795756437147321077010179)
        ·
          refine ⟨1193634655720981615515269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795756437147321077010179 1193634655720981615515269)
          ·
            refine ⟨223806497947684052909113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1193634655720981615515269 223806497947684052909113)
            ·
              refine ⟨167854873460763039681835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223806497947684052909113 167854873460763039681835)
              ·
                refine ⟨251782310191144559522753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167854873460763039681835 251782310191144559522753)
                ·
                  refine ⟨188836732643358419642065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 251782310191144559522753 188836732643358419642065)
                  ·
                    refine ⟨141627549482518814731549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 188836732643358419642065 141627549482518814731549)
                    ·
                      refine ⟨53110331055944555524331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 141627549482518814731549 53110331055944555524331)
                      ·
                        rfl

theorem cell23_103432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_103432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103432 prefixEnd_103432 := by exact prefixLift 103432
  have htrace : WordTrace (prefixWord ++ tailWord_103432) baseStart_103432 baseEnd_103432 := by
    simpa [prefixWord, tailWord_103432, baseEnd_103432] using wordTrace_append hprefix tailTrace_103432
  have hstable : (prefixWord ++ tailWord_103432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103432).length < 2 ^ (prefixWord ++ tailWord_103432).sum := by decide
  have hdescent : baseEnd_103432 < baseStart_103432 := by decide
  rcases family_descends (prefixWord ++ tailWord_103432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103452 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 6]
def baseStart_103452 : Nat := 118140960795 + 103452 * 2 ^ 59
def prefixEnd_103452 : Nat := 4983230072969 + 3 ^ 40 * 103452 * 2
def baseEnd_103452 : Nat := 5902288963226053030471

theorem tailTrace_103452 : CollatzResearch.WordTrace tailWord_103452 prefixEnd_103452 5902288963226053030471 := by
  unfold tailWord_103452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886602210609273520036305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2515469614145698026715073 1886602210609273520036305)
  ·
    refine ⟨1414951657956955140027229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1886602210609273520036305 1414951657956955140027229)
    ·
      refine ⟨530606871733858177510211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1414951657956955140027229 530606871733858177510211)
      ·
        refine ⟨795910307600787266265317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530606871733858177510211 795910307600787266265317)
        ·
          refine ⟨149233182675147612424747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 795910307600787266265317 149233182675147612424747)
          ·
            refine ⟨223849774012721418637121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149233182675147612424747 223849774012721418637121)
            ·
              refine ⟨167887330509541063977841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 223849774012721418637121 167887330509541063977841)
              ·
                refine ⟨125915497882155797983381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 167887330509541063977841 125915497882155797983381)
                ·
                  refine ⟨5902288963226053030471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125915497882155797983381 5902288963226053030471)
                  ·
                    rfl

theorem cell23_103452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 6].length) (baseStart_103452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103452 prefixEnd_103452 := by exact prefixLift 103452
  have htrace : WordTrace (prefixWord ++ tailWord_103452) baseStart_103452 baseEnd_103452 := by
    simpa [prefixWord, tailWord_103452, baseEnd_103452] using wordTrace_append hprefix tailTrace_103452
  have hstable : (prefixWord ++ tailWord_103452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103452).length < 2 ^ (prefixWord ++ tailWord_103452).sum := by decide
  have hdescent : baseEnd_103452 < baseStart_103452 := by decide
  rcases family_descends (prefixWord ++ tailWord_103452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103456 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 1, 4]
def baseStart_103456 : Nat := 118140960795 + 103456 * 2 ^ 59
def prefixEnd_103456 : Nat := 4983230072969 + 3 ^ 40 * 103456 * 2
def baseEnd_103456 : Nat := 17707551530550820541407

theorem tailTrace_103456 : CollatzResearch.WordTrace tailWord_103456 prefixEnd_103456 17707551530550820541407 := by
  unfold tailWord_103456
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886675156602027861609111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2515566875469370482145481 1886675156602027861609111)
  ·
    refine ⟨2830012734903041792413667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1886675156602027861609111 2830012734903041792413667)
    ·
      refine ⟨4245019102354562688620501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2830012734903041792413667 4245019102354562688620501)
      ·
        refine ⟨99492635211435063014543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 4245019102354562688620501 99492635211435063014543)
        ·
          refine ⟨149238952817152594521815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99492635211435063014543 149238952817152594521815)
          ·
            refine ⟨223858429225728891782723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149238952817152594521815 223858429225728891782723)
            ·
              refine ⟨335787643838593337674085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223858429225728891782723 335787643838593337674085)
              ·
                refine ⟨62960183219736250813891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 335787643838593337674085 62960183219736250813891)
                ·
                  refine ⟨94440274829604376220837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62960183219736250813891 94440274829604376220837)
                  ·
                    refine ⟨17707551530550820541407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94440274829604376220837 17707551530550820541407)
                    ·
                      rfl

theorem cell23_103456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 4].length) (baseStart_103456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103456 prefixEnd_103456 := by exact prefixLift 103456
  have htrace : WordTrace (prefixWord ++ tailWord_103456) baseStart_103456 baseEnd_103456 := by
    simpa [prefixWord, tailWord_103456, baseEnd_103456] using wordTrace_append hprefix tailTrace_103456
  have hstable : (prefixWord ++ tailWord_103456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103456).length < 2 ^ (prefixWord ++ tailWord_103456).sum := by decide
  have hdescent : baseEnd_103456 < baseStart_103456 := by decide
  rcases family_descends (prefixWord ++ tailWord_103456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103489 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 1, 5, 2]
def baseStart_103489 : Nat := 118140960795 + 103489 * 2 ^ 59
def prefixEnd_103489 : Nat := 4983230072969 + 3 ^ 40 * 103489 * 2
def baseEnd_103489 : Nat := 53139599453250832511569

theorem tailTrace_103489 : CollatzResearch.WordTrace tailWord_103489 prefixEnd_103489 53139599453250832511569 := by
  unfold tailWord_103489
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774553922084502359169521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2516369281389668239446347 3774553922084502359169521)
  ·
    refine ⟨2830915441563376769377141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3774553922084502359169521 2830915441563376769377141)
    ·
      refine ⟨265398322646566572129107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2830915441563376769377141 265398322646566572129107)
      ·
        refine ⟨398097483969849858193661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265398322646566572129107 398097483969849858193661)
        ·
          refine ⟨149286556488693696822623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398097483969849858193661 149286556488693696822623)
          ·
            refine ⟨223929834733040545233935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149286556488693696822623 223929834733040545233935)
            ·
              refine ⟨335894752099560817850903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 223929834733040545233935 335894752099560817850903)
              ·
                refine ⟨503842128149341226776355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335894752099560817850903 503842128149341226776355)
                ·
                  refine ⟨755763192224011840164533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503842128149341226776355 755763192224011840164533)
                  ·
                    refine ⟨70852799271001110015425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 755763192224011840164533 70852799271001110015425)
                    ·
                      refine ⟨53139599453250832511569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70852799271001110015425 53139599453250832511569)
                      ·
                        rfl

theorem cell23_103489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_103489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103489 prefixEnd_103489 := by exact prefixLift 103489
  have htrace : WordTrace (prefixWord ++ tailWord_103489) baseStart_103489 baseEnd_103489 := by
    simpa [prefixWord, tailWord_103489, baseEnd_103489] using wordTrace_append hprefix tailTrace_103489
  have hstable : (prefixWord ++ tailWord_103489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103489).length < 2 ^ (prefixWord ++ tailWord_103489).sum := by decide
  have hdescent : baseEnd_103489 < baseStart_103489 := by decide
  rcases family_descends (prefixWord ++ tailWord_103489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103495 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 1, 6]
def baseStart_103495 : Nat := 118140960795 + 103495 * 2 ^ 59
def prefixEnd_103495 : Nat := 4983230072969 + 3 ^ 40 * 103495 * 2
def baseEnd_103495 : Nat := 17714226779059269678847

theorem tailTrace_103495 : CollatzResearch.WordTrace tailWord_103495 prefixEnd_103495 17714226779059269678847 := by
  unfold tailWord_103495
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774772760062765383887939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2516515173375176922591959 3774772760062765383887939)
  ·
    refine ⟨5662159140094148075831909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774772760062765383887939 5662159140094148075831909)
    ·
      refine ⟨1061654838767652764218483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5662159140094148075831909 1061654838767652764218483)
      ·
        refine ⟨1592482258151479146327725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061654838767652764218483 1592482258151479146327725)
        ·
          refine ⟨597180846806804679872897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1592482258151479146327725 597180846806804679872897)
          ·
            refine ⟨447885635105103509904673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597180846806804679872897 447885635105103509904673)
            ·
              refine ⟨335914226328827632428505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447885635105103509904673 335914226328827632428505)
              ·
                refine ⟨251935669746620724321379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335914226328827632428505 251935669746620724321379)
                ·
                  refine ⟨377903504619931086482069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251935669746620724321379 377903504619931086482069)
                  ·
                    refine ⟨17714226779059269678847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 377903504619931086482069 17714226779059269678847)
                    ·
                      rfl

theorem cell23_103495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_103495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103495 prefixEnd_103495 := by exact prefixLift 103495
  have htrace : WordTrace (prefixWord ++ tailWord_103495) baseStart_103495 baseEnd_103495 := by
    simpa [prefixWord, tailWord_103495, baseEnd_103495] using wordTrace_append hprefix tailTrace_103495
  have hstable : (prefixWord ++ tailWord_103495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103495).length < 2 ^ (prefixWord ++ tailWord_103495).sum := by decide
  have hdescent : baseEnd_103495 < baseStart_103495 := by decide
  rcases family_descends (prefixWord ++ tailWord_103495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103502 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_103502 : Nat := 118140960795 + 103502 * 2 ^ 59
def prefixEnd_103502 : Nat := 4983230072969 + 3 ^ 40 * 103502 * 2
def baseEnd_103502 : Nat := 53146274701759281649009

theorem tailTrace_103502 : CollatzResearch.WordTrace tailWord_103502 prefixEnd_103502 53146274701759281649009 := by
  unfold tailWord_103502
  simp only [CollatzResearch.WordTrace]
  refine ⟨471878508879675697424095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2516685380691603719595173 471878508879675697424095)
  ·
    refine ⟨707817763319513546136143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 471878508879675697424095 707817763319513546136143)
    ·
      refine ⟨1061726644979270319204215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707817763319513546136143 1061726644979270319204215)
      ·
        refine ⟨1592589967468905478806323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061726644979270319204215 1592589967468905478806323)
        ·
          refine ⟨2388884951203358218209485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592589967468905478806323 2388884951203358218209485)
          ·
            refine ⟨895831856701259331828557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2388884951203358218209485 895831856701259331828557)
            ·
              refine ⟨335936946262972249435709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895831856701259331828557 335936946262972249435709)
              ·
                refine ⟨125976354848614593538391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 335936946262972249435709 125976354848614593538391)
                ·
                  refine ⟨188964532272921890307587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125976354848614593538391 188964532272921890307587)
                  ·
                    refine ⟨283446798409382835461381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 188964532272921890307587 283446798409382835461381)
                    ·
                      refine ⟨53146274701759281649009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 283446798409382835461381 53146274701759281649009)
                      ·
                        rfl

theorem cell23_103502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_103502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103502 prefixEnd_103502 := by exact prefixLift 103502
  have htrace : WordTrace (prefixWord ++ tailWord_103502) baseStart_103502 baseEnd_103502 := by
    simpa [prefixWord, tailWord_103502, baseEnd_103502] using wordTrace_append hprefix tailTrace_103502
  have hstable : (prefixWord ++ tailWord_103502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103502).length < 2 ^ (prefixWord ++ tailWord_103502).sum := by decide
  have hdescent : baseEnd_103502 < baseStart_103502 := by decide
  rcases family_descends (prefixWord ++ tailWord_103502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103519 : List Nat := [1, 1, 2, 3, 1, 1, 6, 1, 3, 2, 2]
def baseStart_103519 : Nat := 118140960795 + 103519 * 2 ^ 59
def prefixEnd_103519 : Nat := 4983230072969 + 3 ^ 40 * 103519 * 2
def baseEnd_103519 : Nat := 53155003872885715136431

theorem tailTrace_103519 : CollatzResearch.WordTrace tailWord_103519 prefixEnd_103519 53155003872885715136431 := by
  unfold tailWord_103519
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775648111975817482761611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2517098741317211655174407 3775648111975817482761611)
  ·
    refine ⟨5663472167963726224142417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775648111975817482761611 5663472167963726224142417)
    ·
      refine ⟨4247604125972794668106813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5663472167963726224142417 4247604125972794668106813)
      ·
        refine ⟨1592851547239798000540055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4247604125972794668106813 1592851547239798000540055)
        ·
          refine ⟨2389277320859697000810083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592851547239798000540055 2389277320859697000810083)
          ·
            refine ⟨3583915981289545501215125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389277320859697000810083 3583915981289545501215125)
            ·
              refine ⟨167996061622947445369459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3583915981289545501215125 167996061622947445369459)
              ·
                refine ⟨251994092434421168054189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 167996061622947445369459 251994092434421168054189)
                ·
                  refine ⟨94497784662907938020321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 251994092434421168054189 94497784662907938020321)
                  ·
                    refine ⟨70873338497180953515241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94497784662907938020321 70873338497180953515241)
                    ·
                      refine ⟨53155003872885715136431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70873338497180953515241 53155003872885715136431)
                      ·
                        rfl

theorem cell23_103519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 1, 3, 2, 2].length) (baseStart_103519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103519 prefixEnd_103519 := by exact prefixLift 103519
  have htrace : WordTrace (prefixWord ++ tailWord_103519) baseStart_103519 baseEnd_103519 := by
    simpa [prefixWord, tailWord_103519, baseEnd_103519] using wordTrace_append hprefix tailTrace_103519
  have hstable : (prefixWord ++ tailWord_103519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103519).length < 2 ^ (prefixWord ++ tailWord_103519).sum := by decide
  have hdescent : baseEnd_103519 < baseStart_103519 := by decide
  rcases family_descends (prefixWord ++ tailWord_103519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103522 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 3, 1, 5]
def baseStart_103522 : Nat := 118140960795 + 103522 * 2 ^ 59
def prefixEnd_103522 : Nat := 4983230072969 + 3 ^ 40 * 103522 * 2
def baseEnd_103522 : Nat := 53156544314849203398917

theorem tailTrace_103522 : CollatzResearch.WordTrace tailWord_103522 prefixEnd_103522 53156544314849203398917 := by
  unfold tailWord_103522
  simp only [CollatzResearch.WordTrace]
  refine ⟨943939382741237248780205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2517171687309965996747213 943939382741237248780205)
  ·
    refine ⟨353977268527963968292577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 943939382741237248780205 353977268527963968292577)
    ·
      refine ⟨265482951395972976219433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 353977268527963968292577 265482951395972976219433)
      ·
        refine ⟨199112213546979732164575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 265482951395972976219433 199112213546979732164575)
        ·
          refine ⟨298668320320469598246863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 199112213546979732164575 298668320320469598246863)
          ·
            refine ⟨448002480480704397370295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298668320320469598246863 448002480480704397370295)
            ·
              refine ⟨672003720721056596055443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448002480480704397370295 672003720721056596055443)
              ·
                refine ⟨1008005581081584894083165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672003720721056596055443 1008005581081584894083165)
                ·
                  refine ⟨378002092905594335281187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1008005581081584894083165 378002092905594335281187)
                  ·
                    refine ⟨567003139358391502921781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 378002092905594335281187 567003139358391502921781)
                    ·
                      refine ⟨53156544314849203398917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 567003139358391502921781 53156544314849203398917)
                      ·
                        rfl

theorem cell23_103522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_103522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103522 prefixEnd_103522 := by exact prefixLift 103522
  have htrace : WordTrace (prefixWord ++ tailWord_103522) baseStart_103522 baseEnd_103522 := by
    simpa [prefixWord, tailWord_103522, baseEnd_103522] using wordTrace_append hprefix tailTrace_103522
  have hstable : (prefixWord ++ tailWord_103522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103522).length < 2 ^ (prefixWord ++ tailWord_103522).sum := by decide
  have hdescent : baseEnd_103522 < baseStart_103522 := by decide
  rcases family_descends (prefixWord ++ tailWord_103522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103529 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 2, 4]
def baseStart_103529 : Nat := 118140960795 + 103529 * 2 ^ 59
def prefixEnd_103529 : Nat := 4983230072969 + 3 ^ 40 * 103529 * 2
def baseEnd_103529 : Nat := 17720046226476892003795

theorem tailTrace_103529 : CollatzResearch.WordTrace tailWord_103529 prefixEnd_103529 17720046226476892003795 := by
  unfold tailWord_103529
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776012841939589190625641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2517341894626392793750427 3776012841939589190625641)
  ·
    refine ⟨2832009631454691892969231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3776012841939589190625641 2832009631454691892969231)
    ·
      refine ⟨4248014447182037839453847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832009631454691892969231 4248014447182037839453847)
      ·
        refine ⟨6372021670773056759180771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248014447182037839453847 6372021670773056759180771)
        ·
          refine ⟨9558032506159585138771157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372021670773056759180771 9558032506159585138771157)
          ·
            refine ⟨224016386863115276689949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 9558032506159585138771157 224016386863115276689949)
            ·
              refine ⟨84006145073668228758731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224016386863115276689949 84006145073668228758731)
              ·
                refine ⟨126009217610502343138097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84006145073668228758731 126009217610502343138097)
                ·
                  refine ⟨94506913207876757353573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126009217610502343138097 94506913207876757353573)
                  ·
                    refine ⟨17720046226476892003795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94506913207876757353573 17720046226476892003795)
                    ·
                      rfl

theorem cell23_103529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 4].length) (baseStart_103529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103529 prefixEnd_103529 := by exact prefixLift 103529
  have htrace : WordTrace (prefixWord ++ tailWord_103529) baseStart_103529 baseEnd_103529 := by
    simpa [prefixWord, tailWord_103529, baseEnd_103529] using wordTrace_append hprefix tailTrace_103529
  have hstable : (prefixWord ++ tailWord_103529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103529).length < 2 ^ (prefixWord ++ tailWord_103529).sum := by decide
  have hdescent : baseEnd_103529 < baseStart_103529 := by decide
  rcases family_descends (prefixWord ++ tailWord_103529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103552 : List Nat := [2, 1, 1, 2, 1, 3, 3, 2, 4, 1, 3]
def baseStart_103552 : Nat := 118140960795 + 103552 * 2 ^ 59
def prefixEnd_103552 : Nat := 4983230072969 + 3 ^ 40 * 103552 * 2
def baseEnd_103552 : Nat := 53171948734484086023779

theorem tailTrace_103552 : CollatzResearch.WordTrace tailWord_103552 prefixEnd_103552 53171948734484086023779 := by
  unfold tailWord_103552
  simp only [CollatzResearch.WordTrace]
  refine ⟨1888425860428132059356455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2517901147237509412475273 1888425860428132059356455)
  ·
    refine ⟨2832638790642198089034683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1888425860428132059356455 2832638790642198089034683)
    ·
      refine ⟨4248958185963297133552025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832638790642198089034683 4248958185963297133552025)
      ·
        refine ⟨3186718639472472850164019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4248958185963297133552025 3186718639472472850164019)
        ·
          refine ⟨4780077959208709275246029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186718639472472850164019 4780077959208709275246029)
          ·
            refine ⟨1792529234703265978217261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4780077959208709275246029 1792529234703265978217261)
            ·
              refine ⟨672198463013724741831473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1792529234703265978217261 672198463013724741831473)
              ·
                refine ⟨504148847260293556373605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672198463013724741831473 504148847260293556373605)
                ·
                  refine ⟨94527908861305041820051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504148847260293556373605 94527908861305041820051)
                  ·
                    refine ⟨141791863291957562730077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94527908861305041820051 141791863291957562730077)
                    ·
                      refine ⟨53171948734484086023779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 141791863291957562730077 53171948734484086023779)
                      ·
                        rfl

theorem cell23_103552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 1, 3].length) (baseStart_103552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103552 prefixEnd_103552 := by exact prefixLift 103552
  have htrace : WordTrace (prefixWord ++ tailWord_103552) baseStart_103552 baseEnd_103552 := by
    simpa [prefixWord, tailWord_103552, baseEnd_103552] using wordTrace_append hprefix tailTrace_103552
  have hstable : (prefixWord ++ tailWord_103552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103552).length < 2 ^ (prefixWord ++ tailWord_103552).sum := by decide
  have hdescent : baseEnd_103552 < baseStart_103552 := by decide
  rcases family_descends (prefixWord ++ tailWord_103552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103553 : List Nat := [1, 2, 4, 2, 2, 1, 3, 3, 1, 2, 2]
def baseStart_103553 : Nat := 118140960795 + 103553 * 2 ^ 59
def prefixEnd_103553 : Nat := 4983230072969 + 3 ^ 40 * 103553 * 2
def baseEnd_103553 : Nat := 53172462215138582111275

theorem tailTrace_103553 : CollatzResearch.WordTrace tailWord_103553 prefixEnd_103553 53172462215138582111275 := by
  unfold tailWord_103553
  simp only [CollatzResearch.WordTrace]
  refine ⟨3776888193852641289499313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2517925462568427526332875 3776888193852641289499313)
  ·
    refine ⟨2832666145389480967124485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3776888193852641289499313 2832666145389480967124485)
    ·
      refine ⟨531124902260527681335841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2832666145389480967124485 531124902260527681335841)
      ·
        refine ⟨398343676695395761001881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 531124902260527681335841 398343676695395761001881)
        ·
          refine ⟨298757757521546820751411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398343676695395761001881 298757757521546820751411)
          ·
            refine ⟨448136636282320231127117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298757757521546820751411 448136636282320231127117)
            ·
              refine ⟨168051238605870086672669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 448136636282320231127117 168051238605870086672669)
              ·
                refine ⟨63019214477201282502251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168051238605870086672669 63019214477201282502251)
                ·
                  refine ⟨94528821715801923753377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63019214477201282502251 94528821715801923753377)
                  ·
                    refine ⟨70896616286851442815033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94528821715801923753377 70896616286851442815033)
                    ·
                      refine ⟨53172462215138582111275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70896616286851442815033 53172462215138582111275)
                      ·
                        rfl

theorem cell23_103553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_103553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103553 prefixEnd_103553 := by exact prefixLift 103553
  have htrace : WordTrace (prefixWord ++ tailWord_103553) baseStart_103553 baseEnd_103553 := by
    simpa [prefixWord, tailWord_103553, baseEnd_103553] using wordTrace_append hprefix tailTrace_103553
  have hstable : (prefixWord ++ tailWord_103553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103553).length < 2 ^ (prefixWord ++ tailWord_103553).sum := by decide
  have hdescent : baseEnd_103553 < baseStart_103553 := by decide
  rcases family_descends (prefixWord ++ tailWord_103553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103570 : List Nat := [3, 2, 3, 1, 1, 3, 3, 2, 1, 2, 2]
def baseStart_103570 : Nat := 118140960795 + 103570 * 2 ^ 59
def prefixEnd_103570 : Nat := 4983230072969 + 3 ^ 40 * 103570 * 2
def baseEnd_103570 : Nat := 53181191386265015598697

theorem tailTrace_103570 : CollatzResearch.WordTrace tailWord_103570 prefixEnd_103570 53181191386265015598697 := by
  unfold tailWord_103570
  simp only [CollatzResearch.WordTrace]
  refine ⟨944377058697763298217041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2518338823194035461912109 944377058697763298217041)
  ·
    refine ⟨708282794023322473662781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 944377058697763298217041 708282794023322473662781)
    ·
      refine ⟨265606047758745927623543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 708282794023322473662781 265606047758745927623543)
      ·
        refine ⟨398409071638118891435315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265606047758745927623543 398409071638118891435315)
        ·
          refine ⟨597613607457178337152973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398409071638118891435315 597613607457178337152973)
          ·
            refine ⟨224105102796441876432365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 597613607457178337152973 224105102796441876432365)
            ·
              refine ⟨84039413548665703662137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224105102796441876432365 84039413548665703662137)
              ·
                refine ⟨63029560161499277746603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84039413548665703662137 63029560161499277746603)
                ·
                  refine ⟨94544340242248916619905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63029560161499277746603 94544340242248916619905)
                  ·
                    refine ⟨70908255181686687464929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94544340242248916619905 70908255181686687464929)
                    ·
                      refine ⟨53181191386265015598697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70908255181686687464929 53181191386265015598697)
                      ·
                        rfl

theorem cell23_103570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_103570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103570 prefixEnd_103570 := by exact prefixLift 103570
  have htrace : WordTrace (prefixWord ++ tailWord_103570) baseStart_103570 baseEnd_103570 := by
    simpa [prefixWord, tailWord_103570, baseEnd_103570] using wordTrace_append hprefix tailTrace_103570
  have hstable : (prefixWord ++ tailWord_103570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103570).length < 2 ^ (prefixWord ++ tailWord_103570).sum := by decide
  have hdescent : baseEnd_103570 < baseStart_103570 := by decide
  rcases family_descends (prefixWord ++ tailWord_103570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103585 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 8]
def baseStart_103585 : Nat := 118140960795 + 103585 * 2 ^ 59
def prefixEnd_103585 : Nat := 4983230072969 + 3 ^ 40 * 103585 * 2
def baseEnd_103585 : Nat := 17729631198694152303709

theorem tailTrace_103585 : CollatzResearch.WordTrace tailWord_103585 prefixEnd_103585 17729631198694152303709 := by
  unfold tailWord_103585
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778055329736710754664209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2518703553157807169776139 3778055329736710754664209)
  ·
    refine ⟨2833541497302533065998157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3778055329736710754664209 2833541497302533065998157)
    ·
      refine ⟨1062578061488449899749309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2833541497302533065998157 1062578061488449899749309)
      ·
        refine ⟨398466773058168712405991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1062578061488449899749309 398466773058168712405991)
        ·
          refine ⟨597700159587253068608987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398466773058168712405991 597700159587253068608987)
          ·
            refine ⟨896550239380879602913481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597700159587253068608987 896550239380879602913481)
            ·
              refine ⟨672412679535659702185111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896550239380879602913481 672412679535659702185111)
              ·
                refine ⟨1008619019303489553277667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672412679535659702185111 1008619019303489553277667)
                ·
                  refine ⟨1512928528955234329916501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008619019303489553277667 1512928528955234329916501)
                  ·
                    refine ⟨17729631198694152303709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1512928528955234329916501 17729631198694152303709)
                    ·
                      rfl

theorem cell23_103585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_103585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103585 prefixEnd_103585 := by exact prefixLift 103585
  have htrace : WordTrace (prefixWord ++ tailWord_103585) baseStart_103585 baseEnd_103585 := by
    simpa [prefixWord, tailWord_103585, baseEnd_103585] using wordTrace_append hprefix tailTrace_103585
  have hstable : (prefixWord ++ tailWord_103585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103585).length < 2 ^ (prefixWord ++ tailWord_103585).sum := by decide
  have hdescent : baseEnd_103585 < baseStart_103585 := by decide
  rcases family_descends (prefixWord ++ tailWord_103585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103609 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 1, 4, 2]
def baseStart_103609 : Nat := 118140960795 + 103609 * 2 ^ 59
def prefixEnd_103609 : Nat := 4983230072969 + 3 ^ 40 * 103609 * 2
def baseEnd_103609 : Nat := 53201217131790363011017

theorem tailTrace_103609 : CollatzResearch.WordTrace tailWord_103609 prefixEnd_103609 53201217131790363011017 := by
  unfold tailWord_103609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3778930681649762853537881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2519287121099841902358587 3778930681649762853537881)
  ·
    refine ⟨2834198011237322140153411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3778930681649762853537881 2834198011237322140153411)
    ·
      refine ⟨4251297016855983210230117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834198011237322140153411 4251297016855983210230117)
      ·
        refine ⟨797118190660496851918147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4251297016855983210230117 797118190660496851918147)
        ·
          refine ⟨1195677285990745277877221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797118190660496851918147 1195677285990745277877221)
          ·
            refine ⟨224189491123264739601979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1195677285990745277877221 224189491123264739601979)
            ·
              refine ⟨336284236684897109402969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 224189491123264739601979 336284236684897109402969)
              ·
                refine ⟨252213177513672832052227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336284236684897109402969 252213177513672832052227)
                ·
                  refine ⟨378319766270509248078341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252213177513672832052227 378319766270509248078341)
                  ·
                    refine ⟨70934956175720484014689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 378319766270509248078341 70934956175720484014689)
                    ·
                      refine ⟨53201217131790363011017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70934956175720484014689 53201217131790363011017)
                      ·
                        rfl

theorem cell23_103609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 1, 4, 2].length) (baseStart_103609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103609 prefixEnd_103609 := by exact prefixLift 103609
  have htrace : WordTrace (prefixWord ++ tailWord_103609) baseStart_103609 baseEnd_103609 := by
    simpa [prefixWord, tailWord_103609, baseEnd_103609] using wordTrace_append hprefix tailTrace_103609
  have hstable : (prefixWord ++ tailWord_103609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103609).length < 2 ^ (prefixWord ++ tailWord_103609).sum := by decide
  have hdescent : baseEnd_103609 < baseStart_103609 := by decide
  rcases family_descends (prefixWord ++ tailWord_103609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103612 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_103612 : Nat := 118140960795 + 103612 * 2 ^ 59
def prefixEnd_103612 : Nat := 4983230072969 + 3 ^ 40 * 103612 * 2
def baseEnd_103612 : Nat := 53202757573753851273503

theorem tailTrace_103612 : CollatzResearch.WordTrace tailWord_103612 prefixEnd_103612 53202757573753851273503 := by
  unfold tailWord_103612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889520050319447182948545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2519360067092596243931393 1889520050319447182948545)
  ·
    refine ⟨1417140037739585387211409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1889520050319447182948545 1417140037739585387211409)
    ·
      refine ⟨1062855028304689040408557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1417140037739585387211409 1062855028304689040408557)
      ·
        refine ⟨398570635614258390153209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1062855028304689040408557 398570635614258390153209)
        ·
          refine ⟨298927976710693792614907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398570635614258390153209 298927976710693792614907)
          ·
            refine ⟨448391965066040688922361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298927976710693792614907 448391965066040688922361)
            ·
              refine ⟨336293973799530516691771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448391965066040688922361 336293973799530516691771)
              ·
                refine ⟨504440960699295775037657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336293973799530516691771 504440960699295775037657)
                ·
                  refine ⟨378330720524471831278243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504440960699295775037657 378330720524471831278243)
                  ·
                    refine ⟨567496080786707746917365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 378330720524471831278243 567496080786707746917365)
                    ·
                      refine ⟨53202757573753851273503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 567496080786707746917365 53202757573753851273503)
                      ·
                        rfl

theorem cell23_103612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_103612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103612 prefixEnd_103612 := by exact prefixLift 103612
  have htrace : WordTrace (prefixWord ++ tailWord_103612) baseStart_103612 baseEnd_103612 := by
    simpa [prefixWord, tailWord_103612, baseEnd_103612] using wordTrace_append hprefix tailTrace_103612
  have hstable : (prefixWord ++ tailWord_103612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103612).length < 2 ^ (prefixWord ++ tailWord_103612).sum := by decide
  have hdescent : baseEnd_103612 < baseStart_103612 := by decide
  rcases family_descends (prefixWord ++ tailWord_103612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103626 : List Nat := [3, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2]
def baseStart_103626 : Nat := 118140960795 + 103626 * 2 ^ 59
def prefixEnd_103626 : Nat := 4983230072969 + 3 ^ 40 * 103626 * 2
def baseEnd_103626 : Nat := 53209946302916796498439

theorem tailTrace_103626 : CollatzResearch.WordTrace tailWord_103626 prefixEnd_103626 53209946302916796498439 := by
  unfold tailWord_103626
  simp only [CollatzResearch.WordTrace]
  refine ⟨944887680647043689226683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2519700481725449837937821 944887680647043689226683)
  ·
    refine ⟨1417331520970565533840025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 944887680647043689226683 1417331520970565533840025)
    ·
      refine ⟨1062998640727924150380019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1417331520970565533840025 1062998640727924150380019)
      ·
        refine ⟨1594497961091886225570029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062998640727924150380019 1594497961091886225570029)
        ·
          refine ⟨597936735409457334588761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1594497961091886225570029 597936735409457334588761)
          ·
            refine ⟨448452551557093000941571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597936735409457334588761 448452551557093000941571)
            ·
              refine ⟨672678827335639501412357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448452551557093000941571 672678827335639501412357)
              ·
                refine ⟨126127280125432406514817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 672678827335639501412357 126127280125432406514817)
                ·
                  refine ⟨94595460094074304886113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126127280125432406514817 94595460094074304886113)
                  ·
                    refine ⟨70946595070555728664585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94595460094074304886113 70946595070555728664585)
                    ·
                      refine ⟨53209946302916796498439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 70946595070555728664585 53209946302916796498439)
                      ·
                        rfl

theorem cell23_103626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 4, 2, 2, 2].length) (baseStart_103626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103626 prefixEnd_103626 := by exact prefixLift 103626
  have htrace : WordTrace (prefixWord ++ tailWord_103626) baseStart_103626 baseEnd_103626 := by
    simpa [prefixWord, tailWord_103626, baseEnd_103626] using wordTrace_append hprefix tailTrace_103626
  have hstable : (prefixWord ++ tailWord_103626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103626).length < 2 ^ (prefixWord ++ tailWord_103626).sum := by decide
  have hdescent : baseEnd_103626 < baseStart_103626 := by decide
  rcases family_descends (prefixWord ++ tailWord_103626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103666 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_103666 : Nat := 118140960795 + 103666 * 2 ^ 59
def prefixEnd_103666 : Nat := 4983230072969 + 3 ^ 40 * 103666 * 2
def baseEnd_103666 : Nat := 5914498392121848888695

theorem tailTrace_103666 : CollatzResearch.WordTrace tailWord_103666 prefixEnd_103666 5914498392121848888695 := by
  unfold tailWord_103666
  simp only [CollatzResearch.WordTrace]
  refine ⟨945252410610815397090713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2520673094962174392241901 945252410610815397090713)
  ·
    refine ⟨708939307958111547818035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 945252410610815397090713 708939307958111547818035)
    ·
      refine ⟨1063408961937167321727053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 708939307958111547818035 1063408961937167321727053)
      ·
        refine ⟨398778360726437745647645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1063408961937167321727053 398778360726437745647645)
        ·
          refine ⟨149541885272414154617867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 398778360726437745647645 149541885272414154617867)
          ·
            refine ⟨224312827908621231926801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149541885272414154617867 224312827908621231926801)
            ·
              refine ⟨168234620931465923945101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224312827908621231926801 168234620931465923945101)
              ·
                refine ⟨63087982849299721479413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168234620931465923945101 63087982849299721479413)
                ·
                  refine ⟨5914498392121848888695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63087982849299721479413 5914498392121848888695)
                  ·
                    rfl

theorem cell23_103666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_103666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103666 prefixEnd_103666 := by exact prefixLift 103666
  have htrace : WordTrace (prefixWord ++ tailWord_103666) baseStart_103666 baseEnd_103666 := by
    simpa [prefixWord, tailWord_103666, baseEnd_103666] using wordTrace_append hprefix tailTrace_103666
  have hstable : (prefixWord ++ tailWord_103666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103666).length < 2 ^ (prefixWord ++ tailWord_103666).sum := by decide
  have hdescent : baseEnd_103666 < baseStart_103666 := by decide
  rcases family_descends (prefixWord ++ tailWord_103666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103743 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 1, 4]
def baseStart_103743 : Nat := 118140960795 + 103743 * 2 ^ 59
def prefixEnd_103743 : Nat := 4983230072969 + 3 ^ 40 * 103743 * 2
def baseEnd_103743 : Nat := 17756674513164279578467

theorem tailTrace_103743 : CollatzResearch.WordTrace tailWord_103743 prefixEnd_103743 17756674513164279578467 := by
  unfold tailWord_103743
  simp only [CollatzResearch.WordTrace]
  refine ⟨3783818063164303738915883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2522545375442869159277255 3783818063164303738915883)
  ·
    refine ⟨5675727094746455608373825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3783818063164303738915883 5675727094746455608373825)
    ·
      refine ⟨4256795321059841706280369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5675727094746455608373825 4256795321059841706280369)
      ·
        refine ⟨3192596490794881279710277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4256795321059841706280369 3192596490794881279710277)
        ·
          refine ⟨598611842024040239945677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3192596490794881279710277 598611842024040239945677)
          ·
            refine ⟨224479440759015089979629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 598611842024040239945677 224479440759015089979629)
            ·
              refine ⟨84179790284630658742361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 224479440759015089979629 84179790284630658742361)
              ·
                refine ⟨63134842713472994056771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84179790284630658742361 63134842713472994056771)
                ·
                  refine ⟨94702264070209491085157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63134842713472994056771 94702264070209491085157)
                  ·
                    refine ⟨17756674513164279578467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94702264070209491085157 17756674513164279578467)
                    ·
                      rfl

theorem cell23_103743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 4].length) (baseStart_103743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103743 prefixEnd_103743 := by exact prefixLift 103743
  have htrace : WordTrace (prefixWord ++ tailWord_103743) baseStart_103743 baseEnd_103743 := by
    simpa [prefixWord, tailWord_103743, baseEnd_103743] using wordTrace_append hprefix tailTrace_103743
  have hstable : (prefixWord ++ tailWord_103743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103743).length < 2 ^ (prefixWord ++ tailWord_103743).sum := by decide
  have hdescent : baseEnd_103743 < baseStart_103743 := by decide
  rcases family_descends (prefixWord ++ tailWord_103743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103752 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 3, 5]
def baseStart_103752 : Nat := 118140960795 + 103752 * 2 ^ 59
def prefixEnd_103752 : Nat := 4983230072969 + 3 ^ 40 * 103752 * 2
def baseEnd_103752 : Nat := 17758214955127767840953

theorem tailTrace_103752 : CollatzResearch.WordTrace tailWord_103752 prefixEnd_103752 17758214955127767840953 := by
  unfold tailWord_103752
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892073160065849137996755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2522764213421132183995673 1892073160065849137996755)
  ·
    refine ⟨2838109740098773706995133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892073160065849137996755 2838109740098773706995133)
    ·
      refine ⟨1064291152537040140123175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2838109740098773706995133 1064291152537040140123175)
      ·
        refine ⟨1596436728805560210184763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064291152537040140123175 1596436728805560210184763)
        ·
          refine ⟨2394655093208340315277145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596436728805560210184763 2394655093208340315277145)
          ·
            refine ⟨1795991319906255236457859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394655093208340315277145 1795991319906255236457859)
            ·
              refine ⟨2693986979859382854686789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795991319906255236457859 2693986979859382854686789)
              ·
                refine ⟨505122558723634285253773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2693986979859382854686789 505122558723634285253773)
                ·
                  refine ⟨189420959521362856970165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 505122558723634285253773 189420959521362856970165)
                  ·
                    refine ⟨17758214955127767840953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 189420959521362856970165 17758214955127767840953)
                    ·
                      rfl

theorem cell23_103752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 5].length) (baseStart_103752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103752 prefixEnd_103752 := by exact prefixLift 103752
  have htrace : WordTrace (prefixWord ++ tailWord_103752) baseStart_103752 baseEnd_103752 := by
    simpa [prefixWord, tailWord_103752, baseEnd_103752] using wordTrace_append hprefix tailTrace_103752
  have hstable : (prefixWord ++ tailWord_103752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103752).length < 2 ^ (prefixWord ++ tailWord_103752).sum := by decide
  have hdescent : baseEnd_103752 < baseStart_103752 := by decide
  rcases family_descends (prefixWord ++ tailWord_103752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103756 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 6]
def baseStart_103756 : Nat := 118140960795 + 103756 * 2 ^ 59
def prefixEnd_103756 : Nat := 4983230072969 + 3 ^ 40 * 103756 * 2
def baseEnd_103756 : Nat := 5919633198666809763649

theorem tailTrace_103756 : CollatzResearch.WordTrace tailWord_103756 prefixEnd_103756 5919633198666809763649 := by
  unfold tailWord_103756
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892146106058603479569561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2522861474744804639426081 1892146106058603479569561)
  ·
    refine ⟨1419109579543952609677171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1892146106058603479569561 1419109579543952609677171)
    ·
      refine ⟨2128664369315928914515757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1419109579543952609677171 2128664369315928914515757)
      ·
        refine ⟨798249138493473342943409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2128664369315928914515757 798249138493473342943409)
        ·
          refine ⟨598686853870105007207557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 798249138493473342943409 598686853870105007207557)
          ·
            refine ⟨112253785100644688851417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 598686853870105007207557 112253785100644688851417)
            ·
              refine ⟨84190338825483516638563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112253785100644688851417 84190338825483516638563)
              ·
                refine ⟨126285508238225274957845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84190338825483516638563 126285508238225274957845)
                ·
                  refine ⟨5919633198666809763649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 126285508238225274957845 5919633198666809763649)
                  ·
                    rfl

theorem cell23_103756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_103756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103756 prefixEnd_103756 := by exact prefixLift 103756
  have htrace : WordTrace (prefixWord ++ tailWord_103756) baseStart_103756 baseEnd_103756 := by
    simpa [prefixWord, tailWord_103756, baseEnd_103756] using wordTrace_append hprefix tailTrace_103756
  have hstable : (prefixWord ++ tailWord_103756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103756).length < 2 ^ (prefixWord ++ tailWord_103756).sum := by decide
  have hdescent : baseEnd_103756 < baseStart_103756 := by decide
  rcases family_descends (prefixWord ++ tailWord_103756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103769 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 1, 5]
def baseStart_103769 : Nat := 118140960795 + 103769 * 2 ^ 59
def prefixEnd_103769 : Nat := 4983230072969 + 3 ^ 40 * 103769 * 2
def baseEnd_103769 : Nat := 17761124678836579003427

theorem tailTrace_103769 : CollatzResearch.WordTrace tailWord_103769 prefixEnd_103769 17761124678836579003427 := by
  unfold tailWord_103769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784766361070110179362361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2523177574046740119574907 3784766361070110179362361)
  ·
    refine ⟨2838574770802582634521771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3784766361070110179362361 2838574770802582634521771)
    ·
      refine ⟨4257862156203873951782657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838574770802582634521771 4257862156203873951782657)
      ·
        refine ⟨3193396617152905463836993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4257862156203873951782657 3193396617152905463836993)
        ·
          refine ⟨2395047462864679097877745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3193396617152905463836993 2395047462864679097877745)
          ·
            refine ⟨1796285597148509323408309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395047462864679097877745 1796285597148509323408309)
            ·
              refine ⟨168401774732672749069529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1796285597148509323408309 168401774732672749069529)
              ·
                refine ⟨126301331049504561802147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168401774732672749069529 126301331049504561802147)
                ·
                  refine ⟨189451996574256842703221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126301331049504561802147 189451996574256842703221)
                  ·
                    refine ⟨17761124678836579003427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 189451996574256842703221 17761124678836579003427)
                    ·
                      rfl

theorem cell23_103769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 5].length) (baseStart_103769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103769 prefixEnd_103769 := by exact prefixLift 103769
  have htrace : WordTrace (prefixWord ++ tailWord_103769) baseStart_103769 baseEnd_103769 := by
    simpa [prefixWord, tailWord_103769, baseEnd_103769] using wordTrace_append hprefix tailTrace_103769
  have hstable : (prefixWord ++ tailWord_103769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103769).length < 2 ^ (prefixWord ++ tailWord_103769).sum := by decide
  have hdescent : baseEnd_103769 < baseStart_103769 := by decide
  rcases family_descends (prefixWord ++ tailWord_103769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103776 : List Nat := [2, 1, 1, 3, 4, 1, 1, 3, 2, 3, 2]
def baseStart_103776 : Nat := 118140960795 + 103776 * 2 ^ 59
def prefixEnd_103776 : Nat := 4983230072969 + 3 ^ 40 * 103776 * 2
def baseEnd_103776 : Nat := 53286968401091209622749

theorem tailTrace_103776 : CollatzResearch.WordTrace tailWord_103776 prefixEnd_103776 53286968401091209622749 := by
  unfold tailWord_103776
  simp only [CollatzResearch.WordTrace]
  refine ⟨1892510836022375187433591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2523347781363166916578121 1892510836022375187433591)
  ·
    refine ⟨2838766254033562781150387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1892510836022375187433591 2838766254033562781150387)
    ·
      refine ⟨4258149381050344171725581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2838766254033562781150387 4258149381050344171725581)
      ·
        refine ⟨1596806017893879064397093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4258149381050344171725581 1596806017893879064397093)
        ·
          refine ⟨299401128355102324574455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1596806017893879064397093 299401128355102324574455)
          ·
            refine ⟨449101692532653486861683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299401128355102324574455 449101692532653486861683)
            ·
              refine ⟨673652538798980230292525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449101692532653486861683 673652538798980230292525)
              ·
                refine ⟨252619702049617586359697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673652538798980230292525 252619702049617586359697)
                ·
                  refine ⟨189464776537213189769773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 252619702049617586359697 189464776537213189769773)
                  ·
                    refine ⟨71049291201454946163665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189464776537213189769773 71049291201454946163665)
                    ·
                      refine ⟨53286968401091209622749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71049291201454946163665 53286968401091209622749)
                      ·
                        rfl

theorem cell23_103776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 3, 2, 3, 2].length) (baseStart_103776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103776 prefixEnd_103776 := by exact prefixLift 103776
  have htrace : WordTrace (prefixWord ++ tailWord_103776) baseStart_103776 baseEnd_103776 := by
    simpa [prefixWord, tailWord_103776, baseEnd_103776] using wordTrace_append hprefix tailTrace_103776
  have hstable : (prefixWord ++ tailWord_103776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103776).length < 2 ^ (prefixWord ++ tailWord_103776).sum := by decide
  have hdescent : baseEnd_103776 < baseStart_103776 := by decide
  rcases family_descends (prefixWord ++ tailWord_103776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103816 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 2, 4]
def baseStart_103816 : Nat := 118140960795 + 103816 * 2 ^ 59
def prefixEnd_103816 : Nat := 4983230072969 + 3 ^ 40 * 103816 * 2
def baseEnd_103816 : Nat := 17769169209090351040855

theorem tailTrace_103816 : CollatzResearch.WordTrace tailWord_103816 prefixEnd_103816 17769169209090351040855 := by
  unfold tailWord_103816
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893240295949918603161651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2524320394599891470882201 1893240295949918603161651)
  ·
    refine ⟨2839860443924877904742477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893240295949918603161651 2839860443924877904742477)
    ·
      refine ⟨1064947666471829214278429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2839860443924877904742477 1064947666471829214278429)
      ·
        refine ⟨399355374926935955354411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1064947666471829214278429 399355374926935955354411)
        ·
          refine ⟨599033062390403933031617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 399355374926935955354411 599033062390403933031617)
          ·
            refine ⟨449274796792802949773713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599033062390403933031617 449274796792802949773713)
            ·
              refine ⟨336956097594602212330285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449274796792802949773713 336956097594602212330285)
              ·
                refine ⟨126358536597975829623857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 336956097594602212330285 126358536597975829623857)
                ·
                  refine ⟨94768902448481872217893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126358536597975829623857 94768902448481872217893)
                  ·
                    refine ⟨17769169209090351040855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 94768902448481872217893 17769169209090351040855)
                    ·
                      rfl

theorem cell23_103816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_103816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103816 prefixEnd_103816 := by exact prefixLift 103816
  have htrace : WordTrace (prefixWord ++ tailWord_103816) baseStart_103816 baseEnd_103816 := by
    simpa [prefixWord, tailWord_103816, baseEnd_103816] using wordTrace_append hprefix tailTrace_103816
  have hstable : (prefixWord ++ tailWord_103816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103816).length < 2 ^ (prefixWord ++ tailWord_103816).sum := by decide
  have hdescent : baseEnd_103816 < baseStart_103816 := by decide
  rcases family_descends (prefixWord ++ tailWord_103816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103819 : List Nat := [1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 4]
def baseStart_103819 : Nat := 118140960795 + 103819 * 2 ^ 59
def prefixEnd_103819 : Nat := 4983230072969 + 3 ^ 40 * 103819 * 2
def baseEnd_103819 : Nat := 53309048069234541385051

theorem tailTrace_103819 : CollatzResearch.WordTrace tailWord_103819 prefixEnd_103819 53309048069234541385051 := by
  unfold tailWord_103819
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786590010888968718682511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2524393340592645812455007 3786590010888968718682511)
  ·
    refine ⟨5679885016333453078023767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786590010888968718682511 5679885016333453078023767)
    ·
      refine ⟨8519827524500179617035651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5679885016333453078023767 8519827524500179617035651)
      ·
        refine ⟨12779741286750269425553477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8519827524500179617035651 12779741286750269425553477)
        ·
          refine ⟨2396201491265675517291277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12779741286750269425553477 2396201491265675517291277)
          ·
            refine ⟨898575559224628318984229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2396201491265675517291277 898575559224628318984229)
            ·
              refine ⟨168482917354617809809543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 898575559224628318984229 168482917354617809809543)
              ·
                refine ⟨252724376031926714714315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168482917354617809809543 252724376031926714714315)
                ·
                  refine ⟨379086564047890072071473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252724376031926714714315 379086564047890072071473)
                  ·
                    refine ⟨284314923035917554053605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 379086564047890072071473 284314923035917554053605)
                    ·
                      refine ⟨53309048069234541385051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 284314923035917554053605 53309048069234541385051)
                      ·
                        rfl

theorem cell23_103819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 1, 2, 4].length) (baseStart_103819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103819 prefixEnd_103819 := by exact prefixLift 103819
  have htrace : WordTrace (prefixWord ++ tailWord_103819) baseStart_103819 baseEnd_103819 := by
    simpa [prefixWord, tailWord_103819, baseEnd_103819] using wordTrace_append hprefix tailTrace_103819
  have hstable : (prefixWord ++ tailWord_103819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103819).length < 2 ^ (prefixWord ++ tailWord_103819).sum := by decide
  have hdescent : baseEnd_103819 < baseStart_103819 := by decide
  rcases family_descends (prefixWord ++ tailWord_103819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103840 : List Nat := [2, 1, 1, 4, 1, 2, 4, 3, 1, 2, 2]
def baseStart_103840 : Nat := 118140960795 + 103840 * 2 ^ 59
def prefixEnd_103840 : Nat := 4983230072969 + 3 ^ 40 * 103840 * 2
def baseEnd_103840 : Nat := 53319831162978959222455

theorem tailTrace_103840 : CollatzResearch.WordTrace tailWord_103840 prefixEnd_103840 53319831162978959222455 := by
  unfold tailWord_103840
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893677971906444652598487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2524903962541926203464649 1893677971906444652598487)
  ·
    refine ⟨2840516957859666978897731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893677971906444652598487 2840516957859666978897731)
    ·
      refine ⟨4260775436789500468346597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840516957859666978897731 4260775436789500468346597)
      ·
        refine ⟨798895394398031337814987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4260775436789500468346597 798895394398031337814987)
        ·
          refine ⟨1198343091597047006722481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798895394398031337814987 1198343091597047006722481)
          ·
            refine ⟨898757318697785255041861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198343091597047006722481 898757318697785255041861)
            ·
              refine ⟨168516997255834735320349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 898757318697785255041861 168516997255834735320349)
              ·
                refine ⟨63193873970938025745131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 168516997255834735320349 63193873970938025745131)
                ·
                  refine ⟨94790810956407038617697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63193873970938025745131 94790810956407038617697)
                  ·
                    refine ⟨71093108217305278963273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 94790810956407038617697 71093108217305278963273)
                    ·
                      refine ⟨53319831162978959222455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71093108217305278963273 53319831162978959222455)
                      ·
                        rfl

theorem cell23_103840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 3, 1, 2, 2].length) (baseStart_103840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103840 prefixEnd_103840 := by exact prefixLift 103840
  have htrace : WordTrace (prefixWord ++ tailWord_103840) baseStart_103840 baseEnd_103840 := by
    simpa [prefixWord, tailWord_103840, baseEnd_103840] using wordTrace_append hprefix tailTrace_103840
  have hstable : (prefixWord ++ tailWord_103840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103840).length < 2 ^ (prefixWord ++ tailWord_103840).sum := by decide
  have hdescent : baseEnd_103840 < baseStart_103840 := by decide
  rcases family_descends (prefixWord ++ tailWord_103840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103856 : List Nat := [2, 1, 1, 1, 2, 1, 1, 8, 2, 1, 3]
def baseStart_103856 : Nat := 118140960795 + 103856 * 2 ^ 59
def prefixEnd_103856 : Nat := 4983230072969 + 3 ^ 40 * 103856 * 2
def baseEnd_103856 : Nat := 53328046853450896622381

theorem tailTrace_103856 : CollatzResearch.WordTrace tailWord_103856 prefixEnd_103856 53328046853450896622381 := by
  unfold tailWord_103856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893969755877462018889711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2525293007836616025186281 1893969755877462018889711)
  ·
    refine ⟨2840954633816193028334567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893969755877462018889711 2840954633816193028334567)
    ·
      refine ⟨4261431950724289542501851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840954633816193028334567 4261431950724289542501851)
      ·
        refine ⟨6392147926086434313752777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4261431950724289542501851 6392147926086434313752777)
        ·
          refine ⟨4794110944564825735314583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6392147926086434313752777 4794110944564825735314583)
          ·
            refine ⟨7191166416847238602971875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4794110944564825735314583 7191166416847238602971875)
            ·
              refine ⟨10786749625270857904457813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7191166416847238602971875 10786749625270857904457813)
              ·
                refine ⟨126407222171142866067865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10786749625270857904457813 126407222171142866067865)
                ·
                  refine ⟨94805416628357149550899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126407222171142866067865 94805416628357149550899)
                  ·
                    refine ⟨142208124942535724326349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 94805416628357149550899 142208124942535724326349)
                    ·
                      refine ⟨53328046853450896622381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 142208124942535724326349 53328046853450896622381)
                      ·
                        rfl

theorem cell23_103856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 8, 2, 1, 3].length) (baseStart_103856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103856 prefixEnd_103856 := by exact prefixLift 103856
  have htrace : WordTrace (prefixWord ++ tailWord_103856) baseStart_103856 baseEnd_103856 := by
    simpa [prefixWord, tailWord_103856, baseEnd_103856] using wordTrace_append hprefix tailTrace_103856
  have hstable : (prefixWord ++ tailWord_103856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103856).length < 2 ^ (prefixWord ++ tailWord_103856).sum := by decide
  have hdescent : baseEnd_103856 < baseStart_103856 := by decide
  rcases family_descends (prefixWord ++ tailWord_103856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103874 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_103874 : Nat := 118140960795 + 103874 * 2 ^ 59
def prefixEnd_103874 : Nat := 4983230072969 + 3 ^ 40 * 103874 * 2
def baseEnd_103874 : Nat := 53337289505231826197299

theorem tailTrace_103874 : CollatzResearch.WordTrace tailWord_103874 prefixEnd_103874 53337289505231826197299 := by
  unfold tailWord_103874
  simp only [CollatzResearch.WordTrace]
  refine ⟨947149006422428277983669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2525730683793142074623117 947149006422428277983669)
  ·
    refine ⟨88795219352102651060969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 947149006422428277983669 88795219352102651060969)
    ·
      refine ⟨66596414514076988295727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 88795219352102651060969 66596414514076988295727)
      ·
        refine ⟨99894621771115482443591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66596414514076988295727 99894621771115482443591)
        ·
          refine ⟨149841932656673223665387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99894621771115482443591 149841932656673223665387)
          ·
            refine ⟨224762898985009835498081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 149841932656673223665387 224762898985009835498081)
            ·
              refine ⟨168572174238757376623561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 224762898985009835498081 168572174238757376623561)
              ·
                refine ⟨126429130679068032467671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168572174238757376623561 126429130679068032467671)
                ·
                  refine ⟨189643696018602048701507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126429130679068032467671 189643696018602048701507)
                  ·
                    refine ⟨284465544027903073052261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 189643696018602048701507 284465544027903073052261)
                    ·
                      refine ⟨53337289505231826197299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 284465544027903073052261 53337289505231826197299)
                      ·
                        rfl

theorem cell23_103874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_103874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103874 prefixEnd_103874 := by exact prefixLift 103874
  have htrace : WordTrace (prefixWord ++ tailWord_103874) baseStart_103874 baseEnd_103874 := by
    simpa [prefixWord, tailWord_103874, baseEnd_103874] using wordTrace_append hprefix tailTrace_103874
  have hstable : (prefixWord ++ tailWord_103874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103874).length < 2 ^ (prefixWord ++ tailWord_103874).sum := by decide
  have hdescent : baseEnd_103874 < baseStart_103874 := by decide
  rcases family_descends (prefixWord ++ tailWord_103874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103896 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 1, 4, 2]
def baseStart_103896 : Nat := 118140960795 + 103896 * 2 ^ 59
def prefixEnd_103896 : Nat := 4983230072969 + 3 ^ 40 * 103896 * 2
def baseEnd_103896 : Nat := 53348586079630740122197

theorem tailTrace_103896 : CollatzResearch.WordTrace tailWord_103896 prefixEnd_103896 53348586079630740122197 := by
  unfold tailWord_103896
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894699215805005434617771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2526265621073340579490361 1894699215805005434617771)
  ·
    refine ⟨2842048823707508151926657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1894699215805005434617771 2842048823707508151926657)
    ·
      refine ⟨2131536617780631113944993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2842048823707508151926657 2131536617780631113944993)
      ·
        refine ⟨1598652463335473335458745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2131536617780631113944993 1598652463335473335458745)
        ·
          refine ⟨1198989347501605001594059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598652463335473335458745 1198989347501605001594059)
          ·
            refine ⟨1798484021252407502391089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198989347501605001594059 1798484021252407502391089)
            ·
              refine ⟨1348863015939305626793317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798484021252407502391089 1348863015939305626793317)
              ·
                refine ⟨252911815488619805023747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1348863015939305626793317 252911815488619805023747)
                ·
                  refine ⟨379367723232929707535621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252911815488619805023747 379367723232929707535621)
                  ·
                    refine ⟨71131448106174320162929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 379367723232929707535621 71131448106174320162929)
                    ·
                      refine ⟨53348586079630740122197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71131448106174320162929 53348586079630740122197)
                      ·
                        rfl

theorem cell23_103896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_103896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103896 prefixEnd_103896 := by exact prefixLift 103896
  have htrace : WordTrace (prefixWord ++ tailWord_103896) baseStart_103896 baseEnd_103896 := by
    simpa [prefixWord, tailWord_103896, baseEnd_103896] using wordTrace_append hprefix tailTrace_103896
  have hstable : (prefixWord ++ tailWord_103896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103896).length < 2 ^ (prefixWord ++ tailWord_103896).sum := by decide
  have hdescent : baseEnd_103896 < baseStart_103896 := by decide
  rcases family_descends (prefixWord ++ tailWord_103896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103919 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 7]
def baseStart_103919 : Nat := 118140960795 + 103919 * 2 ^ 59
def prefixEnd_103919 : Nat := 4983230072969 + 3 ^ 40 * 103919 * 2
def baseEnd_103919 : Nat := 5928932903853794459399

theorem tailTrace_103919 : CollatzResearch.WordTrace tailWord_103919 prefixEnd_103919 5928932903853794459399 := by
  unfold tailWord_103919
  simp only [CollatzResearch.WordTrace]
  refine ⟨3790237310526685797322811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2526824873684457198215207 3790237310526685797322811)
  ·
    refine ⟨5685355965790028695984217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3790237310526685797322811 5685355965790028695984217)
    ·
      refine ⟨4264016974342521521988163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5685355965790028695984217 4264016974342521521988163)
      ·
        refine ⟨6396025461513782282982245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264016974342521521988163 6396025461513782282982245)
        ·
          refine ⟨1199254774033834178059171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6396025461513782282982245 1199254774033834178059171)
          ·
            refine ⟨1798882161050751267088757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199254774033834178059171 1798882161050751267088757)
            ·
              refine ⟨168645202598507931289571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1798882161050751267088757 168645202598507931289571)
              ·
                refine ⟨252967803897761896934357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 168645202598507931289571 252967803897761896934357)
                ·
                  refine ⟨5928932903853794459399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 252967803897761896934357 5928932903853794459399)
                  ·
                    rfl

theorem cell23_103919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 7].length) (baseStart_103919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103919 prefixEnd_103919 := by exact prefixLift 103919
  have htrace : WordTrace (prefixWord ++ tailWord_103919) baseStart_103919 baseEnd_103919 := by
    simpa [prefixWord, tailWord_103919, baseEnd_103919] using wordTrace_append hprefix tailTrace_103919
  have hstable : (prefixWord ++ tailWord_103919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103919).length < 2 ^ (prefixWord ++ tailWord_103919).sum := by decide
  have hdescent : baseEnd_103919 < baseStart_103919 := by decide
  rcases family_descends (prefixWord ++ tailWord_103919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103929 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 3]
def baseStart_103929 : Nat := 118140960795 + 103929 * 2 ^ 59
def prefixEnd_103929 : Nat := 4983230072969 + 3 ^ 40 * 103929 * 2
def baseEnd_103929 : Nat := 53365530941229111009545

theorem tailTrace_103929 : CollatzResearch.WordTrace tailWord_103929 prefixEnd_103929 53365530941229111009545 := by
  unfold tailWord_103929
  simp only [CollatzResearch.WordTrace]
  refine ⟨3790602040490457505186841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2527068026993638336791227 3790602040490457505186841)
  ·
    refine ⟨2842951530367843128890131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3790602040490457505186841 2842951530367843128890131)
    ·
      refine ⟨4264427295551764693335197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2842951530367843128890131 4264427295551764693335197)
      ·
        refine ⟨1599160235831911760000699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4264427295551764693335197 1599160235831911760000699)
        ·
          refine ⟨2398740353747867640001049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599160235831911760000699 2398740353747867640001049)
          ·
            refine ⟨1799055265310900730000787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2398740353747867640001049 1799055265310900730000787)
            ·
              refine ⟨2698582897966351095001181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799055265310900730000787 2698582897966351095001181)
              ·
                refine ⟨1011968586737381660625443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2698582897966351095001181 1011968586737381660625443)
                ·
                  refine ⟨1517952880106072490938165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011968586737381660625443 1517952880106072490938165)
                  ·
                    refine ⟨142308082509944296025453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1517952880106072490938165 142308082509944296025453)
                    ·
                      refine ⟨53365530941229111009545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 142308082509944296025453 53365530941229111009545)
                      ·
                        rfl

theorem cell23_103929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_103929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103929 prefixEnd_103929 := by exact prefixLift 103929
  have htrace : WordTrace (prefixWord ++ tailWord_103929) baseStart_103929 baseEnd_103929 := by
    simpa [prefixWord, tailWord_103929, baseEnd_103929] using wordTrace_append hprefix tailTrace_103929
  have hstable : (prefixWord ++ tailWord_103929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103929).length < 2 ^ (prefixWord ++ tailWord_103929).sum := by decide
  have hdescent : baseEnd_103929 < baseStart_103929 := by decide
  rcases family_descends (prefixWord ++ tailWord_103929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_103934 : List Nat := [4, 2, 2, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_103934 : Nat := 118140960795 + 103934 * 2 ^ 59
def prefixEnd_103934 : Nat := 4983230072969 + 3 ^ 40 * 103934 * 2
def baseEnd_103934 : Nat := 53368098344501591447023

theorem tailTrace_103934 : CollatzResearch.WordTrace tailWord_103934 prefixEnd_103934 53368098344501591447023 := by
  unfold tailWord_103934
  simp only [CollatzResearch.WordTrace]
  refine ⟨473848050684042919889857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2527189603648228906079237 473848050684042919889857)
  ·
    refine ⟨355386038013032189917393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 473848050684042919889857 355386038013032189917393)
    ·
      refine ⟨266539528509774142438045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 355386038013032189917393 266539528509774142438045)
      ·
        refine ⟨99952323191165303414267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 266539528509774142438045 99952323191165303414267)
        ·
          refine ⟨149928484786747955121401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 99952323191165303414267 149928484786747955121401)
          ·
            refine ⟨112446363590060966341051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 149928484786747955121401 112446363590060966341051)
            ·
              refine ⟨168669545385091449511577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112446363590060966341051 168669545385091449511577)
              ·
                refine ⟨126502159038818587133683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 168669545385091449511577 126502159038818587133683)
                ·
                  refine ⟨189753238558227880700525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126502159038818587133683 189753238558227880700525)
                  ·
                    refine ⟨71157464459335455262697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 189753238558227880700525 71157464459335455262697)
                    ·
                      refine ⟨53368098344501591447023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71157464459335455262697 53368098344501591447023)
                      ·
                        rfl

theorem cell23_103934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_103934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_103934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_103934 prefixEnd_103934 := by exact prefixLift 103934
  have htrace : WordTrace (prefixWord ++ tailWord_103934) baseStart_103934 baseEnd_103934 := by
    simpa [prefixWord, tailWord_103934, baseEnd_103934] using wordTrace_append hprefix tailTrace_103934
  have hstable : (prefixWord ++ tailWord_103934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_103934).length < 2 ^ (prefixWord ++ tailWord_103934).sum := by decide
  have hdescent : baseEnd_103934 < baseStart_103934 := by decide
  rcases family_descends (prefixWord ++ tailWord_103934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104049 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 7]
def baseStart_104049 : Nat := 118140960795 + 104049 * 2 ^ 59
def prefixEnd_104049 : Nat := 4983230072969 + 3 ^ 40 * 104049 * 2
def baseEnd_104049 : Nat := 53427148619768641508993

theorem tailTrace_104049 : CollatzResearch.WordTrace tailWord_104049 prefixEnd_104049 53427148619768641508993 := by
  unfold tailWord_104049
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794978800055717999555201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2529985866703811999703467 3794978800055717999555201)
  ·
    refine ⟨2846234100041788499666401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3794978800055717999555201 2846234100041788499666401)
    ·
      refine ⟨2134675575031341374749801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2846234100041788499666401 2134675575031341374749801)
      ·
        refine ⟨1601006681273506031062351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2134675575031341374749801 1601006681273506031062351)
        ·
          refine ⟨2401510021910259046593527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601006681273506031062351 2401510021910259046593527)
          ·
            refine ⟨3602265032865388569890291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401510021910259046593527 3602265032865388569890291)
            ·
              refine ⟨5403397549298082854835437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3602265032865388569890291 5403397549298082854835437)
              ·
                refine ⟨2026274080986781070563289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5403397549298082854835437 2026274080986781070563289)
                ·
                  refine ⟨1519705560740085802922467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2026274080986781070563289 1519705560740085802922467)
                  ·
                    refine ⟨2279558341110128704383701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1519705560740085802922467 2279558341110128704383701)
                    ·
                      refine ⟨53427148619768641508993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2279558341110128704383701 53427148619768641508993)
                      ·
                        rfl

theorem cell23_104049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_104049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104049 prefixEnd_104049 := by exact prefixLift 104049
  have htrace : WordTrace (prefixWord ++ tailWord_104049) baseStart_104049 baseEnd_104049 := by
    simpa [prefixWord, tailWord_104049, baseEnd_104049] using wordTrace_append hprefix tailTrace_104049
  have hstable : (prefixWord ++ tailWord_104049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104049).length < 2 ^ (prefixWord ++ tailWord_104049).sum := by decide
  have hdescent : baseEnd_104049 < baseStart_104049 := by decide
  rcases family_descends (prefixWord ++ tailWord_104049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104127 : List Nat := [1, 1, 2, 2, 2, 3, 2, 5, 1, 2, 2]
def baseStart_104127 : Nat := 118140960795 + 104127 * 2 ^ 59
def prefixEnd_104127 : Nat := 4983230072969 + 3 ^ 40 * 104127 * 2
def baseEnd_104127 : Nat := 53467200110819336333635

theorem tailTrace_104127 : CollatzResearch.WordTrace tailWord_104127 prefixEnd_104127 53467200110819336333635 := by
  unfold tailWord_104127
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797823693773137320894635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2531882462515424880596423 3797823693773137320894635)
  ·
    refine ⟨5696735540659705981341953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3797823693773137320894635 5696735540659705981341953)
    ·
      refine ⟨4272551655494779486006465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5696735540659705981341953 4272551655494779486006465)
      ·
        refine ⟨3204413741621084614504849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4272551655494779486006465 3204413741621084614504849)
        ·
          refine ⟨2403310306215813460878637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3204413741621084614504849 2403310306215813460878637)
          ·
            refine ⟨901241364830930047829489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2403310306215813460878637 901241364830930047829489)
            ·
              refine ⟨675931023623197535872117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 901241364830930047829489 675931023623197535872117)
              ·
                refine ⟨63368533464674768988011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 675931023623197535872117 63368533464674768988011)
                ·
                  refine ⟨95052800197012153482017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63368533464674768988011 95052800197012153482017)
                  ·
                    refine ⟨71289600147759115111513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95052800197012153482017 71289600147759115111513)
                    ·
                      refine ⟨53467200110819336333635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71289600147759115111513 53467200110819336333635)
                      ·
                        rfl

theorem cell23_104127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 5, 1, 2, 2].length) (baseStart_104127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104127 prefixEnd_104127 := by exact prefixLift 104127
  have htrace : WordTrace (prefixWord ++ tailWord_104127) baseStart_104127 baseEnd_104127 := by
    simpa [prefixWord, tailWord_104127, baseEnd_104127] using wordTrace_append hprefix tailTrace_104127
  have hstable : (prefixWord ++ tailWord_104127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104127).length < 2 ^ (prefixWord ++ tailWord_104127).sum := by decide
  have hdescent : baseEnd_104127 < baseStart_104127 := by decide
  rcases family_descends (prefixWord ++ tailWord_104127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104143 : List Nat := [1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 3]
def baseStart_104143 : Nat := 118140960795 + 104143 * 2 ^ 59
def prefixEnd_104143 : Nat := 4983230072969 + 3 ^ 40 * 104143 * 2
def baseEnd_104143 : Nat := 53475415801291273733561

theorem tailTrace_104143 : CollatzResearch.WordTrace tailWord_104143 prefixEnd_104143 53475415801291273733561 := by
  unfold tailWord_104143
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798407261715172053477083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2532271507810114702318055 3798407261715172053477083)
  ·
    refine ⟨5697610892572758080215625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3798407261715172053477083 5697610892572758080215625)
    ·
      refine ⟨4273208169429568560161719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5697610892572758080215625 4273208169429568560161719)
      ·
        refine ⟨6409812254144352840242579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4273208169429568560161719 6409812254144352840242579)
        ·
          refine ⟨9614718381216529260363869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6409812254144352840242579 9614718381216529260363869)
          ·
            refine ⟨3605519392956198472636451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9614718381216529260363869 3605519392956198472636451)
            ·
              refine ⟨5408279089434297708954677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3605519392956198472636451 5408279089434297708954677)
              ·
                refine ⟨507026164634465410214501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5408279089434297708954677 507026164634465410214501)
                ·
                  refine ⟨95067405868962264415219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507026164634465410214501 95067405868962264415219)
                  ·
                    refine ⟨142601108803443396622829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95067405868962264415219 142601108803443396622829)
                    ·
                      refine ⟨53475415801291273733561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 142601108803443396622829 53475415801291273733561)
                      ·
                        rfl

theorem cell23_104143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 1, 3].length) (baseStart_104143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104143 prefixEnd_104143 := by exact prefixLift 104143
  have htrace : WordTrace (prefixWord ++ tailWord_104143) baseStart_104143 baseEnd_104143 := by
    simpa [prefixWord, tailWord_104143, baseEnd_104143] using wordTrace_append hprefix tailTrace_104143
  have hstable : (prefixWord ++ tailWord_104143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104143).length < 2 ^ (prefixWord ++ tailWord_104143).sum := by decide
  have hdescent : baseEnd_104143 < baseStart_104143 := by decide
  rcases family_descends (prefixWord ++ tailWord_104143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104157 : List Nat := [1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_104157 : Nat := 118140960795 + 104157 * 2 ^ 59
def prefixEnd_104157 : Nat := 4983230072969 + 3 ^ 40 * 104157 * 2
def baseEnd_104157 : Nat := 53482604530454218958497

theorem tailTrace_104157 : CollatzResearch.WordTrace tailWord_104157 prefixEnd_104157 53482604530454218958497 := by
  unfold tailWord_104157
  simp only [CollatzResearch.WordTrace]
  refine ⟨3798917883664452444486725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2532611922442968296324483 3798917883664452444486725)
  ·
    refine ⟨712297103187084833341261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3798917883664452444486725 712297103187084833341261)
    ·
      refine ⟨267111413695156812502973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 712297103187084833341261 267111413695156812502973)
      ·
        refine ⟨100166780135683804688615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267111413695156812502973 100166780135683804688615)
        ·
          refine ⟨150250170203525707032923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100166780135683804688615 150250170203525707032923)
          ·
            refine ⟨225375255305288560549385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150250170203525707032923 225375255305288560549385)
            ·
              refine ⟨169031441478966420412039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225375255305288560549385 169031441478966420412039)
              ·
                refine ⟨253547162218449630618059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169031441478966420412039 253547162218449630618059)
                ·
                  refine ⟨380320743327674445927089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253547162218449630618059 380320743327674445927089)
                  ·
                    refine ⟨285240557495755834445317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 380320743327674445927089 285240557495755834445317)
                    ·
                      refine ⟨53482604530454218958497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 285240557495755834445317 53482604530454218958497)
                      ·
                        rfl

theorem cell23_104157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_104157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104157 prefixEnd_104157 := by exact prefixLift 104157
  have htrace : WordTrace (prefixWord ++ tailWord_104157) baseStart_104157 baseEnd_104157 := by
    simpa [prefixWord, tailWord_104157, baseEnd_104157] using wordTrace_append hprefix tailTrace_104157
  have hstable : (prefixWord ++ tailWord_104157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104157).length < 2 ^ (prefixWord ++ tailWord_104157).sum := by decide
  have hdescent : baseEnd_104157 < baseStart_104157 := by decide
  rcases family_descends (prefixWord ++ tailWord_104157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104160 : List Nat := [2, 1, 1, 3, 1, 2, 4, 3, 2, 1, 3]
def baseStart_104160 : Nat := 118140960795 + 104160 * 2 ^ 59
def prefixEnd_104160 : Nat := 4983230072969 + 3 ^ 40 * 104160 * 2
def baseEnd_104160 : Nat := 53484144972417707220983

theorem tailTrace_104160 : CollatzResearch.WordTrace tailWord_104160 prefixEnd_104160 53484144972417707220983 := by
  unfold tailWord_104160
  simp only [CollatzResearch.WordTrace]
  refine ⟨1899513651326791978422967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2532684868435722637897289 1899513651326791978422967)
  ·
    refine ⟨2849270476990187967634451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1899513651326791978422967 2849270476990187967634451)
    ·
      refine ⟨4273905715485281951451677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2849270476990187967634451 4273905715485281951451677)
      ·
        refine ⟨1602714643306980731794379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4273905715485281951451677 1602714643306980731794379)
        ·
          refine ⟨2404071964960471097691569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602714643306980731794379 2404071964960471097691569)
          ·
            refine ⟨1803053973720353323268677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2404071964960471097691569 1803053973720353323268677)
            ·
              refine ⟨338072620072566248112877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1803053973720353323268677 338072620072566248112877)
              ·
                refine ⟨126777232527212343042329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338072620072566248112877 126777232527212343042329)
                ·
                  refine ⟨95082924395409257281747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126777232527212343042329 95082924395409257281747)
                  ·
                    refine ⟨142624386593113885922621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95082924395409257281747 142624386593113885922621)
                    ·
                      refine ⟨53484144972417707220983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 142624386593113885922621 53484144972417707220983)
                      ·
                        rfl

theorem cell23_104160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 3, 2, 1, 3].length) (baseStart_104160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104160 prefixEnd_104160 := by exact prefixLift 104160
  have htrace : WordTrace (prefixWord ++ tailWord_104160) baseStart_104160 baseEnd_104160 := by
    simpa [prefixWord, tailWord_104160, baseEnd_104160] using wordTrace_append hprefix tailTrace_104160
  have hstable : (prefixWord ++ tailWord_104160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104160).length < 2 ^ (prefixWord ++ tailWord_104160).sum := by decide
  have hdescent : baseEnd_104160 < baseStart_104160 := by decide
  rcases family_descends (prefixWord ++ tailWord_104160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104170 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2]
def baseStart_104170 : Nat := 118140960795 + 104170 * 2 ^ 59
def prefixEnd_104170 : Nat := 4983230072969 + 3 ^ 40 * 104170 * 2
def baseEnd_104170 : Nat := 53489279778962668095937

theorem tailTrace_104170 : CollatzResearch.WordTrace tailWord_104170 prefixEnd_104170 53489279778962668095937 := by
  unfold tailWord_104170
  simp only [CollatzResearch.WordTrace]
  refine ⟨949848008154338916177491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2532928021744903776473309 949848008154338916177491)
  ·
    refine ⟨1424772012231508374266237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949848008154338916177491 1424772012231508374266237)
    ·
      refine ⟨534289504586815640349839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1424772012231508374266237 534289504586815640349839)
      ·
        refine ⟨801434256880223460524759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534289504586815640349839 801434256880223460524759)
        ·
          refine ⟨1202151385320335190787139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801434256880223460524759 1202151385320335190787139)
          ·
            refine ⟨1803227077980502786180709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202151385320335190787139 1803227077980502786180709)
            ·
              refine ⟨338105077121344272408883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1803227077980502786180709 338105077121344272408883)
              ·
                refine ⟨507157615682016408613325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338105077121344272408883 507157615682016408613325)
                ·
                  refine ⟨190184105880756153229997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 507157615682016408613325 190184105880756153229997)
                  ·
                    refine ⟨71319039705283557461249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 190184105880756153229997 71319039705283557461249)
                    ·
                      refine ⟨53489279778962668095937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71319039705283557461249 53489279778962668095937)
                      ·
                        rfl

theorem cell23_104170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_104170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104170 prefixEnd_104170 := by exact prefixLift 104170
  have htrace : WordTrace (prefixWord ++ tailWord_104170) baseStart_104170 baseEnd_104170 := by
    simpa [prefixWord, tailWord_104170, baseEnd_104170] using wordTrace_append hprefix tailTrace_104170
  have hstable : (prefixWord ++ tailWord_104170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104170).length < 2 ^ (prefixWord ++ tailWord_104170).sum := by decide
  have hdescent : baseEnd_104170 < baseStart_104170 := by decide
  rcases family_descends (prefixWord ++ tailWord_104170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104186 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_104186 : Nat := 118140960795 + 104186 * 2 ^ 59
def prefixEnd_104186 : Nat := 4983230072969 + 3 ^ 40 * 104186 * 2
def baseEnd_104186 : Nat := 53497495469434605495863

theorem tailTrace_104186 : CollatzResearch.WordTrace tailWord_104186 prefixEnd_104186 53497495469434605495863 := by
  unfold tailWord_104186
  simp only [CollatzResearch.WordTrace]
  refine ⟨949993900139847599323103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2533317067039593598194941 949993900139847599323103)
  ·
    refine ⟨1424990850209771398984655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 949993900139847599323103 1424990850209771398984655)
    ·
      refine ⟨2137486275314657098476983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424990850209771398984655 2137486275314657098476983)
      ·
        refine ⟨3206229412971985647715475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2137486275314657098476983 3206229412971985647715475)
        ·
          refine ⟨4809344119457978471573213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3206229412971985647715475 4809344119457978471573213)
          ·
            refine ⟨1803504044796741926839955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4809344119457978471573213 1803504044796741926839955)
            ·
              refine ⟨2705256067195112890259933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803504044796741926839955 2705256067195112890259933)
              ·
                refine ⟨1014471025198167333847475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2705256067195112890259933 1014471025198167333847475)
                ·
                  refine ⟨1521706537797251000771213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014471025198167333847475 1521706537797251000771213)
                  ·
                    refine ⟨570639951673969125289205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1521706537797251000771213 570639951673969125289205)
                    ·
                      refine ⟨53497495469434605495863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 570639951673969125289205 53497495469434605495863)
                      ·
                        rfl

theorem cell23_104186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_104186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104186 prefixEnd_104186 := by exact prefixLift 104186
  have htrace : WordTrace (prefixWord ++ tailWord_104186) baseStart_104186 baseEnd_104186 := by
    simpa [prefixWord, tailWord_104186, baseEnd_104186] using wordTrace_append hprefix tailTrace_104186
  have hstable : (prefixWord ++ tailWord_104186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104186).length < 2 ^ (prefixWord ++ tailWord_104186).sum := by decide
  have hdescent : baseEnd_104186 < baseStart_104186 := by decide
  rcases family_descends (prefixWord ++ tailWord_104186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104210 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 2, 6]
def baseStart_104210 : Nat := 118140960795 + 104210 * 2 ^ 59
def prefixEnd_104210 : Nat := 4983230072969 + 3 ^ 40 * 104210 * 2
def baseEnd_104210 : Nat := 17836606335047503865251

theorem tailTrace_104210 : CollatzResearch.WordTrace tailWord_104210 prefixEnd_104210 17836606335047503865251 := by
  unfold tailWord_104210
  simp only [CollatzResearch.WordTrace]
  refine ⟨950212738118110624041521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2533900634981628330777389 950212738118110624041521)
  ·
    refine ⟨712659553588582968031141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 950212738118110624041521 712659553588582968031141)
    ·
      refine ⟨133623666297859306505839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 712659553588582968031141 133623666297859306505839)
      ·
        refine ⟨200435499446788959758759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133623666297859306505839 200435499446788959758759)
        ·
          refine ⟨300653249170183439638139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200435499446788959758759 300653249170183439638139)
          ·
            refine ⟨450979873755275159457209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300653249170183439638139 450979873755275159457209)
            ·
              refine ⟨338234905316456369592907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450979873755275159457209 338234905316456369592907)
              ·
                refine ⟨507352357974684554389361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338234905316456369592907 507352357974684554389361)
                ·
                  refine ⟨380514268481013415792021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507352357974684554389361 380514268481013415792021)
                  ·
                    refine ⟨17836606335047503865251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 380514268481013415792021 17836606335047503865251)
                    ·
                      rfl

theorem cell23_104210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_104210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104210 prefixEnd_104210 := by exact prefixLift 104210
  have htrace : WordTrace (prefixWord ++ tailWord_104210) baseStart_104210 baseEnd_104210 := by
    simpa [prefixWord, tailWord_104210, baseEnd_104210] using wordTrace_append hprefix tailTrace_104210
  have hstable : (prefixWord ++ tailWord_104210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104210).length < 2 ^ (prefixWord ++ tailWord_104210).sum := by decide
  have hdescent : baseEnd_104210 < baseStart_104210 := by decide
  rcases family_descends (prefixWord ++ tailWord_104210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104213 : List Nat := [1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_104213 : Nat := 118140960795 + 104213 * 2 ^ 59
def prefixEnd_104213 : Nat := 4983230072969 + 3 ^ 40 * 104213 * 2
def baseEnd_104213 : Nat := 53511359447105999858239

theorem tailTrace_104213 : CollatzResearch.WordTrace tailWord_104213 prefixEnd_104213 53511359447105999858239 := by
  unfold tailWord_104213
  simp only [CollatzResearch.WordTrace]
  refine ⟨3800960371461574008525293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2533973580974382672350195 3800960371461574008525293)
  ·
    refine ⟨1425360139298090253196985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3800960371461574008525293 1425360139298090253196985)
    ·
      refine ⟨1069020104473567689897739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1425360139298090253196985 1069020104473567689897739)
      ·
        refine ⟨1603530156710351534846609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1069020104473567689897739 1603530156710351534846609)
        ·
          refine ⟨1202647617532763651134957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603530156710351534846609 1202647617532763651134957)
          ·
            refine ⟨450992856574786369175609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1202647617532763651134957 450992856574786369175609)
            ·
              refine ⟨338244642431089776881707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450992856574786369175609 338244642431089776881707)
              ·
                refine ⟨507366963646634665322561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338244642431089776881707 507366963646634665322561)
                ·
                  refine ⟨380525222734975998991921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507366963646634665322561 380525222734975998991921)
                  ·
                    refine ⟨285393917051231999243941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 380525222734975998991921 285393917051231999243941)
                    ·
                      refine ⟨53511359447105999858239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 285393917051231999243941 53511359447105999858239)
                      ·
                        rfl

theorem cell23_104213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_104213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104213 prefixEnd_104213 := by exact prefixLift 104213
  have htrace : WordTrace (prefixWord ++ tailWord_104213) baseStart_104213 baseEnd_104213 := by
    simpa [prefixWord, tailWord_104213, baseEnd_104213] using wordTrace_append hprefix tailTrace_104213
  have hstable : (prefixWord ++ tailWord_104213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104213).length < 2 ^ (prefixWord ++ tailWord_104213).sum := by decide
  have hdescent : baseEnd_104213 < baseStart_104213 := by decide
  rcases family_descends (prefixWord ++ tailWord_104213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104256 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_104256 : Nat := 118140960795 + 104256 * 2 ^ 59
def prefixEnd_104256 : Nat := 4983230072969 + 3 ^ 40 * 104256 * 2
def baseEnd_104256 : Nat := 53533439115249331620541

theorem tailTrace_104256 : CollatzResearch.WordTrace tailWord_104256 prefixEnd_104256 53533439115249331620541 := by
  unfold tailWord_104256
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901264355152896176170311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2535019140203861568227081 1901264355152896176170311)
  ·
    refine ⟨2851896532729344264255467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1901264355152896176170311 2851896532729344264255467)
    ·
      refine ⟨4277844799094016396383201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2851896532729344264255467 4277844799094016396383201)
      ·
        refine ⟨3208383599320512297287401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4277844799094016396383201 3208383599320512297287401)
        ·
          refine ⟨2406287699490384222965551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3208383599320512297287401 2406287699490384222965551)
          ·
            refine ⟨3609431549235576334448327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406287699490384222965551 3609431549235576334448327)
            ·
              refine ⟨5414147323853364501672491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3609431549235576334448327 5414147323853364501672491)
              ·
                refine ⟨8121220985780046752508737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5414147323853364501672491 8121220985780046752508737)
                ·
                  refine ⟨6090915739335035064381553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8121220985780046752508737 6090915739335035064381553)
                  ·
                    refine ⟨4568186804501276298286165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6090915739335035064381553 4568186804501276298286165)
                    ·
                      refine ⟨53533439115249331620541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4568186804501276298286165 53533439115249331620541)
                      ·
                        rfl

theorem cell23_104256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_104256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104256 prefixEnd_104256 := by exact prefixLift 104256
  have htrace : WordTrace (prefixWord ++ tailWord_104256) baseStart_104256 baseEnd_104256 := by
    simpa [prefixWord, tailWord_104256, baseEnd_104256] using wordTrace_append hprefix tailTrace_104256
  have hstable : (prefixWord ++ tailWord_104256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104256).length < 2 ^ (prefixWord ++ tailWord_104256).sum := by decide
  have hdescent : baseEnd_104256 < baseStart_104256 := by decide
  rcases family_descends (prefixWord ++ tailWord_104256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104268 : List Nat := [2, 2, 1, 3, 5, 1, 2, 1, 2, 2, 2]
def baseStart_104268 : Nat := 118140960795 + 104268 * 2 ^ 59
def prefixEnd_104268 : Nat := 4983230072969 + 3 ^ 40 * 104268 * 2
def baseEnd_104268 : Nat := 53539600883103284670487

theorem tailTrace_104268 : CollatzResearch.WordTrace tailWord_104268 prefixEnd_104268 53539600883103284670487 := by
  unfold tailWord_104268
  simp only [CollatzResearch.WordTrace]
  refine ⟨1901483193131159200888729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2535310924174878934518305 1901483193131159200888729)
  ·
    refine ⟨1426112394848369400666547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1901483193131159200888729 1426112394848369400666547)
    ·
      refine ⟨2139168592272554100999821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426112394848369400666547 2139168592272554100999821)
      ·
        refine ⟨802188222102207787874933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2139168592272554100999821 802188222102207787874933)
        ·
          refine ⟨75205145822081980113275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 802188222102207787874933 75205145822081980113275)
          ·
            refine ⟨112807718733122970169913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75205145822081980113275 112807718733122970169913)
            ·
              refine ⟨84605789049842227627435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112807718733122970169913 84605789049842227627435)
              ·
                refine ⟨126908683574763341441153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84605789049842227627435 126908683574763341441153)
                ·
                  refine ⟨95181512681072506080865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126908683574763341441153 95181512681072506080865)
                  ·
                    refine ⟨71386134510804379560649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95181512681072506080865 71386134510804379560649)
                    ·
                      refine ⟨53539600883103284670487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71386134510804379560649 53539600883103284670487)
                      ·
                        rfl

theorem cell23_104268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_104268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104268 prefixEnd_104268 := by exact prefixLift 104268
  have htrace : WordTrace (prefixWord ++ tailWord_104268) baseStart_104268 baseEnd_104268 := by
    simpa [prefixWord, tailWord_104268, baseEnd_104268] using wordTrace_append hprefix tailTrace_104268
  have hstable : (prefixWord ++ tailWord_104268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104268).length < 2 ^ (prefixWord ++ tailWord_104268).sum := by decide
  have hdescent : baseEnd_104268 < baseStart_104268 := by decide
  rcases family_descends (prefixWord ++ tailWord_104268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104334 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_104334 : Nat := 118140960795 + 104334 * 2 ^ 59
def prefixEnd_104334 : Nat := 4983230072969 + 3 ^ 40 * 104334 * 2
def baseEnd_104334 : Nat := 17857830202100008815061

theorem tailTrace_104334 : CollatzResearch.WordTrace tailWord_104334 prefixEnd_104334 17857830202100008815061 := by
  unfold tailWord_104334
  simp only [CollatzResearch.WordTrace]
  refine ⟨475671700502901459210007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2536915736015474449120037 475671700502901459210007)
  ·
    refine ⟨713507550754352188815011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 475671700502901459210007 713507550754352188815011)
    ·
      refine ⟨1070261326131528283222517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 713507550754352188815011 1070261326131528283222517)
      ·
        refine ⟨100336999324830776552111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1070261326131528283222517 100336999324830776552111)
        ·
          refine ⟨150505498987246164828167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100336999324830776552111 150505498987246164828167)
          ·
            refine ⟨225758248480869247242251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150505498987246164828167 225758248480869247242251)
            ·
              refine ⟨338637372721303870863377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225758248480869247242251 338637372721303870863377)
              ·
                refine ⟨253978029540977903147533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338637372721303870863377 253978029540977903147533)
                ·
                  refine ⟨95241761077866713680325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 253978029540977903147533 95241761077866713680325)
                  ·
                    refine ⟨17857830202100008815061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95241761077866713680325 17857830202100008815061)
                    ·
                      rfl

theorem cell23_104334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_104334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104334 prefixEnd_104334 := by exact prefixLift 104334
  have htrace : WordTrace (prefixWord ++ tailWord_104334) baseStart_104334 baseEnd_104334 := by
    simpa [prefixWord, tailWord_104334, baseEnd_104334] using wordTrace_append hprefix tailTrace_104334
  have hstable : (prefixWord ++ tailWord_104334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104334).length < 2 ^ (prefixWord ++ tailWord_104334).sum := by decide
  have hdescent : baseEnd_104334 < baseStart_104334 := by decide
  rcases family_descends (prefixWord ++ tailWord_104334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104393 : List Nat := [1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_104393 : Nat := 118140960795 + 104393 * 2 ^ 59
def prefixEnd_104393 : Nat := 4983230072969 + 3 ^ 40 * 104393 * 2
def baseEnd_104393 : Nat := 53603785964915295607411

theorem tailTrace_104393 : CollatzResearch.WordTrace tailWord_104393 prefixEnd_104393 53603785964915295607411 := by
  unfold tailWord_104393
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807525510809464750077833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2538350340539643166718555 3807525510809464750077833)
  ·
    refine ⟨2855644133107098562558375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3807525510809464750077833 2855644133107098562558375)
    ·
      refine ⟨4283466199660647843837563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855644133107098562558375 4283466199660647843837563)
      ·
        refine ⟨6425199299490971765756345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283466199660647843837563 6425199299490971765756345)
        ·
          refine ⟨4818899474618228824317259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6425199299490971765756345 4818899474618228824317259)
          ·
            refine ⟨7228349211927343236475889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818899474618228824317259 7228349211927343236475889)
            ·
              refine ⟨5421261908945507427356917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7228349211927343236475889 5421261908945507427356917)
              ·
                refine ⟨508243303963641321314711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5421261908945507427356917 508243303963641321314711)
                ·
                  refine ⟨762364955945461981972067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508243303963641321314711 762364955945461981972067)
                  ·
                    refine ⟨1143547433918192972958101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 762364955945461981972067 1143547433918192972958101)
                    ·
                      refine ⟨53603785964915295607411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1143547433918192972958101 53603785964915295607411)
                      ·
                        rfl

theorem cell23_104393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_104393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104393 prefixEnd_104393 := by exact prefixLift 104393
  have htrace : WordTrace (prefixWord ++ tailWord_104393) baseStart_104393 baseEnd_104393 := by
    simpa [prefixWord, tailWord_104393, baseEnd_104393] using wordTrace_append hprefix tailTrace_104393
  have hstable : (prefixWord ++ tailWord_104393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104393).length < 2 ^ (prefixWord ++ tailWord_104393).sum := by decide
  have hdescent : baseEnd_104393 < baseStart_104393 := by decide
  rcases family_descends (prefixWord ++ tailWord_104393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104400 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3]
def baseStart_104400 : Nat := 118140960795 + 104400 * 2 ^ 59
def prefixEnd_104400 : Nat := 4983230072969 + 3 ^ 40 * 104400 * 2
def baseEnd_104400 : Nat := 53607380329496768219879

theorem tailTrace_104400 : CollatzResearch.WordTrace tailWord_104400 prefixEnd_104400 53607380329496768219879 := by
  unfold tailWord_104400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1903890410892052472791327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2538520547856069963721769 1903890410892052472791327)
  ·
    refine ⟨2855835616338078709186991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1903890410892052472791327 2855835616338078709186991)
    ·
      refine ⟨4283753424507118063780487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2855835616338078709186991 4283753424507118063780487)
      ·
        refine ⟨6425630136760677095670731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283753424507118063780487 6425630136760677095670731)
        ·
          refine ⟨9638445205141015643506097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6425630136760677095670731 9638445205141015643506097)
          ·
            refine ⟨7228833903855761732629573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9638445205141015643506097 7228833903855761732629573)
            ·
              refine ⟨1355406356972955324868045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7228833903855761732629573 1355406356972955324868045)
              ·
                refine ⟨508277383864858246825517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355406356972955324868045 508277383864858246825517)
                ·
                  refine ⟨190604018949321842559569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 508277383864858246825517 190604018949321842559569)
                  ·
                    refine ⟨142953014211991381919677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190604018949321842559569 142953014211991381919677)
                    ·
                      refine ⟨53607380329496768219879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 142953014211991381919677 53607380329496768219879)
                      ·
                        rfl

theorem cell23_104400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 3].length) (baseStart_104400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104400 prefixEnd_104400 := by exact prefixLift 104400
  have htrace : WordTrace (prefixWord ++ tailWord_104400) baseStart_104400 baseEnd_104400 := by
    simpa [prefixWord, tailWord_104400, baseEnd_104400] using wordTrace_append hprefix tailTrace_104400
  have hstable : (prefixWord ++ tailWord_104400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104400).length < 2 ^ (prefixWord ++ tailWord_104400).sum := by decide
  have hdescent : baseEnd_104400 < baseStart_104400 := by decide
  rcases family_descends (prefixWord ++ tailWord_104400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104417 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 3]
def baseStart_104417 : Nat := 118140960795 + 104417 * 2 ^ 59
def prefixEnd_104417 : Nat := 4983230072969 + 3 ^ 40 * 104417 * 2
def baseEnd_104417 : Nat := 53616109500623201707301

theorem tailTrace_104417 : CollatzResearch.WordTrace tailWord_104417 prefixEnd_104417 53616109500623201707301 := by
  unfold tailWord_104417
  simp only [CollatzResearch.WordTrace]
  refine ⟨3808400862722516848951505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2538933908481677899301003 3808400862722516848951505)
  ·
    refine ⟨2856300647041887636713629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3808400862722516848951505 2856300647041887636713629)
    ·
      refine ⟨1071112742640707863767611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2856300647041887636713629 1071112742640707863767611)
      ·
        refine ⟨1606669113961061795651417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1071112742640707863767611 1606669113961061795651417)
        ·
          refine ⟨1205001835470796346738563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1606669113961061795651417 1205001835470796346738563)
          ·
            refine ⟨1807502753206194520107845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205001835470796346738563 1807502753206194520107845)
            ·
              refine ⟨338906766226161472520221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1807502753206194520107845 338906766226161472520221)
              ·
                refine ⟨127090037334810552195083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338906766226161472520221 127090037334810552195083)
                ·
                  refine ⟨190635056002215828292625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127090037334810552195083 190635056002215828292625)
                  ·
                    refine ⟨142976292001661871219469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 190635056002215828292625 142976292001661871219469)
                    ·
                      refine ⟨53616109500623201707301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 142976292001661871219469 53616109500623201707301)
                      ·
                        rfl

theorem cell23_104417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_104417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104417 prefixEnd_104417 := by exact prefixLift 104417
  have htrace : WordTrace (prefixWord ++ tailWord_104417) baseStart_104417 baseEnd_104417 := by
    simpa [prefixWord, tailWord_104417, baseEnd_104417] using wordTrace_append hprefix tailTrace_104417
  have hstable : (prefixWord ++ tailWord_104417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104417).length < 2 ^ (prefixWord ++ tailWord_104417).sum := by decide
  have hdescent : baseEnd_104417 < baseStart_104417 := by decide
  rcases family_descends (prefixWord ++ tailWord_104417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104468 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 1, 1, 5]
def baseStart_104468 : Nat := 118140960795 + 104468 * 2 ^ 59
def prefixEnd_104468 : Nat := 4983230072969 + 3 ^ 40 * 104468 * 2
def baseEnd_104468 : Nat := 53642297014002502169567

theorem tailTrace_104468 : CollatzResearch.WordTrace tailWord_104468 prefixEnd_104468 53642297014002502169567 := by
  unfold tailWord_104468
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905130492768876279529029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2540173990358501706038705 1905130492768876279529029)
  ·
    refine ⟨357211967394164302411693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1905130492768876279529029 357211967394164302411693)
    ·
      refine ⟨133954487772811613404385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 357211967394164302411693 133954487772811613404385)
      ·
        refine ⟨100465865829608710053289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133954487772811613404385 100465865829608710053289)
        ·
          refine ⟨75349399372206532539967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100465865829608710053289 75349399372206532539967)
          ·
            refine ⟨113024099058309798809951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75349399372206532539967 113024099058309798809951)
            ·
              refine ⟨169536148587464698214927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113024099058309798809951 169536148587464698214927)
              ·
                refine ⟨254304222881197047322391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169536148587464698214927 254304222881197047322391)
                ·
                  refine ⟨381456334321795570983587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254304222881197047322391 381456334321795570983587)
                  ·
                    refine ⟨572184501482693356475381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 381456334321795570983587 572184501482693356475381)
                    ·
                      refine ⟨53642297014002502169567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 572184501482693356475381 53642297014002502169567)
                      ·
                        rfl

theorem cell23_104468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_104468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104468 prefixEnd_104468 := by exact prefixLift 104468
  have htrace : WordTrace (prefixWord ++ tailWord_104468) baseStart_104468 baseEnd_104468 := by
    simpa [prefixWord, tailWord_104468, baseEnd_104468] using wordTrace_append hprefix tailTrace_104468
  have hstable : (prefixWord ++ tailWord_104468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104468).length < 2 ^ (prefixWord ++ tailWord_104468).sum := by decide
  have hdescent : baseEnd_104468 < baseStart_104468 := by decide
  rcases family_descends (prefixWord ++ tailWord_104468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104481 : List Nat := [1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 3]
def baseStart_104481 : Nat := 118140960795 + 104481 * 2 ^ 59
def prefixEnd_104481 : Nat := 4983230072969 + 3 ^ 40 * 104481 * 2
def baseEnd_104481 : Nat := 53648972262510951307007

theorem tailTrace_104481 : CollatzResearch.WordTrace tailWord_104481 prefixEnd_104481 53648972262510951307007 := by
  unfold tailWord_104481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810735134490655779281297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2540490089660437186187531 3810735134490655779281297)
  ·
    refine ⟨2858051350867991834460973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3810735134490655779281297 2858051350867991834460973)
    ·
      refine ⟨1071769256575496937922865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2858051350867991834460973 1071769256575496937922865)
      ·
        refine ⟨803826942431622703442149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1071769256575496937922865 803826942431622703442149)
        ·
          refine ⟨150717551705929256895403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 803826942431622703442149 150717551705929256895403)
          ·
            refine ⟨226076327558893885343105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150717551705929256895403 226076327558893885343105)
            ·
              refine ⟨169557245669170414007329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226076327558893885343105 169557245669170414007329)
              ·
                refine ⟨127167934251877810505497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169557245669170414007329 127167934251877810505497)
                ·
                  refine ⟨95375950688908357879123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127167934251877810505497 95375950688908357879123)
                  ·
                    refine ⟨143063926033362536818685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95375950688908357879123 143063926033362536818685)
                    ·
                      refine ⟨53648972262510951307007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 143063926033362536818685 53648972262510951307007)
                      ·
                        rfl

theorem cell23_104481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_104481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104481 prefixEnd_104481 := by exact prefixLift 104481
  have htrace : WordTrace (prefixWord ++ tailWord_104481) baseStart_104481 baseEnd_104481 := by
    simpa [prefixWord, tailWord_104481, baseEnd_104481] using wordTrace_append hprefix tailTrace_104481
  have hstable : (prefixWord ++ tailWord_104481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104481).length < 2 ^ (prefixWord ++ tailWord_104481).sum := by decide
  have hdescent : baseEnd_104481 < baseStart_104481 := by decide
  rcases family_descends (prefixWord ++ tailWord_104481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104547 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 1, 7, 2]
def baseStart_104547 : Nat := 118140960795 + 104547 * 2 ^ 59
def prefixEnd_104547 : Nat := 4983230072969 + 3 ^ 40 * 104547 * 2
def baseEnd_104547 : Nat := 53682861985707693081703

theorem tailTrace_104547 : CollatzResearch.WordTrace tailWord_104547 prefixEnd_104547 53682861985707693081703 := by
  unfold tailWord_104547
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813142352251549051183895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2542094901501032700789263 3813142352251549051183895)
  ·
    refine ⟨5719713528377323576775843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813142352251549051183895 5719713528377323576775843)
    ·
      refine ⟨8579570292565985365163765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5719713528377323576775843 8579570292565985365163765)
      ·
        refine ⟨804334714928061127984103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8579570292565985365163765 804334714928061127984103)
        ·
          refine ⟨1206502072392091691976155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804334714928061127984103 1206502072392091691976155)
          ·
            refine ⟨1809753108588137537964233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206502072392091691976155 1809753108588137537964233)
            ·
              refine ⟨1357314831441103153473175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809753108588137537964233 1357314831441103153473175)
              ·
                refine ⟨2035972247161654730209763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357314831441103153473175 2035972247161654730209763)
                ·
                  refine ⟨3053958370742482095314645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2035972247161654730209763 3053958370742482095314645)
                  ·
                    refine ⟨71577149314276924108937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3053958370742482095314645 71577149314276924108937)
                    ·
                      refine ⟨53682861985707693081703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71577149314276924108937 53682861985707693081703)
                      ·
                        rfl

theorem cell23_104547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_104547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104547 prefixEnd_104547 := by exact prefixLift 104547
  have htrace : WordTrace (prefixWord ++ tailWord_104547) baseStart_104547 baseEnd_104547 := by
    simpa [prefixWord, tailWord_104547, baseEnd_104547] using wordTrace_append hprefix tailTrace_104547
  have hstable : (prefixWord ++ tailWord_104547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104547).length < 2 ^ (prefixWord ++ tailWord_104547).sum := by decide
  have hdescent : baseEnd_104547 < baseStart_104547 := by decide
  rcases family_descends (prefixWord ++ tailWord_104547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104594 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 2, 1, 4]
def baseStart_104594 : Nat := 118140960795 + 104594 * 2 ^ 59
def prefixEnd_104594 : Nat := 4983230072969 + 3 ^ 40 * 104594 * 2
def baseEnd_104594 : Nat := 53706995576469009193987

theorem tailTrace_104594 : CollatzResearch.WordTrace tailWord_104594 prefixEnd_104594 53706995576469009193987 := by
  unfold tailWord_104594
  simp only [CollatzResearch.WordTrace]
  refine ⟨953714145770319019536209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2543237722054184052096557 953714145770319019536209)
  ·
    refine ⟨715285609327739264652157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 953714145770319019536209 715285609327739264652157)
    ·
      refine ⟨268232103497902224244559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 715285609327739264652157 268232103497902224244559)
      ·
        refine ⟨402348155246853336366839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268232103497902224244559 402348155246853336366839)
        ·
          refine ⟨603522232870280004550259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402348155246853336366839 603522232870280004550259)
          ·
            refine ⟨905283349305420006825389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603522232870280004550259 905283349305420006825389)
            ·
              refine ⟨339481255989532502559521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905283349305420006825389 339481255989532502559521)
              ·
                refine ⟨254610941992149376919641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339481255989532502559521 254610941992149376919641)
                ·
                  refine ⟨190958206494112032689731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 254610941992149376919641 190958206494112032689731)
                  ·
                    refine ⟨286437309741168049034597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190958206494112032689731 286437309741168049034597)
                    ·
                      refine ⟨53706995576469009193987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 286437309741168049034597 53706995576469009193987)
                      ·
                        rfl

theorem cell23_104594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_104594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104594 prefixEnd_104594 := by exact prefixLift 104594
  have htrace : WordTrace (prefixWord ++ tailWord_104594) baseStart_104594 baseEnd_104594 := by
    simpa [prefixWord, tailWord_104594, baseEnd_104594] using wordTrace_append hprefix tailTrace_104594
  have hstable : (prefixWord ++ tailWord_104594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104594).length < 2 ^ (prefixWord ++ tailWord_104594).sum := by decide
  have hdescent : baseEnd_104594 < baseStart_104594 := by decide
  rcases family_descends (prefixWord ++ tailWord_104594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104620 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_104620 : Nat := 118140960795 + 104620 * 2 ^ 59
def prefixEnd_104620 : Nat := 4983230072969 + 3 ^ 40 * 104620 * 2
def baseEnd_104620 : Nat := 53720346073485907468867

theorem tailTrace_104620 : CollatzResearch.WordTrace tailWord_104620 prefixEnd_104620 53720346073485907468867 := by
  unfold tailWord_104620
  simp only [CollatzResearch.WordTrace]
  refine ⟨1907902440493541259295657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2543869920658055012394209 1907902440493541259295657)
  ·
    refine ⟨1430926830370155944471743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1907902440493541259295657 1430926830370155944471743)
    ·
      refine ⟨2146390245555233916707615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430926830370155944471743 2146390245555233916707615)
      ·
        refine ⟨3219585368332850875061423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146390245555233916707615 3219585368332850875061423)
        ·
          refine ⟨4829378052499276312592135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219585368332850875061423 4829378052499276312592135)
          ·
            refine ⟨7244067078748914468888203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829378052499276312592135 7244067078748914468888203)
            ·
              refine ⟨10866100618123371703332305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244067078748914468888203 10866100618123371703332305)
              ·
                refine ⟨8149575463592528777499229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10866100618123371703332305 8149575463592528777499229)
                ·
                  refine ⟨3056090798847198291562211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8149575463592528777499229 3056090798847198291562211)
                  ·
                    refine ⟨4584136198270797437343317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3056090798847198291562211 4584136198270797437343317)
                    ·
                      refine ⟨53720346073485907468867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 4584136198270797437343317 53720346073485907468867)
                      ·
                        rfl

theorem cell23_104620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_104620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104620 prefixEnd_104620 := by exact prefixLift 104620
  have htrace : WordTrace (prefixWord ++ tailWord_104620) baseStart_104620 baseEnd_104620 := by
    simpa [prefixWord, tailWord_104620, baseEnd_104620] using wordTrace_append hprefix tailTrace_104620
  have hstable : (prefixWord ++ tailWord_104620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104620).length < 2 ^ (prefixWord ++ tailWord_104620).sum := by decide
  have hdescent : baseEnd_104620 < baseStart_104620 := by decide
  rcases family_descends (prefixWord ++ tailWord_104620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104667 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 4]
def baseStart_104667 : Nat := 118140960795 + 104667 * 2 ^ 59
def prefixEnd_104667 : Nat := 4983230072969 + 3 ^ 40 * 104667 * 2
def baseEnd_104667 : Nat := 53744479664247223581151

theorem tailTrace_104667 : CollatzResearch.WordTrace tailWord_104667 prefixEnd_104667 53744479664247223581151 := by
  unfold tailWord_104667
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817519111816809545552255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2545012741211206363701503 3817519111816809545552255)
  ·
    refine ⟨5726278667725214318328383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3817519111816809545552255 5726278667725214318328383)
    ·
      refine ⟨8589418001587821477492575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726278667725214318328383 8589418001587821477492575)
      ·
        refine ⟨12884127002381732216238863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8589418001587821477492575 12884127002381732216238863)
        ·
          refine ⟨19326190503572598324358295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12884127002381732216238863 19326190503572598324358295)
          ·
            refine ⟨28989285755358897486537443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19326190503572598324358295 28989285755358897486537443)
            ·
              refine ⟨43483928633038346229806165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28989285755358897486537443 43483928633038346229806165)
              ·
                refine ⟨509577288668418119880541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 43483928633038346229806165 509577288668418119880541)
                ·
                  refine ⟨191091483250656794955203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 509577288668418119880541 191091483250656794955203)
                  ·
                    refine ⟨286637224875985192432805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191091483250656794955203 286637224875985192432805)
                    ·
                      refine ⟨53744479664247223581151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 286637224875985192432805 53744479664247223581151)
                      ·
                        rfl

theorem cell23_104667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3, 1, 4].length) (baseStart_104667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104667 prefixEnd_104667 := by exact prefixLift 104667
  have htrace : WordTrace (prefixWord ++ tailWord_104667) baseStart_104667 baseEnd_104667 := by
    simpa [prefixWord, tailWord_104667, baseEnd_104667] using wordTrace_append hprefix tailTrace_104667
  have hstable : (prefixWord ++ tailWord_104667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104667).length < 2 ^ (prefixWord ++ tailWord_104667).sum := by decide
  have hdescent : baseEnd_104667 < baseStart_104667 := by decide
  rcases family_descends (prefixWord ++ tailWord_104667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104684 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 4]
def baseStart_104684 : Nat := 118140960795 + 104684 * 2 ^ 59
def prefixEnd_104684 : Nat := 4983230072969 + 3 ^ 40 * 104684 * 2
def baseEnd_104684 : Nat := 53753208835373657068573

theorem tailTrace_104684 : CollatzResearch.WordTrace tailWord_104684 prefixEnd_104684 53753208835373657068573 := by
  unfold tailWord_104684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1909069576377610724460553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2545426101836814299280737 1909069576377610724460553)
  ·
    refine ⟨1431802182283208043345415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1909069576377610724460553 1431802182283208043345415)
    ·
      refine ⟨2147703273424812065018123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1431802182283208043345415 2147703273424812065018123)
      ·
        refine ⟨3221554910137218097527185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147703273424812065018123 3221554910137218097527185)
        ·
          refine ⟨2416166182602913573145389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221554910137218097527185 2416166182602913573145389)
          ·
            refine ⟨906062318476092589929521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2416166182602913573145389 906062318476092589929521)
            ·
              refine ⟨679546738857069442447141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906062318476092589929521 679546738857069442447141)
              ·
                refine ⟨127415013535700520458839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 679546738857069442447141 127415013535700520458839)
                ·
                  refine ⟨191122520303550780688259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127415013535700520458839 191122520303550780688259)
                  ·
                    refine ⟨286683780455326171032389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 191122520303550780688259 286683780455326171032389)
                    ·
                      refine ⟨53753208835373657068573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 286683780455326171032389 53753208835373657068573)
                      ·
                        rfl

theorem cell23_104684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 4].length) (baseStart_104684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104684 prefixEnd_104684 := by exact prefixLift 104684
  have htrace : WordTrace (prefixWord ++ tailWord_104684) baseStart_104684 baseEnd_104684 := by
    simpa [prefixWord, tailWord_104684, baseEnd_104684] using wordTrace_append hprefix tailTrace_104684
  have hstable : (prefixWord ++ tailWord_104684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104684).length < 2 ^ (prefixWord ++ tailWord_104684).sum := by decide
  have hdescent : baseEnd_104684 < baseStart_104684 := by decide
  rcases family_descends (prefixWord ++ tailWord_104684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104694 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_104694 : Nat := 118140960795 + 104694 * 2 ^ 59
def prefixEnd_104694 : Nat := 4983230072969 + 3 ^ 40 * 104694 * 2
def baseEnd_104694 : Nat := 17919447880639539314509

theorem tailTrace_104694 : CollatzResearch.WordTrace tailWord_104694 prefixEnd_104694 17919447880639539314509 := by
  unfold tailWord_104694
  simp only [CollatzResearch.WordTrace]
  refine ⟨238656492669937072299071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2545669255145995437856757 238656492669937072299071)
  ·
    refine ⟨357984739004905608448607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 238656492669937072299071 357984739004905608448607)
    ·
      refine ⟨536977108507358412672911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 357984739004905608448607 536977108507358412672911)
      ·
        refine ⟨805465662761037619009367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 536977108507358412672911 805465662761037619009367)
        ·
          refine ⟨1208198494141556428514051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805465662761037619009367 1208198494141556428514051)
          ·
            refine ⟨1812297741212334642771077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208198494141556428514051 1812297741212334642771077)
            ·
              refine ⟨339805826477312745519577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1812297741212334642771077 339805826477312745519577)
              ·
                refine ⟨254854369857984559139683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339805826477312745519577 254854369857984559139683)
                ·
                  refine ⟨382281554786976838709525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254854369857984559139683 382281554786976838709525)
                  ·
                    refine ⟨17919447880639539314509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 382281554786976838709525 17919447880639539314509)
                    ·
                      rfl

theorem cell23_104694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_104694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104694 prefixEnd_104694 := by exact prefixLift 104694
  have htrace : WordTrace (prefixWord ++ tailWord_104694) baseStart_104694 baseEnd_104694 := by
    simpa [prefixWord, tailWord_104694, baseEnd_104694] using wordTrace_append hprefix tailTrace_104694
  have hstable : (prefixWord ++ tailWord_104694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104694).length < 2 ^ (prefixWord ++ tailWord_104694).sum := by decide
  have hdescent : baseEnd_104694 < baseStart_104694 := by decide
  rcases family_descends (prefixWord ++ tailWord_104694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104697 : List Nat := [1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_104697 : Nat := 118140960795 + 104697 * 2 ^ 59
def prefixEnd_104697 : Nat := 4983230072969 + 3 ^ 40 * 104697 * 2
def baseEnd_104697 : Nat := 53759884083882106206013

theorem tailTrace_104697 : CollatzResearch.WordTrace tailWord_104697 prefixEnd_104697 53759884083882106206013 := by
  unfold tailWord_104697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818613301708124669144345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2545742201138749779429563 3818613301708124669144345)
  ·
    refine ⟨2863959976281093501858259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3818613301708124669144345 2863959976281093501858259)
    ·
      refine ⟨4295939964421640252787389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863959976281093501858259 4295939964421640252787389)
      ·
        refine ⟨1610977486658115094795271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4295939964421640252787389 1610977486658115094795271)
        ·
          refine ⟨2416466229987172642192907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1610977486658115094795271 2416466229987172642192907)
          ·
            refine ⟨3624699344980758963289361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416466229987172642192907 3624699344980758963289361)
            ·
              refine ⟨2718524508735569222467021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624699344980758963289361 2718524508735569222467021)
              ·
                refine ⟨1019446690775838458425133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718524508735569222467021 1019446690775838458425133)
                ·
                  refine ⟨382292509040939421909425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019446690775838458425133 382292509040939421909425)
                  ·
                    refine ⟨286719381780704566432069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 382292509040939421909425 286719381780704566432069)
                    ·
                      refine ⟨53759884083882106206013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 286719381780704566432069 53759884083882106206013)
                      ·
                        rfl

theorem cell23_104697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_104697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104697 prefixEnd_104697 := by exact prefixLift 104697
  have htrace : WordTrace (prefixWord ++ tailWord_104697) baseStart_104697 baseEnd_104697 := by
    simpa [prefixWord, tailWord_104697, baseEnd_104697] using wordTrace_append hprefix tailTrace_104697
  have hstable : (prefixWord ++ tailWord_104697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104697).length < 2 ^ (prefixWord ++ tailWord_104697).sum := by decide
  have hdescent : baseEnd_104697 < baseStart_104697 := by decide
  rcases family_descends (prefixWord ++ tailWord_104697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104718 : List Nat := [4, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_104718 : Nat := 118140960795 + 104718 * 2 ^ 59
def prefixEnd_104718 : Nat := 4983230072969 + 3 ^ 40 * 104718 * 2
def baseEnd_104718 : Nat := 53770667177626524043417

theorem tailTrace_104718 : CollatzResearch.WordTrace tailWord_104718 prefixEnd_104718 53770667177626524043417 := by
  unfold tailWord_104718
  simp only [CollatzResearch.WordTrace]
  refine ⟨477422404329005656957351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2546252823088030170439205 477422404329005656957351)
  ·
    refine ⟨716133606493508485436027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 477422404329005656957351 716133606493508485436027)
    ·
      refine ⟨1074200409740262728154041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 716133606493508485436027 1074200409740262728154041)
      ·
        refine ⟨805650307305197046115531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1074200409740262728154041 805650307305197046115531)
        ·
          refine ⟨1208475460957795569173297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805650307305197046115531 1208475460957795569173297)
          ·
            refine ⟨906356595718346676879973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208475460957795569173297 906356595718346676879973)
            ·
              refine ⟨169941861697190001914995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 906356595718346676879973 169941861697190001914995)
              ·
                refine ⟨254912792545785002872493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169941861697190001914995 254912792545785002872493)
                ·
                  refine ⟨95592297204669376077185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 254912792545785002872493 95592297204669376077185)
                  ·
                    refine ⟨71694222903502032057889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95592297204669376077185 71694222903502032057889)
                    ·
                      refine ⟨53770667177626524043417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71694222903502032057889 53770667177626524043417)
                      ·
                        rfl

theorem cell23_104718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_104718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104718 prefixEnd_104718 := by exact prefixLift 104718
  have htrace : WordTrace (prefixWord ++ tailWord_104718) baseStart_104718 baseEnd_104718 := by
    simpa [prefixWord, tailWord_104718, baseEnd_104718] using wordTrace_append hprefix tailTrace_104718
  have hstable : (prefixWord ++ tailWord_104718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104718).length < 2 ^ (prefixWord ++ tailWord_104718).sum := by decide
  have hdescent : baseEnd_104718 < baseStart_104718 := by decide
  rcases family_descends (prefixWord ++ tailWord_104718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104737 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 2, 7]
def baseStart_104737 : Nat := 118140960795 + 104737 * 2 ^ 59
def prefixEnd_104737 : Nat := 4983230072969 + 3 ^ 40 * 104737 * 2
def baseEnd_104737 : Nat := 17926807770020649901943

theorem tailTrace_104737 : CollatzResearch.WordTrace tailWord_104737 prefixEnd_104737 17926807770020649901943 := by
  unfold tailWord_104737
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820072221563211500600465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2546714814375474333733643 3820072221563211500600465)
  ·
    refine ⟨2865054166172408625450349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3820072221563211500600465 2865054166172408625450349)
    ·
      refine ⟨1074395312314653234543881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2865054166172408625450349 1074395312314653234543881)
      ·
        refine ⟨805796484235989925907911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1074395312314653234543881 805796484235989925907911)
        ·
          refine ⟨1208694726353984888861867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 805796484235989925907911 1208694726353984888861867)
          ·
            refine ⟨1813042089530977333292801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208694726353984888861867 1813042089530977333292801)
            ·
              refine ⟨1359781567148232999969601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813042089530977333292801 1359781567148232999969601)
              ·
                refine ⟨1019836175361174749977201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359781567148232999969601 1019836175361174749977201)
                ·
                  refine ⟨764877131520881062482901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1019836175361174749977201 764877131520881062482901)
                  ·
                    refine ⟨17926807770020649901943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 764877131520881062482901 17926807770020649901943)
                    ·
                      rfl

theorem cell23_104737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_104737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104737 prefixEnd_104737 := by exact prefixLift 104737
  have htrace : WordTrace (prefixWord ++ tailWord_104737) baseStart_104737 baseEnd_104737 := by
    simpa [prefixWord, tailWord_104737, baseEnd_104737] using wordTrace_append hprefix tailTrace_104737
  have hstable : (prefixWord ++ tailWord_104737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104737).length < 2 ^ (prefixWord ++ tailWord_104737).sum := by decide
  have hdescent : baseEnd_104737 < baseStart_104737 := by decide
  rcases family_descends (prefixWord ++ tailWord_104737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104738 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 1, 2, 3]
def baseStart_104738 : Nat := 118140960795 + 104738 * 2 ^ 59
def prefixEnd_104738 : Nat := 4983230072969 + 3 ^ 40 * 104738 * 2
def baseEnd_104738 : Nat := 53780936790716445793325

theorem tailTrace_104738 : CollatzResearch.WordTrace tailWord_104738 prefixEnd_104738 53780936790716445793325 := by
  unfold tailWord_104738
  simp only [CollatzResearch.WordTrace]
  refine ⟨955027173639897167846717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2546739129706392447591245 955027173639897167846717)
  ·
    refine ⟨358135190114961437942519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 955027173639897167846717 358135190114961437942519)
    ·
      refine ⟨537202785172442156913779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 358135190114961437942519 537202785172442156913779)
      ·
        refine ⟨805804177758663235370669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537202785172442156913779 805804177758663235370669)
        ·
          refine ⟨302176566659498713264001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 805804177758663235370669 302176566659498713264001)
          ·
            refine ⟨226632424994624034948001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302176566659498713264001 226632424994624034948001)
            ·
              refine ⟨169974318745968026211001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226632424994624034948001 169974318745968026211001)
              ·
                refine ⟨127480739059476019658251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169974318745968026211001 127480739059476019658251)
                ·
                  refine ⟨191221108589214029487377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 127480739059476019658251 191221108589214029487377)
                  ·
                    refine ⟨143415831441910522115533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 191221108589214029487377 143415831441910522115533)
                    ·
                      refine ⟨53780936790716445793325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 143415831441910522115533 53780936790716445793325)
                      ·
                        rfl

theorem cell23_104738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_104738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104738 prefixEnd_104738 := by exact prefixLift 104738
  have htrace : WordTrace (prefixWord ++ tailWord_104738) baseStart_104738 baseEnd_104738 := by
    simpa [prefixWord, tailWord_104738, baseEnd_104738] using wordTrace_append hprefix tailTrace_104738
  have hstable : (prefixWord ++ tailWord_104738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104738).length < 2 ^ (prefixWord ++ tailWord_104738).sum := by decide
  have hdescent : baseEnd_104738 < baseStart_104738 := by decide
  rcases family_descends (prefixWord ++ tailWord_104738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104741 : List Nat := [1, 3, 1, 2, 5, 2, 2, 7]
def baseStart_104741 : Nat := 118140960795 + 104741 * 2 ^ 59
def prefixEnd_104741 : Nat := 4983230072969 + 3 ^ 40 * 104741 * 2
def baseEnd_104741 : Nat := 1991943601210367927993

theorem tailTrace_104741 : CollatzResearch.WordTrace tailWord_104741 prefixEnd_104741 1991943601210367927993 := by
  unfold tailWord_104741
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820218113548720183746077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2546812075699146789164051 3820218113548720183746077)
  ·
    refine ⟨1432581792580770068904779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3820218113548720183746077 1432581792580770068904779)
    ·
      refine ⟨2148872688871155103357169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432581792580770068904779 2148872688871155103357169)
      ·
        refine ⟨1611654516653366327517877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2148872688871155103357169 1611654516653366327517877)
        ·
          refine ⟨151092610936253093204801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1611654516653366327517877 151092610936253093204801)
          ·
            refine ⟨113319458202189819903601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151092610936253093204801 113319458202189819903601)
            ·
              refine ⟨84989593651642364927701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113319458202189819903601 84989593651642364927701)
              ·
                refine ⟨1991943601210367927993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84989593651642364927701 1991943601210367927993)
                ·
                  rfl

theorem cell23_104741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 7].length) (baseStart_104741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104741 prefixEnd_104741 := by exact prefixLift 104741
  have htrace : WordTrace (prefixWord ++ tailWord_104741) baseStart_104741 baseEnd_104741 := by
    simpa [prefixWord, tailWord_104741, baseEnd_104741] using wordTrace_append hprefix tailTrace_104741
  have hstable : (prefixWord ++ tailWord_104741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104741).length < 2 ^ (prefixWord ++ tailWord_104741).sum := by decide
  have hdescent : baseEnd_104741 < baseStart_104741 := by decide
  rcases family_descends (prefixWord ++ tailWord_104741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104769 : List Nat := [1, 2, 5, 2, 2, 1, 3, 2, 1, 2, 2]
def baseStart_104769 : Nat := 118140960795 + 104769 * 2 ^ 59
def prefixEnd_104769 : Nat := 4983230072969 + 3 ^ 40 * 104769 * 2
def baseEnd_104769 : Nat := 53796854691005824505683

theorem tailTrace_104769 : CollatzResearch.WordTrace tailWord_104769 prefixEnd_104769 53796854691005824505683 := by
  unfold tailWord_104769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821239357447280965765361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2547492904964853977176907 3821239357447280965765361)
  ·
    refine ⟨2865929518085460724324021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3821239357447280965765361 2865929518085460724324021)
    ·
      refine ⟨268680892320511942905377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2865929518085460724324021 268680892320511942905377)
      ·
        refine ⟨201510669240383957179033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268680892320511942905377 201510669240383957179033)
        ·
          refine ⟨151133001930287967884275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201510669240383957179033 151133001930287967884275)
          ·
            refine ⟨226699502895431951826413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151133001930287967884275 226699502895431951826413)
            ·
              refine ⟨85012313585786981934905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226699502895431951826413 85012313585786981934905)
              ·
                refine ⟨63759235189340236451179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85012313585786981934905 63759235189340236451179)
                ·
                  refine ⟨95638852784010354676769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63759235189340236451179 95638852784010354676769)
                  ·
                    refine ⟨71729139588007766007577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95638852784010354676769 71729139588007766007577)
                    ·
                      refine ⟨53796854691005824505683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71729139588007766007577 53796854691005824505683)
                      ·
                        rfl

theorem cell23_104769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_104769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104769 prefixEnd_104769 := by exact prefixLift 104769
  have htrace : WordTrace (prefixWord ++ tailWord_104769) baseStart_104769 baseEnd_104769 := by
    simpa [prefixWord, tailWord_104769, baseEnd_104769] using wordTrace_append hprefix tailTrace_104769
  have hstable : (prefixWord ++ tailWord_104769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104769).length < 2 ^ (prefixWord ++ tailWord_104769).sum := by decide
  have hdescent : baseEnd_104769 < baseStart_104769 := by decide
  rcases family_descends (prefixWord ++ tailWord_104769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104777 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_104777 : Nat := 118140960795 + 104777 * 2 ^ 59
def prefixEnd_104777 : Nat := 4983230072969 + 3 ^ 40 * 104777 * 2
def baseEnd_104777 : Nat := 53800962536241793205645

theorem tailTrace_104777 : CollatzResearch.WordTrace tailWord_104777 prefixEnd_104777 53800962536241793205645 := by
  unfold tailWord_104777
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821531141418298332056585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2547687427612198888037723 3821531141418298332056585)
  ·
    refine ⟨2866148356063723749042439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3821531141418298332056585 2866148356063723749042439)
    ·
      refine ⟨4299222534095585623563659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2866148356063723749042439 4299222534095585623563659)
      ·
        refine ⟨6448833801143378435345489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299222534095585623563659 6448833801143378435345489)
        ·
          refine ⟨4836625350857533826509117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6448833801143378435345489 4836625350857533826509117)
          ·
            refine ⟨1813734506571575184940919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4836625350857533826509117 1813734506571575184940919)
            ·
              refine ⟨2720601759857362777411379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813734506571575184940919 2720601759857362777411379)
              ·
                refine ⟨4080902639786044166117069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720601759857362777411379 4080902639786044166117069)
                ·
                  refine ⟨1530338489919766562293901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4080902639786044166117069 1530338489919766562293901)
                  ·
                    refine ⟨573876933719912460860213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1530338489919766562293901 573876933719912460860213)
                    ·
                      refine ⟨53800962536241793205645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 573876933719912460860213 53800962536241793205645)
                      ·
                        rfl

theorem cell23_104777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_104777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104777 prefixEnd_104777 := by exact prefixLift 104777
  have htrace : WordTrace (prefixWord ++ tailWord_104777) baseStart_104777 baseEnd_104777 := by
    simpa [prefixWord, tailWord_104777, baseEnd_104777] using wordTrace_append hprefix tailTrace_104777
  have hstable : (prefixWord ++ tailWord_104777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104777).length < 2 ^ (prefixWord ++ tailWord_104777).sum := by decide
  have hdescent : baseEnd_104777 < baseStart_104777 := by decide
  rcases family_descends (prefixWord ++ tailWord_104777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104785 : List Nat := [1, 2, 2, 1, 4, 4, 2, 1, 2, 1, 3]
def baseStart_104785 : Nat := 118140960795 + 104785 * 2 ^ 59
def prefixEnd_104785 : Nat := 4983230072969 + 3 ^ 40 * 104785 * 2
def baseEnd_104785 : Nat := 53805070381477761905609

theorem tailTrace_104785 : CollatzResearch.WordTrace tailWord_104785 prefixEnd_104785 53805070381477761905609 := by
  unfold tailWord_104785
  simp only [CollatzResearch.WordTrace]
  refine ⟨3821822925389315698347809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2547881950259543798898539 3821822925389315698347809)
  ·
    refine ⟨2866367194041986773760857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3821822925389315698347809 2866367194041986773760857)
    ·
      refine ⟨2149775395531490080320643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2866367194041986773760857 2149775395531490080320643)
      ·
        refine ⟨3224663093297235120480965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149775395531490080320643 3224663093297235120480965)
        ·
          refine ⟨604624329993231585090181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3224663093297235120480965 604624329993231585090181)
          ·
            refine ⟨113367061873730922204409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 604624329993231585090181 113367061873730922204409)
            ·
              refine ⟨85025296405298191653307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113367061873730922204409 85025296405298191653307)
              ·
                refine ⟨127537944607947287479961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85025296405298191653307 127537944607947287479961)
                ·
                  refine ⟨95653458455960465609971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127537944607947287479961 95653458455960465609971)
                  ·
                    refine ⟨143480187683940698414957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95653458455960465609971 143480187683940698414957)
                    ·
                      refine ⟨53805070381477761905609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 143480187683940698414957 53805070381477761905609)
                      ·
                        rfl

theorem cell23_104785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 1, 3].length) (baseStart_104785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104785 prefixEnd_104785 := by exact prefixLift 104785
  have htrace : WordTrace (prefixWord ++ tailWord_104785) baseStart_104785 baseEnd_104785 := by
    simpa [prefixWord, tailWord_104785, baseEnd_104785] using wordTrace_append hprefix tailTrace_104785
  have hstable : (prefixWord ++ tailWord_104785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104785).length < 2 ^ (prefixWord ++ tailWord_104785).sum := by decide
  have hdescent : baseEnd_104785 < baseStart_104785 := by decide
  rcases family_descends (prefixWord ++ tailWord_104785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104791 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 1, 4, 2]
def baseStart_104791 : Nat := 118140960795 + 104791 * 2 ^ 59
def prefixEnd_104791 : Nat := 4983230072969 + 3 ^ 40 * 104791 * 2
def baseEnd_104791 : Nat := 53808151265404738430581

theorem tailTrace_104791 : CollatzResearch.WordTrace tailWord_104791 prefixEnd_104791 53808151265404738430581 := by
  unfold tailWord_104791
  simp only [CollatzResearch.WordTrace]
  refine ⟨3822041763367578723066227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2548027842245052482044151 3822041763367578723066227)
  ·
    refine ⟨5733062645051368084599341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3822041763367578723066227 5733062645051368084599341)
    ·
      refine ⟨2149898491894263031724753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5733062645051368084599341 2149898491894263031724753)
      ·
        refine ⟨1612423868920697273793565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2149898491894263031724753 1612423868920697273793565)
        ·
          refine ⟨604658950845261477672587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1612423868920697273793565 604658950845261477672587)
          ·
            refine ⟨906988426267892216508881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604658950845261477672587 906988426267892216508881)
            ·
              refine ⟨680241319700919162381661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 906988426267892216508881 680241319700919162381661)
              ·
                refine ⟨255090494887844685893123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 680241319700919162381661 255090494887844685893123)
                ·
                  refine ⟨382635742331767028839685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255090494887844685893123 382635742331767028839685)
                  ·
                    refine ⟨71744201687206317907441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382635742331767028839685 71744201687206317907441)
                    ·
                      refine ⟨53808151265404738430581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71744201687206317907441 53808151265404738430581)
                      ·
                        rfl

theorem cell23_104791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_104791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104791 prefixEnd_104791 := by exact prefixLift 104791
  have htrace : WordTrace (prefixWord ++ tailWord_104791) baseStart_104791 baseEnd_104791 := by
    simpa [prefixWord, tailWord_104791, baseEnd_104791] using wordTrace_append hprefix tailTrace_104791
  have hstable : (prefixWord ++ tailWord_104791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104791).length < 2 ^ (prefixWord ++ tailWord_104791).sum := by decide
  have hdescent : baseEnd_104791 < baseStart_104791 := by decide
  rcases family_descends (prefixWord ++ tailWord_104791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104808 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 1, 4, 2]
def baseStart_104808 : Nat := 118140960795 + 104808 * 2 ^ 59
def prefixEnd_104808 : Nat := 4983230072969 + 3 ^ 40 * 104808 * 2
def baseEnd_104808 : Nat := 53816880436531171918003

theorem tailTrace_104808 : CollatzResearch.WordTrace tailWord_104808 prefixEnd_104808 53816880436531171918003 := by
  unfold tailWord_104808
  simp only [CollatzResearch.WordTrace]
  refine ⟨1911330902152995313217539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2548441202870660417623385 1911330902152995313217539)
  ·
    refine ⟨2866996353229492969826309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1911330902152995313217539 2866996353229492969826309)
    ·
      refine ⟨537561816230529931842433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2866996353229492969826309 537561816230529931842433)
      ·
        refine ⟨403171362172897448881825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 537561816230529931842433 403171362172897448881825)
        ·
          refine ⟨302378521629673086661369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 403171362172897448881825 302378521629673086661369)
          ·
            refine ⟨226783891222254814996027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302378521629673086661369 226783891222254814996027)
            ·
              refine ⟨340175836833382222494041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226783891222254814996027 340175836833382222494041)
              ·
                refine ⟨255131877625036666870531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340175836833382222494041 255131877625036666870531)
                ·
                  refine ⟨382697816437555000305797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255131877625036666870531 382697816437555000305797)
                  ·
                    refine ⟨71755840582041562557337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 382697816437555000305797 71755840582041562557337)
                    ·
                      refine ⟨53816880436531171918003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71755840582041562557337 53816880436531171918003)
                      ·
                        rfl

theorem cell23_104808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_104808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104808 prefixEnd_104808 := by exact prefixLift 104808
  have htrace : WordTrace (prefixWord ++ tailWord_104808) baseStart_104808 baseEnd_104808 := by
    simpa [prefixWord, tailWord_104808, baseEnd_104808] using wordTrace_append hprefix tailTrace_104808
  have hstable : (prefixWord ++ tailWord_104808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104808).length < 2 ^ (prefixWord ++ tailWord_104808).sum := by decide
  have hdescent : baseEnd_104808 < baseStart_104808 := by decide
  rcases family_descends (prefixWord ++ tailWord_104808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104841 : List Nat := [1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 3]
def baseStart_104841 : Nat := 118140960795 + 104841 * 2 ^ 59
def prefixEnd_104841 : Nat := 4983230072969 + 3 ^ 40 * 104841 * 2
def baseEnd_104841 : Nat := 53833825298129542805351

theorem tailTrace_104841 : CollatzResearch.WordTrace tailWord_104841 prefixEnd_104841 53833825298129542805351 := by
  unfold tailWord_104841
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823865413186437262386377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2549243608790958174924251 3823865413186437262386377)
  ·
    refine ⟨2867899059889827946789783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3823865413186437262386377 2867899059889827946789783)
    ·
      refine ⟨4301848589834741920184675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2867899059889827946789783 4301848589834741920184675)
      ·
        refine ⟨6452772884752112880277013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301848589834741920184675 6452772884752112880277013)
        ·
          refine ⟨302473728972755291262985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6452772884752112880277013 302473728972755291262985)
          ·
            refine ⟨226855296729566468447239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 302473728972755291262985 226855296729566468447239)
            ·
              refine ⟨340282945094349702670859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226855296729566468447239 340282945094349702670859)
              ·
                refine ⟨510424417641524554006289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340282945094349702670859 510424417641524554006289)
                ·
                  refine ⟨382818313231143415504717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510424417641524554006289 382818313231143415504717)
                  ·
                    refine ⟨143556867461678780814269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382818313231143415504717 143556867461678780814269)
                    ·
                      refine ⟨53833825298129542805351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 143556867461678780814269 53833825298129542805351)
                      ·
                        rfl

theorem cell23_104841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 3, 3].length) (baseStart_104841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104841 prefixEnd_104841 := by exact prefixLift 104841
  have htrace : WordTrace (prefixWord ++ tailWord_104841) baseStart_104841 baseEnd_104841 := by
    simpa [prefixWord, tailWord_104841, baseEnd_104841] using wordTrace_append hprefix tailTrace_104841
  have hstable : (prefixWord ++ tailWord_104841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104841).length < 2 ^ (prefixWord ++ tailWord_104841).sum := by decide
  have hdescent : baseEnd_104841 < baseStart_104841 := by decide
  rcases family_descends (prefixWord ++ tailWord_104841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104861 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 1, 7]
def baseStart_104861 : Nat := 118140960795 + 104861 * 2 ^ 59
def prefixEnd_104861 : Nat := 4983230072969 + 3 ^ 40 * 104861 * 2
def baseEnd_104861 : Nat := 17948031637073154851753

theorem tailTrace_104861 : CollatzResearch.WordTrace tailWord_104861 prefixEnd_104861 17948031637073154851753 := by
  unfold tailWord_104861
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824594873113980678114437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2549729915409320452076291 3824594873113980678114437)
  ·
    refine ⟨717111538708871377146457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3824594873113980678114437 717111538708871377146457)
    ·
      refine ⟨537833654031653532859843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717111538708871377146457 537833654031653532859843)
      ·
        refine ⟨806750481047480299289765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 537833654031653532859843 806750481047480299289765)
        ·
          refine ⟨151265715196402556116831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 806750481047480299289765 151265715196402556116831)
          ·
            refine ⟨226898572794603834175247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151265715196402556116831 226898572794603834175247)
            ·
              refine ⟨340347859191905751262871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226898572794603834175247 340347859191905751262871)
              ·
                refine ⟨510521788787858626894307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340347859191905751262871 510521788787858626894307)
                ·
                  refine ⟨765782683181787940341461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510521788787858626894307 765782683181787940341461)
                  ·
                    refine ⟨17948031637073154851753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 765782683181787940341461 17948031637073154851753)
                    ·
                      rfl

theorem cell23_104861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_104861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104861 prefixEnd_104861 := by exact prefixLift 104861
  have htrace : WordTrace (prefixWord ++ tailWord_104861) baseStart_104861 baseEnd_104861 := by
    simpa [prefixWord, tailWord_104861, baseEnd_104861] using wordTrace_append hprefix tailTrace_104861
  have hstable : (prefixWord ++ tailWord_104861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104861).length < 2 ^ (prefixWord ++ tailWord_104861).sum := by decide
  have hdescent : baseEnd_104861 < baseStart_104861 := by decide
  rcases family_descends (prefixWord ++ tailWord_104861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104865 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 5]
def baseStart_104865 : Nat := 118140960795 + 104865 * 2 ^ 59
def prefixEnd_104865 : Nat := 4983230072969 + 3 ^ 40 * 104865 * 2
def baseEnd_104865 : Nat := 5982905425981938767249

theorem tailTrace_104865 : CollatzResearch.WordTrace tailWord_104865 prefixEnd_104865 5982905425981938767249 := by
  unfold tailWord_104865
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824740765099489361260049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2549827176732992907506699 3824740765099489361260049)
  ·
    refine ⟨2868555573824617020945037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3824740765099489361260049 2868555573824617020945037)
    ·
      refine ⟨1075708340184231382854389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2868555573824617020945037 1075708340184231382854389)
      ·
        refine ⟨100847656892271692142599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1075708340184231382854389 100847656892271692142599)
        ·
          refine ⟨151271485338407538213899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100847656892271692142599 151271485338407538213899)
          ·
            refine ⟨226907228007611307320849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151271485338407538213899 226907228007611307320849)
            ·
              refine ⟨170180421005708480490637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226907228007611307320849 170180421005708480490637)
              ·
                refine ⟨63817657877140680183989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 170180421005708480490637 63817657877140680183989)
                ·
                  refine ⟨5982905425981938767249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63817657877140680183989 5982905425981938767249)
                  ·
                    rfl

theorem cell23_104865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 5].length) (baseStart_104865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104865 prefixEnd_104865 := by exact prefixLift 104865
  have htrace : WordTrace (prefixWord ++ tailWord_104865) baseStart_104865 baseEnd_104865 := by
    simpa [prefixWord, tailWord_104865, baseEnd_104865] using wordTrace_append hprefix tailTrace_104865
  have hstable : (prefixWord ++ tailWord_104865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104865).length < 2 ^ (prefixWord ++ tailWord_104865).sum := by decide
  have hdescent : baseEnd_104865 < baseStart_104865 := by decide
  rcases family_descends (prefixWord ++ tailWord_104865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104918 : List Nat := [5, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3]
def baseStart_104918 : Nat := 118140960795 + 104918 * 2 ^ 59
def prefixEnd_104918 : Nat := 4983230072969 + 3 ^ 40 * 104918 * 2
def baseEnd_104918 : Nat := 53873363308525741542497

theorem tailTrace_104918 : CollatzResearch.WordTrace tailWord_104918 prefixEnd_104918 53873363308525741542497 := by
  unfold tailWord_104918
  simp only [CollatzResearch.WordTrace]
  refine ⟨239167114619217463308713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2551115889271652941959605 239167114619217463308713)
  ·
    refine ⟨179375335964413097481535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 239167114619217463308713 179375335964413097481535)
    ·
      refine ⟨269063003946619646222303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179375335964413097481535 269063003946619646222303)
      ·
        refine ⟨403594505919929469333455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 269063003946619646222303 403594505919929469333455)
        ·
          refine ⟨605391758879894204000183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403594505919929469333455 605391758879894204000183)
          ·
            refine ⟨908087638319841306000275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605391758879894204000183 908087638319841306000275)
            ·
              refine ⟨1362131457479761959000413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908087638319841306000275 1362131457479761959000413)
              ·
                refine ⟨510799296554910734625155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1362131457479761959000413 510799296554910734625155)
                ·
                  refine ⟨766198944832366101937733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 510799296554910734625155 766198944832366101937733)
                  ·
                    refine ⟨143662302156068644113325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 766198944832366101937733 143662302156068644113325)
                    ·
                      refine ⟨53873363308525741542497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 143662302156068644113325 53873363308525741542497)
                      ·
                        rfl

theorem cell23_104918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_104918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104918 prefixEnd_104918 := by exact prefixLift 104918
  have htrace : WordTrace (prefixWord ++ tailWord_104918) baseStart_104918 baseEnd_104918 := by
    simpa [prefixWord, tailWord_104918, baseEnd_104918] using wordTrace_append hprefix tailTrace_104918
  have hstable : (prefixWord ++ tailWord_104918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104918).length < 2 ^ (prefixWord ++ tailWord_104918).sum := by decide
  have hdescent : baseEnd_104918 < baseStart_104918 := by decide
  rcases family_descends (prefixWord ++ tailWord_104918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104942 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_104942 : Nat := 118140960795 + 104942 * 2 ^ 59
def prefixEnd_104942 : Nat := 4983230072969 + 3 ^ 40 * 104942 * 2
def baseEnd_104942 : Nat := 17961895614744549214129

theorem tailTrace_104942 : CollatzResearch.WordTrace tailWord_104942 prefixEnd_104942 17961895614744549214129 := by
  unfold tailWord_104942
  simp only [CollatzResearch.WordTrace]
  refine ⟨478443648227566438976635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2551699457213687674542053 478443648227566438976635)
  ·
    refine ⟨717665472341349658464953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478443648227566438976635 717665472341349658464953)
    ·
      refine ⟨538249104256012243848715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 717665472341349658464953 538249104256012243848715)
      ·
        refine ⟨807373656384018365773073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 538249104256012243848715 807373656384018365773073)
        ·
          refine ⟨605530242288013774329805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807373656384018365773073 605530242288013774329805)
          ·
            refine ⟨227073840858005165373677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 605530242288013774329805 227073840858005165373677)
            ·
              refine ⟨85152690321751937015129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227073840858005165373677 85152690321751937015129)
              ·
                refine ⟨63864517741313952761347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85152690321751937015129 63864517741313952761347)
                ·
                  refine ⟨95796776611970929142021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63864517741313952761347 95796776611970929142021)
                  ·
                    refine ⟨17961895614744549214129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95796776611970929142021 17961895614744549214129)
                    ·
                      rfl

theorem cell23_104942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_104942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104942 prefixEnd_104942 := by exact prefixLift 104942
  have htrace : WordTrace (prefixWord ++ tailWord_104942) baseStart_104942 baseEnd_104942 := by
    simpa [prefixWord, tailWord_104942, baseEnd_104942] using wordTrace_append hprefix tailTrace_104942
  have hstable : (prefixWord ++ tailWord_104942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104942).length < 2 ^ (prefixWord ++ tailWord_104942).sum := by decide
  have hdescent : baseEnd_104942 < baseStart_104942 := by decide
  rcases family_descends (prefixWord ++ tailWord_104942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_104981 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 1, 6]
def baseStart_104981 : Nat := 118140960795 + 104981 * 2 ^ 59
def prefixEnd_104981 : Nat := 4983230072969 + 3 ^ 40 * 104981 * 2
def baseEnd_104981 : Nat := 17968570863252998351569

theorem tailTrace_104981 : CollatzResearch.WordTrace tailWord_104981 prefixEnd_104981 17968570863252998351569 := by
  unfold tailWord_104981
  simp only [CollatzResearch.WordTrace]
  refine ⟨3828971632679241172482797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2552647755119494114988531 3828971632679241172482797)
  ·
    refine ⟨1435864362254715439681049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3828971632679241172482797 1435864362254715439681049)
    ·
      refine ⟨1076898271691036579760787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1435864362254715439681049 1076898271691036579760787)
      ·
        refine ⟨1615347407536554869641181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076898271691036579760787 1615347407536554869641181)
        ·
          refine ⟨605755277826208076115443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1615347407536554869641181 605755277826208076115443)
          ·
            refine ⟨908632916739312114173165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605755277826208076115443 908632916739312114173165)
            ·
              refine ⟨340737343777242042814937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908632916739312114173165 340737343777242042814937)
              ·
                refine ⟨255553007832931532111203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340737343777242042814937 255553007832931532111203)
                ·
                  refine ⟨383329511749397298166805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255553007832931532111203 383329511749397298166805)
                  ·
                    refine ⟨17968570863252998351569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 383329511749397298166805 17968570863252998351569)
                    ·
                      rfl

theorem cell23_104981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_104981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_104981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_104981 prefixEnd_104981 := by exact prefixLift 104981
  have htrace : WordTrace (prefixWord ++ tailWord_104981) baseStart_104981 baseEnd_104981 := by
    simpa [prefixWord, tailWord_104981, baseEnd_104981] using wordTrace_append hprefix tailTrace_104981
  have hstable : (prefixWord ++ tailWord_104981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_104981).length < 2 ^ (prefixWord ++ tailWord_104981).sum := by decide
  have hdescent : baseEnd_104981 < baseStart_104981 := by decide
  rcases family_descends (prefixWord ++ tailWord_104981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105018 : List Nat := [3, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4]
def baseStart_105018 : Nat := 118140960795 + 105018 * 2 ^ 59
def prefixEnd_105018 : Nat := 4983230072969 + 3 ^ 40 * 105018 * 2
def baseEnd_105018 : Nat := 53924711373975350292037

theorem tailTrace_105018 : CollatzResearch.WordTrace tailWord_105018 prefixEnd_105018 53924711373975350292037 := by
  unfold tailWord_105018
  simp only [CollatzResearch.WordTrace]
  refine ⟨957580283386299122894927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2553547422363464327719805 957580283386299122894927)
  ·
    refine ⟨1436370425079448684342391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 957580283386299122894927 1436370425079448684342391)
    ·
      refine ⟨2154555637619173026513587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436370425079448684342391 2154555637619173026513587)
      ·
        refine ⟨3231833456428759539770381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154555637619173026513587 3231833456428759539770381)
        ·
          refine ⟨1211937546160784827413893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3231833456428759539770381 1211937546160784827413893)
          ·
            refine ⟨227238289905147155140105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1211937546160784827413893 227238289905147155140105)
            ·
              refine ⟨170428717428860366355079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 227238289905147155140105 170428717428860366355079)
              ·
                refine ⟨255643076143290549532619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170428717428860366355079 255643076143290549532619)
                ·
                  refine ⟨383464614214935824298929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255643076143290549532619 383464614214935824298929)
                  ·
                    refine ⟨287598460661201868224197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 383464614214935824298929 287598460661201868224197)
                    ·
                      refine ⟨53924711373975350292037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 287598460661201868224197 53924711373975350292037)
                      ·
                        rfl

theorem cell23_105018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_105018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105018 prefixEnd_105018 := by exact prefixLift 105018
  have htrace : WordTrace (prefixWord ++ tailWord_105018) baseStart_105018 baseEnd_105018 := by
    simpa [prefixWord, tailWord_105018, baseEnd_105018] using wordTrace_append hprefix tailTrace_105018
  have hstable : (prefixWord ++ tailWord_105018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105018).length < 2 ^ (prefixWord ++ tailWord_105018).sum := by decide
  have hdescent : baseEnd_105018 < baseStart_105018 := by decide
  rcases family_descends (prefixWord ++ tailWord_105018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105038 : List Nat := [4, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_105038 : Nat := 118140960795 + 105038 * 2 ^ 59
def prefixEnd_105038 : Nat := 4983230072969 + 3 ^ 40 * 105038 * 2
def baseEnd_105038 : Nat := 53934980987065272041945

theorem tailTrace_105038 : CollatzResearch.WordTrace tailWord_105038 prefixEnd_105038 53934980987065272041945 := by
  unfold tailWord_105038
  simp only [CollatzResearch.WordTrace]
  refine ⟨478881324184092488413471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2554033728981826604871845 478881324184092488413471)
  ·
    refine ⟨718321986276138732620207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 478881324184092488413471 718321986276138732620207)
    ·
      refine ⟨1077482979414208098930311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 718321986276138732620207 1077482979414208098930311)
      ·
        refine ⟨1616224469121312148395467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077482979414208098930311 1616224469121312148395467)
        ·
          refine ⟨2424336703681968222593201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616224469121312148395467 2424336703681968222593201)
          ·
            refine ⟨1818252527761476166944901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424336703681968222593201 1818252527761476166944901)
            ·
              refine ⟨340922348955276781302169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1818252527761476166944901 340922348955276781302169)
              ·
                refine ⟨255691761716457585976627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340922348955276781302169 255691761716457585976627)
                ·
                  refine ⟨383537642574686378964941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255691761716457585976627 383537642574686378964941)
                  ·
                    refine ⟨143826615965507392111853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383537642574686378964941 143826615965507392111853)
                    ·
                      refine ⟨53934980987065272041945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 143826615965507392111853 53934980987065272041945)
                      ·
                        rfl

theorem cell23_105038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_105038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105038 prefixEnd_105038 := by exact prefixLift 105038
  have htrace : WordTrace (prefixWord ++ tailWord_105038) baseStart_105038 baseEnd_105038 := by
    simpa [prefixWord, tailWord_105038, baseEnd_105038] using wordTrace_append hprefix tailTrace_105038
  have hstable : (prefixWord ++ tailWord_105038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105038).length < 2 ^ (prefixWord ++ tailWord_105038).sum := by decide
  have hdescent : baseEnd_105038 < baseStart_105038 := by decide
  rcases family_descends (prefixWord ++ tailWord_105038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105071 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 2, 6]
def baseStart_105071 : Nat := 118140960795 + 105071 * 2 ^ 59
def prefixEnd_105071 : Nat := 4983230072969 + 3 ^ 40 * 105071 * 2
def baseEnd_105071 : Nat := 17983975282887880976431

theorem tailTrace_105071 : CollatzResearch.WordTrace tailWord_105071 prefixEnd_105071 17983975282887880976431 := by
  unfold tailWord_105071
  simp only [CollatzResearch.WordTrace]
  refine ⟨3832254202353186543259067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2554836134902124362172711 3832254202353186543259067)
  ·
    refine ⟨5748381303529779814888601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3832254202353186543259067 5748381303529779814888601)
    ·
      refine ⟨4311285977647334861166451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5748381303529779814888601 4311285977647334861166451)
      ·
        refine ⟨6466928966471002291749677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311285977647334861166451 6466928966471002291749677)
        ·
          refine ⟨2425098362426625859406129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6466928966471002291749677 2425098362426625859406129)
          ·
            refine ⟨1818823771819969394554597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425098362426625859406129 1818823771819969394554597)
            ·
              refine ⟨341029457216244261478987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1818823771819969394554597 341029457216244261478987)
              ·
                refine ⟨511544185824366392218481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341029457216244261478987 511544185824366392218481)
                ·
                  refine ⟨383658139368274794163861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511544185824366392218481 383658139368274794163861)
                  ·
                    refine ⟨17983975282887880976431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 383658139368274794163861 17983975282887880976431)
                    ·
                      rfl

theorem cell23_105071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_105071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105071 prefixEnd_105071 := by exact prefixLift 105071
  have htrace : WordTrace (prefixWord ++ tailWord_105071) baseStart_105071 baseEnd_105071 := by
    simpa [prefixWord, tailWord_105071, baseEnd_105071] using wordTrace_append hprefix tailTrace_105071
  have hstable : (prefixWord ++ tailWord_105071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105071).length < 2 ^ (prefixWord ++ tailWord_105071).sum := by decide
  have hdescent : baseEnd_105071 < baseStart_105071 := by decide
  rcases family_descends (prefixWord ++ tailWord_105071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105072 : List Nat := [2, 1, 1, 1, 8, 1, 1, 1, 1, 3, 3]
def baseStart_105072 : Nat := 118140960795 + 105072 * 2 ^ 59
def prefixEnd_105072 : Nat := 4983230072969 + 3 ^ 40 * 105072 * 2
def baseEnd_105072 : Nat := 53952439329318139016789

theorem tailTrace_105072 : CollatzResearch.WordTrace tailWord_105072 prefixEnd_105072 53952439329318139016789 := by
  unfold tailWord_105072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916145337674781857022735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2554860450233042476030313 1916145337674781857022735)
  ·
    refine ⟨2874218006512172785534103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1916145337674781857022735 2874218006512172785534103)
    ·
      refine ⟨4311327009768259178301155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874218006512172785534103 4311327009768259178301155)
      ·
        refine ⟨6466990514652388767451733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311327009768259178301155 6466990514652388767451733)
        ·
          refine ⟨75785045093582680868575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 6466990514652388767451733 75785045093582680868575)
          ·
            refine ⟨113677567640374021302863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75785045093582680868575 113677567640374021302863)
            ·
              refine ⟨170516351460561031954295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113677567640374021302863 170516351460561031954295)
              ·
                refine ⟨255774527190841547931443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170516351460561031954295 255774527190841547931443)
                ·
                  refine ⟨383661790786262321897165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255774527190841547931443 383661790786262321897165)
                  ·
                    refine ⟨143873171544848370711437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383661790786262321897165 143873171544848370711437)
                    ·
                      refine ⟨53952439329318139016789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 143873171544848370711437 53952439329318139016789)
                      ·
                        rfl

theorem cell23_105072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 1, 1, 3, 3].length) (baseStart_105072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105072 prefixEnd_105072 := by exact prefixLift 105072
  have htrace : WordTrace (prefixWord ++ tailWord_105072) baseStart_105072 baseEnd_105072 := by
    simpa [prefixWord, tailWord_105072, baseEnd_105072] using wordTrace_append hprefix tailTrace_105072
  have hstable : (prefixWord ++ tailWord_105072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105072).length < 2 ^ (prefixWord ++ tailWord_105072).sum := by decide
  have hdescent : baseEnd_105072 < baseStart_105072 := by decide
  rcases family_descends (prefixWord ++ tailWord_105072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105091 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4]
def baseStart_105091 : Nat := 118140960795 + 105091 * 2 ^ 59
def prefixEnd_105091 : Nat := 4983230072969 + 3 ^ 40 * 105091 * 2
def baseEnd_105091 : Nat := 53962195461753564679201

theorem tailTrace_105091 : CollatzResearch.WordTrace tailWord_105091 prefixEnd_105091 53962195461753564679201 := by
  unfold tailWord_105091
  simp only [CollatzResearch.WordTrace]
  refine ⟨3832983662280729958987127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2555322441520486639324751 3832983662280729958987127)
  ·
    refine ⟨5749475493421094938480691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3832983662280729958987127 5749475493421094938480691)
    ·
      refine ⟨8624213240131642407721037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749475493421094938480691 8624213240131642407721037)
      ·
        refine ⟨3234079965049365902895389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8624213240131642407721037 3234079965049365902895389)
        ·
          refine ⟨1212779986893512213585771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3234079965049365902895389 1212779986893512213585771)
          ·
            refine ⟨1819169980340268320378657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212779986893512213585771 1819169980340268320378657)
            ·
              refine ⟨1364377485255201240283993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819169980340268320378657 1364377485255201240283993)
              ·
                refine ⟨1023283113941400930212995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364377485255201240283993 1023283113941400930212995)
                ·
                  refine ⟨1534924670912101395319493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1023283113941400930212995 1534924670912101395319493)
                  ·
                    refine ⟨287798375796019011622405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1534924670912101395319493 287798375796019011622405)
                    ·
                      refine ⟨53962195461753564679201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 287798375796019011622405 53962195461753564679201)
                      ·
                        rfl

theorem cell23_105091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_105091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105091 prefixEnd_105091 := by exact prefixLift 105091
  have htrace : WordTrace (prefixWord ++ tailWord_105091) baseStart_105091 baseEnd_105091 := by
    simpa [prefixWord, tailWord_105091, baseEnd_105091] using wordTrace_append hprefix tailTrace_105091
  have hstable : (prefixWord ++ tailWord_105091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105091).length < 2 ^ (prefixWord ++ tailWord_105091).sum := by decide
  have hdescent : baseEnd_105091 < baseStart_105091 := by decide
  rcases family_descends (prefixWord ++ tailWord_105091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105095 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 6, 2, 2]
def baseStart_105095 : Nat := 118140960795 + 105095 * 2 ^ 59
def prefixEnd_105095 : Nat := 4983230072969 + 3 ^ 40 * 105095 * 2
def baseEnd_105095 : Nat := 53964249384371549029183

theorem tailTrace_105095 : CollatzResearch.WordTrace tailWord_105095 prefixEnd_105095 53964249384371549029183 := by
  unfold tailWord_105095
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833129554266238642132739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2555419702844159094755159 3833129554266238642132739)
  ·
    refine ⟨5749694331399357963199109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3833129554266238642132739 5749694331399357963199109)
    ·
      refine ⟨1078067687137379618099833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5749694331399357963199109 1078067687137379618099833)
      ·
        refine ⟨808550765353034713574875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1078067687137379618099833 808550765353034713574875)
        ·
          refine ⟨1212826148029552070362313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 808550765353034713574875 1212826148029552070362313)
          ·
            refine ⟨909619611022164052771735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1212826148029552070362313 909619611022164052771735)
            ·
              refine ⟨1364429416533246079157603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909619611022164052771735 1364429416533246079157603)
              ·
                refine ⟨2046644124799869118736405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364429416533246079157603 2046644124799869118736405)
                ·
                  refine ⟨95936443349993864940769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2046644124799869118736405 95936443349993864940769)
                  ·
                    refine ⟨71952332512495398705577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95936443349993864940769 71952332512495398705577)
                    ·
                      refine ⟨53964249384371549029183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71952332512495398705577 53964249384371549029183)
                      ·
                        rfl

theorem cell23_105095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 2, 2].length) (baseStart_105095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105095 prefixEnd_105095 := by exact prefixLift 105095
  have htrace : WordTrace (prefixWord ++ tailWord_105095) baseStart_105095 baseEnd_105095 := by
    simpa [prefixWord, tailWord_105095, baseEnd_105095] using wordTrace_append hprefix tailTrace_105095
  have hstable : (prefixWord ++ tailWord_105095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105095).length < 2 ^ (prefixWord ++ tailWord_105095).sum := by decide
  have hdescent : baseEnd_105095 < baseStart_105095 := by decide
  rcases family_descends (prefixWord ++ tailWord_105095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105111 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_105111 : Nat := 118140960795 + 105111 * 2 ^ 59
def prefixEnd_105111 : Nat := 4983230072969 + 3 ^ 40 * 105111 * 2
def baseEnd_105111 : Nat := 53972465074843486429109

theorem tailTrace_105111 : CollatzResearch.WordTrace tailWord_105111 prefixEnd_105111 53972465074843486429109 := by
  unfold tailWord_105111
  simp only [CollatzResearch.WordTrace]
  refine ⟨3833713122208273374715187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2555808748138848916476791 3833713122208273374715187)
  ·
    refine ⟨5750569683312410062072781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3833713122208273374715187 5750569683312410062072781)
    ·
      refine ⟨2156463631242153773277293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5750569683312410062072781 2156463631242153773277293)
      ·
        refine ⟨808673861715807664978985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2156463631242153773277293 808673861715807664978985)
        ·
          refine ⟨606505396286855748734239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808673861715807664978985 606505396286855748734239)
          ·
            refine ⟨909758094430283623101359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606505396286855748734239 909758094430283623101359)
            ·
              refine ⟨1364637141645425434652039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909758094430283623101359 1364637141645425434652039)
              ·
                refine ⟨2046955712468138151978059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364637141645425434652039 2046955712468138151978059)
                ·
                  refine ⟨3070433568702207227967089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046955712468138151978059 3070433568702207227967089)
                  ·
                    refine ⟨2302825176526655420975317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3070433568702207227967089 2302825176526655420975317)
                    ·
                      refine ⟨53972465074843486429109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2302825176526655420975317 53972465074843486429109)
                      ·
                        rfl

theorem cell23_105111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_105111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105111 prefixEnd_105111 := by exact prefixLift 105111
  have htrace : WordTrace (prefixWord ++ tailWord_105111) baseStart_105111 baseEnd_105111 := by
    simpa [prefixWord, tailWord_105111, baseEnd_105111] using wordTrace_append hprefix tailTrace_105111
  have hstable : (prefixWord ++ tailWord_105111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105111).length < 2 ^ (prefixWord ++ tailWord_105111).sum := by decide
  have hdescent : baseEnd_105111 < baseStart_105111 := by decide
  rcases family_descends (prefixWord ++ tailWord_105111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105112 : List Nat := [2, 1, 2, 4, 1, 1, 2, 4, 2, 2, 2]
def baseStart_105112 : Nat := 118140960795 + 105112 * 2 ^ 59
def prefixEnd_105112 : Nat := 4983230072969 + 3 ^ 40 * 105112 * 2
def baseEnd_105112 : Nat := 53972978555497982516605

theorem tailTrace_105112 : CollatzResearch.WordTrace tailWord_105112 prefixEnd_105112 53972978555497982516605 := by
  unfold tailWord_105112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1916874797602325272750795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2555833063469767030334393 1916874797602325272750795)
  ·
    refine ⟨2875312196403487909126193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1916874797602325272750795 2875312196403487909126193)
    ·
      refine ⟨2156484147302615931844645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2875312196403487909126193 2156484147302615931844645)
      ·
        refine ⟨404340777619240487220871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2156484147302615931844645 404340777619240487220871)
        ·
          refine ⟨606511166428860730831307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404340777619240487220871 606511166428860730831307)
          ·
            refine ⟨909766749643291096246961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606511166428860730831307 909766749643291096246961)
            ·
              refine ⟨682325062232468322185221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 909766749643291096246961 682325062232468322185221)
              ·
                refine ⟨127935949168587810409729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 682325062232468322185221 127935949168587810409729)
                ·
                  refine ⟨95951961876440857807297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 127935949168587810409729 95951961876440857807297)
                  ·
                    refine ⟨71963971407330643355473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95951961876440857807297 71963971407330643355473)
                    ·
                      refine ⟨53972978555497982516605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 71963971407330643355473 53972978555497982516605)
                      ·
                        rfl

theorem cell23_105112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_105112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105112 prefixEnd_105112 := by exact prefixLift 105112
  have htrace : WordTrace (prefixWord ++ tailWord_105112) baseStart_105112 baseEnd_105112 := by
    simpa [prefixWord, tailWord_105112, baseEnd_105112] using wordTrace_append hprefix tailTrace_105112
  have hstable : (prefixWord ++ tailWord_105112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105112).length < 2 ^ (prefixWord ++ tailWord_105112).sum := by decide
  have hdescent : baseEnd_105112 < baseStart_105112 := by decide
  rcases family_descends (prefixWord ++ tailWord_105112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105185 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_105185 : Nat := 118140960795 + 105185 * 2 ^ 59
def prefixEnd_105185 : Nat := 4983230072969 + 3 ^ 40 * 105185 * 2
def baseEnd_105185 : Nat := 54010462643276196903769

theorem tailTrace_105185 : CollatzResearch.WordTrace tailWord_105185 prefixEnd_105185 54010462643276196903769 := by
  unfold tailWord_105185
  simp only [CollatzResearch.WordTrace]
  refine ⟨3836412123940184012909009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2557608082626789341939339 3836412123940184012909009)
  ·
    refine ⟨2877309092955138009681757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3836412123940184012909009 2877309092955138009681757)
    ·
      refine ⟨1078990909858176753630659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2877309092955138009681757 1078990909858176753630659)
      ·
        refine ⟨1618486364787265130445989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078990909858176753630659 1618486364787265130445989)
        ·
          refine ⟨303466193397612211958623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1618486364787265130445989 303466193397612211958623)
          ·
            refine ⟨455199290096418317937935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 303466193397612211958623 455199290096418317937935)
            ·
              refine ⟨682798935144627476906903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455199290096418317937935 682798935144627476906903)
              ·
                refine ⟨1024198402716941215360355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682798935144627476906903 1024198402716941215360355)
                ·
                  refine ⟨1536297604075411823040533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024198402716941215360355 1536297604075411823040533)
                  ·
                    refine ⟨72013950191034929205025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1536297604075411823040533 72013950191034929205025)
                    ·
                      refine ⟨54010462643276196903769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72013950191034929205025 54010462643276196903769)
                      ·
                        rfl

theorem cell23_105185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_105185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105185 prefixEnd_105185 := by exact prefixLift 105185
  have htrace : WordTrace (prefixWord ++ tailWord_105185) baseStart_105185 baseEnd_105185 := by
    simpa [prefixWord, tailWord_105185, baseEnd_105185] using wordTrace_append hprefix tailTrace_105185
  have hstable : (prefixWord ++ tailWord_105185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105185).length < 2 ^ (prefixWord ++ tailWord_105185).sum := by decide
  have hdescent : baseEnd_105185 < baseStart_105185 := by decide
  rcases family_descends (prefixWord ++ tailWord_105185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105202 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 2, 1, 4]
def baseStart_105202 : Nat := 118140960795 + 105202 * 2 ^ 59
def prefixEnd_105202 : Nat := 4983230072969 + 3 ^ 40 * 105202 * 2
def baseEnd_105202 : Nat := 54019191814402630391191

theorem tailTrace_105202 : CollatzResearch.WordTrace tailWord_105202 prefixEnd_105202 54019191814402630391191 := by
  unfold tailWord_105202
  simp only [CollatzResearch.WordTrace]
  refine ⟨959258041219648979069465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2558021443252397277518573 959258041219648979069465)
  ·
    refine ⟨719443530914736734302099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 959258041219648979069465 719443530914736734302099)
    ·
      refine ⟨1079165296372105101453149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 719443530914736734302099 1079165296372105101453149)
      ·
        refine ⟨404686986139539413044931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1079165296372105101453149 404686986139539413044931)
        ·
          refine ⟨607030479209309119567397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 404686986139539413044931 607030479209309119567397)
          ·
            refine ⟨113818214851745459918887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 607030479209309119567397 113818214851745459918887)
            ·
              refine ⟨170727322277618189878331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113818214851745459918887 170727322277618189878331)
              ·
                refine ⟨256090983416427284817497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 170727322277618189878331 256090983416427284817497)
                ·
                  refine ⟨192068237562320463613123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 256090983416427284817497 192068237562320463613123)
                  ·
                    refine ⟨288102356343480695419685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192068237562320463613123 288102356343480695419685)
                    ·
                      refine ⟨54019191814402630391191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 288102356343480695419685 54019191814402630391191)
                      ·
                        rfl

theorem cell23_105202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_105202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105202 prefixEnd_105202 := by exact prefixLift 105202
  have htrace : WordTrace (prefixWord ++ tailWord_105202) baseStart_105202 baseEnd_105202 := by
    simpa [prefixWord, tailWord_105202, baseEnd_105202] using wordTrace_append hprefix tailTrace_105202
  have hstable : (prefixWord ++ tailWord_105202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105202).length < 2 ^ (prefixWord ++ tailWord_105202).sum := by decide
  have hdescent : baseEnd_105202 < baseStart_105202 := by decide
  rcases family_descends (prefixWord ++ tailWord_105202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105212 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 1, 4]
def baseStart_105212 : Nat := 118140960795 + 105212 * 2 ^ 59
def prefixEnd_105212 : Nat := 4983230072969 + 3 ^ 40 * 105212 * 2
def baseEnd_105212 : Nat := 18008108873649197088715

theorem tailTrace_105212 : CollatzResearch.WordTrace tailWord_105212 prefixEnd_105212 18008108873649197088715 := by
  unfold tailWord_105212
  simp only [CollatzResearch.WordTrace]
  refine ⟨1918698447421183812070945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2558264596561578416094593 1918698447421183812070945)
  ·
    refine ⟨1439023835565887859053209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1918698447421183812070945 1439023835565887859053209)
    ·
      refine ⟨1079267876674415894289907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1439023835565887859053209 1079267876674415894289907)
      ·
        refine ⟨1618901815011623841434861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1079267876674415894289907 1618901815011623841434861)
        ·
          refine ⟨607088180629358940538073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1618901815011623841434861 607088180629358940538073)
          ·
            refine ⟨455316135472019205403555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 607088180629358940538073 455316135472019205403555)
            ·
              refine ⟨682974203208028808105333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455316135472019205403555 682974203208028808105333)
              ·
                refine ⟨64028831550752700759875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 682974203208028808105333 64028831550752700759875)
                ·
                  refine ⟨96043247326129051139813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64028831550752700759875 96043247326129051139813)
                  ·
                    refine ⟨18008108873649197088715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96043247326129051139813 18008108873649197088715)
                    ·
                      rfl

theorem cell23_105212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_105212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105212 prefixEnd_105212 := by exact prefixLift 105212
  have htrace : WordTrace (prefixWord ++ tailWord_105212) baseStart_105212 baseEnd_105212 := by
    simpa [prefixWord, tailWord_105212, baseEnd_105212] using wordTrace_append hprefix tailTrace_105212
  have hstable : (prefixWord ++ tailWord_105212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105212).length < 2 ^ (prefixWord ++ tailWord_105212).sum := by decide
  have hdescent : baseEnd_105212 < baseStart_105212 := by decide
  rcases family_descends (prefixWord ++ tailWord_105212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105288 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_105288 : Nat := 118140960795 + 105288 * 2 ^ 59
def prefixEnd_105288 : Nat := 4983230072969 + 3 ^ 40 * 105288 * 2
def baseEnd_105288 : Nat := 54063351150689293915795

theorem tailTrace_105288 : CollatzResearch.WordTrace tailWord_105288 prefixEnd_105288 54063351150689293915795 := by
  unfold tailWord_105288
  simp only [CollatzResearch.WordTrace]
  refine ⟨1920084421283516301954259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2560112561711355069272345 1920084421283516301954259)
  ·
    refine ⟨2880126631925274452931389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1920084421283516301954259 2880126631925274452931389)
    ·
      refine ⟨1080047486971977919849271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2880126631925274452931389 1080047486971977919849271)
      ·
        refine ⟨1620071230457966879773907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1080047486971977919849271 1620071230457966879773907)
        ·
          refine ⟨2430106845686950319660861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620071230457966879773907 2430106845686950319660861)
          ·
            refine ⟨911290067132606369872823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2430106845686950319660861 911290067132606369872823)
            ·
              refine ⟨1366935100698909554809235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 911290067132606369872823 1366935100698909554809235)
              ·
                refine ⟨2050402651048364332213853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1366935100698909554809235 2050402651048364332213853)
                ·
                  refine ⟨768900994143136624580195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2050402651048364332213853 768900994143136624580195)
                  ·
                    refine ⟨1153351491214704936870293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 768900994143136624580195 1153351491214704936870293)
                    ·
                      refine ⟨54063351150689293915795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1153351491214704936870293 54063351150689293915795)
                      ·
                        rfl

theorem cell23_105288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_105288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105288 prefixEnd_105288 := by exact prefixLift 105288
  have htrace : WordTrace (prefixWord ++ tailWord_105288) baseStart_105288 baseEnd_105288 := by
    simpa [prefixWord, tailWord_105288, baseEnd_105288] using wordTrace_append hprefix tailTrace_105288
  have hstable : (prefixWord ++ tailWord_105288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105288).length < 2 ^ (prefixWord ++ tailWord_105288).sum := by decide
  have hdescent : baseEnd_105288 < baseStart_105288 := by decide
  rcases family_descends (prefixWord ++ tailWord_105288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105326 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_105326 : Nat := 118140960795 + 105326 * 2 ^ 59
def prefixEnd_105326 : Nat := 4983230072969 + 3 ^ 40 * 105326 * 2
def baseEnd_105326 : Nat := 54082863415560145240621

theorem tailTrace_105326 : CollatzResearch.WordTrace tailWord_105326 prefixEnd_105326 54082863415560145240621 := by
  unfold tailWord_105326
  simp only [CollatzResearch.WordTrace]
  refine ⟨480194352053670636723979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2561036544286243395861221 480194352053670636723979)
  ·
    refine ⟨720291528080505955085969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 480194352053670636723979 720291528080505955085969)
    ·
      refine ⟨540218646060379466314477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 720291528080505955085969 540218646060379466314477)
      ·
        refine ⟨202581992272642299867929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 540218646060379466314477 202581992272642299867929)
        ·
          refine ⟨151936494204481724900947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 202581992272642299867929 151936494204481724900947)
          ·
            refine ⟨227904741306722587351421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151936494204481724900947 227904741306722587351421)
            ·
              refine ⟨85464277990020970256783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227904741306722587351421 85464277990020970256783)
              ·
                refine ⟨128196416985031455385175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85464277990020970256783 128196416985031455385175)
                ·
                  refine ⟨192294625477547183077763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128196416985031455385175 192294625477547183077763)
                  ·
                    refine ⟨288441938216320774616645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192294625477547183077763 288441938216320774616645)
                    ·
                      refine ⟨54082863415560145240621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 288441938216320774616645 54082863415560145240621)
                      ·
                        rfl

theorem cell23_105326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_105326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105326 prefixEnd_105326 := by exact prefixLift 105326
  have htrace : WordTrace (prefixWord ++ tailWord_105326) baseStart_105326 baseEnd_105326 := by
    simpa [prefixWord, tailWord_105326, baseEnd_105326] using wordTrace_append hprefix tailTrace_105326
  have hstable : (prefixWord ++ tailWord_105326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105326).length < 2 ^ (prefixWord ++ tailWord_105326).sum := by decide
  have hdescent : baseEnd_105326 < baseStart_105326 := by decide
  rcases family_descends (prefixWord ++ tailWord_105326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105329 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 1, 2, 3]
def baseStart_105329 : Nat := 118140960795 + 105329 * 2 ^ 59
def prefixEnd_105329 : Nat := 4983230072969 + 3 ^ 40 * 105329 * 2
def baseEnd_105329 : Nat := 54084403857523633503107

theorem tailTrace_105329 : CollatzResearch.WordTrace tailWord_105329 prefixEnd_105329 54084403857523633503107 := by
  unfold tailWord_105329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3841664235418496606151041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2561109490278997737434027 3841664235418496606151041)
  ·
    refine ⟨2881248176563872454613281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3841664235418496606151041 2881248176563872454613281)
    ·
      refine ⟨2160936132422904340959961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2881248176563872454613281 2160936132422904340959961)
      ·
        refine ⟨1620702099317178255719971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2160936132422904340959961 1620702099317178255719971)
        ·
          refine ⟨2431053148975767383579957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620702099317178255719971 2431053148975767383579957)
          ·
            refine ⟨227911232716478192210621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2431053148975767383579957 227911232716478192210621)
            ·
              refine ⟨85466712268679322078983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227911232716478192210621 85466712268679322078983)
              ·
                refine ⟨128200068403018983118475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85466712268679322078983 128200068403018983118475)
                ·
                  refine ⟨192300102604528474677713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128200068403018983118475 192300102604528474677713)
                  ·
                    refine ⟨144225076953396356008285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 192300102604528474677713 144225076953396356008285)
                    ·
                      refine ⟨54084403857523633503107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 144225076953396356008285 54084403857523633503107)
                      ·
                        rfl

theorem cell23_105329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_105329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105329 prefixEnd_105329 := by exact prefixLift 105329
  have htrace : WordTrace (prefixWord ++ tailWord_105329) baseStart_105329 baseEnd_105329 := by
    simpa [prefixWord, tailWord_105329, baseEnd_105329] using wordTrace_append hprefix tailTrace_105329
  have hstable : (prefixWord ++ tailWord_105329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105329).length < 2 ^ (prefixWord ++ tailWord_105329).sum := by decide
  have hdescent : baseEnd_105329 < baseStart_105329 := by decide
  rcases family_descends (prefixWord ++ tailWord_105329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105366 : List Nat := [5, 3, 1, 1, 1, 2, 3, 7]
def baseStart_105366 : Nat := 118140960795 + 105366 * 2 ^ 59
def prefixEnd_105366 : Nat := 4983230072969 + 3 ^ 40 * 105366 * 2
def baseEnd_105366 : Nat := 2003829727471851434831

theorem tailTrace_105366 : CollatzResearch.WordTrace tailWord_105366 prefixEnd_105366 2003829727471851434831 := by
  unfold tailWord_105366
  simp only [CollatzResearch.WordTrace]
  refine ⟨240188358517778245327997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2562009157522967950165301 240188358517778245327997)
  ·
    refine ⟨90070634444166841997999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240188358517778245327997 90070634444166841997999)
    ·
      refine ⟨135105951666250262996999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90070634444166841997999 135105951666250262996999)
      ·
        refine ⟨202658927499375394495499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135105951666250262996999 202658927499375394495499)
        ·
          refine ⟨303988391249063091743249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 202658927499375394495499 303988391249063091743249)
          ·
            refine ⟨227991293436797318807437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 303988391249063091743249 227991293436797318807437)
            ·
              refine ⟨85496735038798994552789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 227991293436797318807437 85496735038798994552789)
              ·
                refine ⟨2003829727471851434831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85496735038798994552789 2003829727471851434831)
                ·
                  rfl

theorem cell23_105366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_105366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105366 prefixEnd_105366 := by exact prefixLift 105366
  have htrace : WordTrace (prefixWord ++ tailWord_105366) baseStart_105366 baseEnd_105366 := by
    simpa [prefixWord, tailWord_105366, baseEnd_105366] using wordTrace_append hprefix tailTrace_105366
  have hstable : (prefixWord ++ tailWord_105366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105366).length < 2 ^ (prefixWord ++ tailWord_105366).sum := by decide
  have hdescent : baseEnd_105366 < baseStart_105366 := by decide
  rcases family_descends (prefixWord ++ tailWord_105366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105393 : List Nat := [1, 2, 2, 4, 4, 1, 1, 2, 2, 1, 3]
def baseStart_105393 : Nat := 118140960795 + 105393 * 2 ^ 59
def prefixEnd_105393 : Nat := 4983230072969 + 3 ^ 40 * 105393 * 2
def baseEnd_105393 : Nat := 54117266619411383102813

theorem tailTrace_105393 : CollatzResearch.WordTrace tailWord_105393 prefixEnd_105393 54117266619411383102813 := by
  unfold tailWord_105393
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843998507186635536480833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2562665671457757024320555 3843998507186635536480833)
  ·
    refine ⟨2882998880389976652360625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3843998507186635536480833 2882998880389976652360625)
    ·
      refine ⟨2162249160292482489270469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2882998880389976652360625 2162249160292482489270469)
      ·
        refine ⟨405421717554840466738213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2162249160292482489270469 405421717554840466738213)
        ·
          refine ⟨76016572041532587513415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 405421717554840466738213 76016572041532587513415)
          ·
            refine ⟨114024858062298881270123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76016572041532587513415 114024858062298881270123)
            ·
              refine ⟨171037287093448321905185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114024858062298881270123 171037287093448321905185)
              ·
                refine ⟨128277965320086241428889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171037287093448321905185 128277965320086241428889)
                ·
                  refine ⟨96208473990064681071667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128277965320086241428889 96208473990064681071667)
                  ·
                    refine ⟨144312710985097021607501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96208473990064681071667 144312710985097021607501)
                    ·
                      refine ⟨54117266619411383102813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 144312710985097021607501 54117266619411383102813)
                      ·
                        rfl

theorem cell23_105393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_105393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105393 prefixEnd_105393 := by exact prefixLift 105393
  have htrace : WordTrace (prefixWord ++ tailWord_105393) baseStart_105393 baseEnd_105393 := by
    simpa [prefixWord, tailWord_105393, baseEnd_105393] using wordTrace_append hprefix tailTrace_105393
  have hstable : (prefixWord ++ tailWord_105393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105393).length < 2 ^ (prefixWord ++ tailWord_105393).sum := by decide
  have hdescent : baseEnd_105393 < baseStart_105393 := by decide
  rcases family_descends (prefixWord ++ tailWord_105393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105416 : List Nat := [2, 1, 3, 1, 5, 2, 1, 1, 1, 4, 2]
def baseStart_105416 : Nat := 118140960795 + 105416 * 2 ^ 59
def prefixEnd_105416 : Nat := 4983230072969 + 3 ^ 40 * 105416 * 2
def baseEnd_105416 : Nat := 54129076674464793115207

theorem tailTrace_105416 : CollatzResearch.WordTrace tailWord_105416 prefixEnd_105416 54129076674464793115207 := by
  unfold tailWord_105416
  simp only [CollatzResearch.WordTrace]
  refine ⟨1922418693051655232284051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2563224924068873643045401 1922418693051655232284051)
  ·
    refine ⟨2883628039577482848426077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1922418693051655232284051 2883628039577482848426077)
    ·
      refine ⟨1081360514841556068159779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2883628039577482848426077 1081360514841556068159779)
      ·
        refine ⟨1622040772262334102239669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1081360514841556068159779 1622040772262334102239669)
        ·
          refine ⟨152066322399593822084969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1622040772262334102239669 152066322399593822084969)
          ·
            refine ⟨114049741799695366563727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152066322399593822084969 114049741799695366563727)
            ·
              refine ⟨171074612699543049845591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114049741799695366563727 171074612699543049845591)
              ·
                refine ⟨256611919049314574768387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171074612699543049845591 256611919049314574768387)
                ·
                  refine ⟨384917878573971862152581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 256611919049314574768387 384917878573971862152581)
                  ·
                    refine ⟨72172102232619724153609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 384917878573971862152581 72172102232619724153609)
                    ·
                      refine ⟨54129076674464793115207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72172102232619724153609 54129076674464793115207)
                      ·
                        rfl

theorem cell23_105416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 1, 1, 1, 4, 2].length) (baseStart_105416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105416 prefixEnd_105416 := by exact prefixLift 105416
  have htrace : WordTrace (prefixWord ++ tailWord_105416) baseStart_105416 baseEnd_105416 := by
    simpa [prefixWord, tailWord_105416, baseEnd_105416] using wordTrace_append hprefix tailTrace_105416
  have hstable : (prefixWord ++ tailWord_105416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105416).length < 2 ^ (prefixWord ++ tailWord_105416).sum := by decide
  have hdescent : baseEnd_105416 < baseStart_105416 := by decide
  rcases family_descends (prefixWord ++ tailWord_105416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105462 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_105462 : Nat := 118140960795 + 105462 * 2 ^ 59
def prefixEnd_105462 : Nat := 4983230072969 + 3 ^ 40 * 105462 * 2
def baseEnd_105462 : Nat := 54152696784571613139995

theorem tailTrace_105462 : CollatzResearch.WordTrace tailWord_105462 prefixEnd_105462 54152696784571613139995 := by
  unfold tailWord_105462
  simp only [CollatzResearch.WordTrace]
  refine ⟨240407196496041270046415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2564343429291106880495093 240407196496041270046415)
  ·
    refine ⟨360610794744061905069623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240407196496041270046415 360610794744061905069623)
    ·
      refine ⟨540916192116092857604435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 360610794744061905069623 540916192116092857604435)
      ·
        refine ⟨811374288174139286406653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 540916192116092857604435 811374288174139286406653)
        ·
          refine ⟨304265358065302232402495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 811374288174139286406653 304265358065302232402495)
          ·
            refine ⟨456398037097953348603743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304265358065302232402495 456398037097953348603743)
            ·
              refine ⟨684597055646930022905615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456398037097953348603743 684597055646930022905615)
              ·
                refine ⟨1026895583470395034358423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684597055646930022905615 1026895583470395034358423)
                ·
                  refine ⟨1540343375205592551537635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026895583470395034358423 1540343375205592551537635)
                  ·
                    refine ⟨2310515062808388827306453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1540343375205592551537635 2310515062808388827306453)
                    ·
                      refine ⟨54152696784571613139995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2310515062808388827306453 54152696784571613139995)
                      ·
                        rfl

theorem cell23_105462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_105462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105462 prefixEnd_105462 := by exact prefixLift 105462
  have htrace : WordTrace (prefixWord ++ tailWord_105462) baseStart_105462 baseEnd_105462 := by
    simpa [prefixWord, tailWord_105462, baseEnd_105462] using wordTrace_append hprefix tailTrace_105462
  have hstable : (prefixWord ++ tailWord_105462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105462).length < 2 ^ (prefixWord ++ tailWord_105462).sum := by decide
  have hdescent : baseEnd_105462 < baseStart_105462 := by decide
  rcases family_descends (prefixWord ++ tailWord_105462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105472 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 6, 4, 2]
def baseStart_105472 : Nat := 118140960795 + 105472 * 2 ^ 59
def prefixEnd_105472 : Nat := 4983230072969 + 3 ^ 40 * 105472 * 2
def baseEnd_105472 : Nat := 54157831591116574014949

theorem tailTrace_105472 : CollatzResearch.WordTrace tailWord_105472 prefixEnd_105472 54157831591116574014949 := by
  unfold tailWord_105472
  simp only [CollatzResearch.WordTrace]
  refine ⟨1923439936950216014303335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2564586582600288019071113 1923439936950216014303335)
  ·
    refine ⟨2885159905425324021455003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1923439936950216014303335 2885159905425324021455003)
    ·
      refine ⟨4327739858137986032182505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2885159905425324021455003 4327739858137986032182505)
      ·
        refine ⟨3245804893603489524136879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4327739858137986032182505 3245804893603489524136879)
        ·
          refine ⟨4868707340405234286205319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3245804893603489524136879 4868707340405234286205319)
          ·
            refine ⟨7303061010607851429307979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4868707340405234286205319 7303061010607851429307979)
            ·
              refine ⟨10954591515911777143961969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7303061010607851429307979 10954591515911777143961969)
              ·
                refine ⟨8215943636933832857971477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10954591515911777143961969 8215943636933832857971477)
                ·
                  refine ⟨385122357981273415217413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8215943636933832857971477 385122357981273415217413)
                  ·
                    refine ⟨72210442121488765353265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 385122357981273415217413 72210442121488765353265)
                    ·
                      refine ⟨54157831591116574014949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72210442121488765353265 54157831591116574014949)
                      ·
                        rfl

theorem cell23_105472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 6, 4, 2].length) (baseStart_105472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105472 prefixEnd_105472 := by exact prefixLift 105472
  have htrace : WordTrace (prefixWord ++ tailWord_105472) baseStart_105472 baseEnd_105472 := by
    simpa [prefixWord, tailWord_105472, baseEnd_105472] using wordTrace_append hprefix tailTrace_105472
  have hstable : (prefixWord ++ tailWord_105472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105472).length < 2 ^ (prefixWord ++ tailWord_105472).sum := by decide
  have hdescent : baseEnd_105472 < baseStart_105472 := by decide
  rcases family_descends (prefixWord ++ tailWord_105472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105515 : List Nat := [1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6]
def baseStart_105515 : Nat := 118140960795 + 105515 * 2 ^ 59
def prefixEnd_105515 : Nat := 4983230072969 + 3 ^ 40 * 105515 * 2
def baseEnd_105515 : Nat := 54179911259259905777251

theorem tailTrace_105515 : CollatzResearch.WordTrace tailWord_105515 prefixEnd_105515 54179911259259905777251 := by
  unfold tailWord_105515
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848448212744650372421999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2565632141829766914947999 3848448212744650372421999)
  ·
    refine ⟨5772672319116975558632999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3848448212744650372421999 5772672319116975558632999)
    ·
      refine ⟨8659008478675463337949499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772672319116975558632999 8659008478675463337949499)
      ·
        refine ⟨12988512718013195006924249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8659008478675463337949499 12988512718013195006924249)
        ·
          refine ⟨9741384538509896255193187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12988512718013195006924249 9741384538509896255193187)
          ·
            refine ⟨14612076807764844382789781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9741384538509896255193187 14612076807764844382789781)
            ·
              refine ⟨684941100363977080443271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14612076807764844382789781 684941100363977080443271)
              ·
                refine ⟨1027411650545965620664907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 684941100363977080443271 1027411650545965620664907)
                ·
                  refine ⟨1541117475818948430997361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027411650545965620664907 1541117475818948430997361)
                  ·
                    refine ⟨1155838106864211323248021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1541117475818948430997361 1155838106864211323248021)
                    ·
                      refine ⟨54179911259259905777251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1155838106864211323248021 54179911259259905777251)
                      ·
                        rfl

theorem cell23_105515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 6].length) (baseStart_105515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105515 prefixEnd_105515 := by exact prefixLift 105515
  have htrace : WordTrace (prefixWord ++ tailWord_105515) baseStart_105515 baseEnd_105515 := by
    simpa [prefixWord, tailWord_105515, baseEnd_105515] using wordTrace_append hprefix tailTrace_105515
  have hstable : (prefixWord ++ tailWord_105515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105515).length < 2 ^ (prefixWord ++ tailWord_105515).sum := by decide
  have hdescent : baseEnd_105515 < baseStart_105515 := by decide
  rcases family_descends (prefixWord ++ tailWord_105515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105535 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 7]
def baseStart_105535 : Nat := 118140960795 + 105535 * 2 ^ 59
def prefixEnd_105535 : Nat := 4983230072969 + 3 ^ 40 * 105535 * 2
def baseEnd_105535 : Nat := 54190180872349827527159

theorem tailTrace_105535 : CollatzResearch.WordTrace tailWord_105535 prefixEnd_105535 54190180872349827527159 := by
  unfold tailWord_105535
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849177672672193788150059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2566118448448129192100039 3849177672672193788150059)
  ·
    refine ⟨5773766509008290682225089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849177672672193788150059 5773766509008290682225089)
    ·
      refine ⟨4330324881756218011668817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5773766509008290682225089 4330324881756218011668817)
      ·
        refine ⟨3247743661317163508751613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4330324881756218011668817 3247743661317163508751613)
        ·
          refine ⟨1217903872993936315781855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3247743661317163508751613 1217903872993936315781855)
          ·
            refine ⟨1826855809490904473672783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217903872993936315781855 1826855809490904473672783)
            ·
              refine ⟨2740283714236356710509175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826855809490904473672783 2740283714236356710509175)
              ·
                refine ⟨4110425571354535065763763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740283714236356710509175 4110425571354535065763763)
                ·
                  refine ⟨6165638357031802598645645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110425571354535065763763 6165638357031802598645645)
                  ·
                    refine ⟨2312114383886925974492117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6165638357031802598645645 2312114383886925974492117)
                    ·
                      refine ⟨54190180872349827527159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 2312114383886925974492117 54190180872349827527159)
                      ·
                        rfl

theorem cell23_105535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_105535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105535 prefixEnd_105535 := by exact prefixLift 105535
  have htrace : WordTrace (prefixWord ++ tailWord_105535) baseStart_105535 baseEnd_105535 := by
    simpa [prefixWord, tailWord_105535, baseEnd_105535] using wordTrace_append hprefix tailTrace_105535
  have hstable : (prefixWord ++ tailWord_105535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105535).length < 2 ^ (prefixWord ++ tailWord_105535).sum := by decide
  have hdescent : baseEnd_105535 < baseStart_105535 := by decide
  rcases family_descends (prefixWord ++ tailWord_105535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105539 : List Nat := [1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 3]
def baseStart_105539 : Nat := 118140960795 + 105539 * 2 ^ 59
def prefixEnd_105539 : Nat := 4983230072969 + 3 ^ 40 * 105539 * 2
def baseEnd_105539 : Nat := 54192234794967811877141

theorem tailTrace_105539 : CollatzResearch.WordTrace tailWord_105539 prefixEnd_105539 54192234794967811877141 := by
  unfold tailWord_105539
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849323564657702471295671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2566215709771801647530447 3849323564657702471295671)
  ·
    refine ⟨5773985346986553706943507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849323564657702471295671 5773985346986553706943507)
    ·
      refine ⟨8660978020479830560415261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5773985346986553706943507 8660978020479830560415261)
      ·
        refine ⟨3247866757679936460155723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8660978020479830560415261 3247866757679936460155723)
        ·
          refine ⟨4871800136519904690233585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247866757679936460155723 4871800136519904690233585)
          ·
            refine ⟨3653850102389928517675189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4871800136519904690233585 3653850102389928517675189)
            ·
              refine ⟨342548447099055798532049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3653850102389928517675189 342548447099055798532049)
              ·
                refine ⟨256911335324291848899037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 342548447099055798532049 256911335324291848899037)
                ·
                  refine ⟨96341750746609443337139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 256911335324291848899037 96341750746609443337139)
                  ·
                    refine ⟨144512626119914165005709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96341750746609443337139 144512626119914165005709)
                    ·
                      refine ⟨54192234794967811877141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 144512626119914165005709 54192234794967811877141)
                      ·
                        rfl

theorem cell23_105539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_105539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105539 prefixEnd_105539 := by exact prefixLift 105539
  have htrace : WordTrace (prefixWord ++ tailWord_105539) baseStart_105539 baseEnd_105539 := by
    simpa [prefixWord, tailWord_105539, baseEnd_105539] using wordTrace_append hprefix tailTrace_105539
  have hstable : (prefixWord ++ tailWord_105539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105539).length < 2 ^ (prefixWord ++ tailWord_105539).sum := by decide
  have hdescent : baseEnd_105539 < baseStart_105539 := by decide
  rcases family_descends (prefixWord ++ tailWord_105539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105562 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_105562 : Nat := 118140960795 + 105562 * 2 ^ 59
def prefixEnd_105562 : Nat := 4983230072969 + 3 ^ 40 * 105562 * 2
def baseEnd_105562 : Nat := 54204044850021221889535

theorem tailTrace_105562 : CollatzResearch.WordTrace tailWord_105562 prefixEnd_105562 54204044850021221889535 := by
  unfold tailWord_105562
  simp only [CollatzResearch.WordTrace]
  refine ⟨962540610893594349845735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2566774962382918266255293 962540610893594349845735)
  ·
    refine ⟨1443810916340391524768603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 962540610893594349845735 1443810916340391524768603)
    ·
      refine ⟨2165716374510587287152905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1443810916340391524768603 2165716374510587287152905)
      ·
        refine ⟨1624287280882940465364679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2165716374510587287152905 1624287280882940465364679)
        ·
          refine ⟨2436430921324410698047019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624287280882940465364679 2436430921324410698047019)
          ·
            refine ⟨3654646381986616047070529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436430921324410698047019 3654646381986616047070529)
            ·
              refine ⟨2740984786489962035302897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3654646381986616047070529 2740984786489962035302897)
              ·
                refine ⟨2055738589867471526477173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740984786489962035302897 2055738589867471526477173)
                ·
                  refine ⟨192725492800075455607235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2055738589867471526477173 192725492800075455607235)
                  ·
                    refine ⟨289088239200113183410853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192725492800075455607235 289088239200113183410853)
                    ·
                      refine ⟨54204044850021221889535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 289088239200113183410853 54204044850021221889535)
                      ·
                        rfl

theorem cell23_105562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_105562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105562 prefixEnd_105562 := by exact prefixLift 105562
  have htrace : WordTrace (prefixWord ++ tailWord_105562) baseStart_105562 baseEnd_105562 := by
    simpa [prefixWord, tailWord_105562, baseEnd_105562] using wordTrace_append hprefix tailTrace_105562
  have hstable : (prefixWord ++ tailWord_105562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105562).length < 2 ^ (prefixWord ++ tailWord_105562).sum := by decide
  have hdescent : baseEnd_105562 < baseStart_105562 := by decide
  rcases family_descends (prefixWord ++ tailWord_105562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105566 : List Nat := [4, 4, 1, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_105566 : Nat := 118140960795 + 105566 * 2 ^ 59
def prefixEnd_105566 : Nat := 4983230072969 + 3 ^ 40 * 105566 * 2
def baseEnd_105566 : Nat := 54206098772639206239517

theorem tailTrace_105566 : CollatzResearch.WordTrace tailWord_105566 prefixEnd_105566 54206098772639206239517 := by
  unfold tailWord_105566
  simp only [CollatzResearch.WordTrace]
  refine ⟨481288541944985760316069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2566872223706590721685701 481288541944985760316069)
  ·
    refine ⟨90241601614684830059263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 481288541944985760316069 90241601614684830059263)
    ·
      refine ⟨135362402422027245088895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90241601614684830059263 135362402422027245088895)
      ·
        refine ⟨203043603633040867633343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135362402422027245088895 203043603633040867633343)
        ·
          refine ⟨304565405449561301450015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203043603633040867633343 304565405449561301450015)
          ·
            refine ⟨456848108174341952175023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304565405449561301450015 456848108174341952175023)
            ·
              refine ⟨685272162261512928262535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 456848108174341952175023 685272162261512928262535)
              ·
                refine ⟨1027908243392269392393803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685272162261512928262535 1027908243392269392393803)
                ·
                  refine ⟨1541862365088404088590705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027908243392269392393803 1541862365088404088590705)
                  ·
                    refine ⟨1156396773816303066443029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1541862365088404088590705 1156396773816303066443029)
                    ·
                      refine ⟨54206098772639206239517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1156396773816303066443029 54206098772639206239517)
                      ·
                        rfl

theorem cell23_105566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_105566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105566 prefixEnd_105566 := by exact prefixLift 105566
  have htrace : WordTrace (prefixWord ++ tailWord_105566) baseStart_105566 baseEnd_105566 := by
    simpa [prefixWord, tailWord_105566, baseEnd_105566] using wordTrace_append hprefix tailTrace_105566
  have hstable : (prefixWord ++ tailWord_105566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105566).length < 2 ^ (prefixWord ++ tailWord_105566).sum := by decide
  have hdescent : baseEnd_105566 < baseStart_105566 := by decide
  rcases family_descends (prefixWord ++ tailWord_105566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105596 : List Nat := [2, 2, 2, 1, 1, 3, 1, 4, 3, 2, 2]
def baseStart_105596 : Nat := 118140960795 + 105596 * 2 ^ 59
def prefixEnd_105596 : Nat := 4983230072969 + 3 ^ 40 * 105596 * 2
def baseEnd_105596 : Nat := 54221503192274088864379

theorem tailTrace_105596 : CollatzResearch.WordTrace tailWord_105596 prefixEnd_105596 54221503192274088864379 := by
  unfold tailWord_105596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925701262725600603060321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2567601683634134137413761 1925701262725600603060321)
  ·
    refine ⟨1444275947044200452295241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1925701262725600603060321 1444275947044200452295241)
    ·
      refine ⟨1083206960283150339221431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1444275947044200452295241 1083206960283150339221431)
      ·
        refine ⟨1624810440424725508832147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1083206960283150339221431 1624810440424725508832147)
        ·
          refine ⟨2437215660637088263248221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624810440424725508832147 2437215660637088263248221)
          ·
            refine ⟨913955872738908098718083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2437215660637088263248221 913955872738908098718083)
            ·
              refine ⟨1370933809108362148077125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913955872738908098718083 1370933809108362148077125)
              ·
                refine ⟨257050089207817902764461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1370933809108362148077125 257050089207817902764461)
                ·
                  refine ⟨96393783452931713536673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257050089207817902764461 96393783452931713536673)
                  ·
                    refine ⟨72295337589698785152505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96393783452931713536673 72295337589698785152505)
                    ·
                      refine ⟨54221503192274088864379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72295337589698785152505 54221503192274088864379)
                      ·
                        rfl

theorem cell23_105596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_105596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105596 prefixEnd_105596 := by exact prefixLift 105596
  have htrace : WordTrace (prefixWord ++ tailWord_105596) baseStart_105596 baseEnd_105596 := by
    simpa [prefixWord, tailWord_105596, baseEnd_105596] using wordTrace_append hprefix tailTrace_105596
  have hstable : (prefixWord ++ tailWord_105596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105596).length < 2 ^ (prefixWord ++ tailWord_105596).sum := by decide
  have hdescent : baseEnd_105596 < baseStart_105596 := by decide
  rcases family_descends (prefixWord ++ tailWord_105596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105630 : List Nat := [4, 3, 1, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_105630 : Nat := 118140960795 + 105630 * 2 ^ 59
def prefixEnd_105630 : Nat := 4983230072969 + 3 ^ 40 * 105630 * 2
def baseEnd_105630 : Nat := 54238961534526955839223

theorem tailTrace_105630 : CollatzResearch.WordTrace tailWord_105630 prefixEnd_105630 54238961534526955839223 := by
  unfold tailWord_105630
  simp only [CollatzResearch.WordTrace]
  refine ⟨481580325916003126607293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2568428404885350008572229 481580325916003126607293)
  ·
    refine ⟨180592622218501172477735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 481580325916003126607293 180592622218501172477735)
    ·
      refine ⟨270888933327751758716603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180592622218501172477735 270888933327751758716603)
      ·
        refine ⟨406333399991627638074905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270888933327751758716603 406333399991627638074905)
        ·
          refine ⟨304750049993720728556179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406333399991627638074905 304750049993720728556179)
          ·
            refine ⟨457125074990581092834269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304750049993720728556179 457125074990581092834269)
            ·
              refine ⟨171421903121467909812851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457125074990581092834269 171421903121467909812851)
              ·
                refine ⟨257132854682201864719277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171421903121467909812851 257132854682201864719277)
                ·
                  refine ⟨96424820505825699269729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257132854682201864719277 96424820505825699269729)
                  ·
                    refine ⟨72318615379369274452297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96424820505825699269729 72318615379369274452297)
                    ·
                      refine ⟨54238961534526955839223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72318615379369274452297 54238961534526955839223)
                      ·
                        rfl

theorem cell23_105630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_105630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105630 prefixEnd_105630 := by exact prefixLift 105630
  have htrace : WordTrace (prefixWord ++ tailWord_105630) baseStart_105630 baseEnd_105630 := by
    simpa [prefixWord, tailWord_105630, baseEnd_105630] using wordTrace_append hprefix tailTrace_105630
  have hstable : (prefixWord ++ tailWord_105630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105630).length < 2 ^ (prefixWord ++ tailWord_105630).sum := by decide
  have hdescent : baseEnd_105630 < baseStart_105630 := by decide
  rcases family_descends (prefixWord ++ tailWord_105630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105632 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_105632 : Nat := 118140960795 + 105632 * 2 ^ 59
def prefixEnd_105632 : Nat := 4983230072969 + 3 ^ 40 * 105632 * 2
def baseEnd_105632 : Nat := 18079996165278649338071

theorem tailTrace_105632 : CollatzResearch.WordTrace tailWord_105632 prefixEnd_105632 18079996165278649338071 := by
  unfold tailWord_105632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926357776660389677215575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2568477035547186236287433 1926357776660389677215575)
  ·
    refine ⟨2889536664990584515823363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926357776660389677215575 2889536664990584515823363)
    ·
      refine ⟨4334304997485876773735045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2889536664990584515823363 4334304997485876773735045)
      ·
        refine ⟨812682187028601895075321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4334304997485876773735045 812682187028601895075321)
        ·
          refine ⟨609511640271451421306491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812682187028601895075321 609511640271451421306491)
          ·
            refine ⟨914267460407177131959737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609511640271451421306491 914267460407177131959737)
            ·
              refine ⟨685700595305382848969803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 914267460407177131959737 685700595305382848969803)
              ·
                refine ⟨1028550892958074273454705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 685700595305382848969803 1028550892958074273454705)
                ·
                  refine ⟨771413169718555705091029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1028550892958074273454705 771413169718555705091029)
                  ·
                    refine ⟨18079996165278649338071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 771413169718555705091029 18079996165278649338071)
                    ·
                      rfl

theorem cell23_105632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_105632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105632 prefixEnd_105632 := by exact prefixLift 105632
  have htrace : WordTrace (prefixWord ++ tailWord_105632) baseStart_105632 baseEnd_105632 := by
    simpa [prefixWord, tailWord_105632, baseEnd_105632] using wordTrace_append hprefix tailTrace_105632
  have hstable : (prefixWord ++ tailWord_105632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105632).length < 2 ^ (prefixWord ++ tailWord_105632).sum := by decide
  have hdescent : baseEnd_105632 < baseStart_105632 := by decide
  rcases family_descends (prefixWord ++ tailWord_105632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105656 : List Nat := [2, 1, 2, 1, 2, 1, 2, 6, 1, 3, 2]
def baseStart_105656 : Nat := 118140960795 + 105656 * 2 ^ 59
def prefixEnd_105656 : Nat := 4983230072969 + 3 ^ 40 * 105656 * 2
def baseEnd_105656 : Nat := 54252312031543854114103

theorem tailTrace_105656 : CollatzResearch.WordTrace tailWord_105656 prefixEnd_105656 54252312031543854114103 := by
  unfold tailWord_105656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926795452616915726652411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2569060603489220968869881 1926795452616915726652411)
  ·
    refine ⟨2890193178925373589978617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926795452616915726652411 2890193178925373589978617)
    ·
      refine ⟨2167644884194030192483963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2890193178925373589978617 2167644884194030192483963)
      ·
        refine ⟨3251467326291045288725945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167644884194030192483963 3251467326291045288725945)
        ·
          refine ⟨2438600494718283966544459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3251467326291045288725945 2438600494718283966544459)
          ·
            refine ⟨3657900742077425949816689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438600494718283966544459 3657900742077425949816689)
            ·
              refine ⟨2743425556558069462362517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3657900742077425949816689 2743425556558069462362517)
              ·
                refine ⟨128598072963659506048243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2743425556558069462362517 128598072963659506048243)
                ·
                  refine ⟨192897109445489259072365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128598072963659506048243 192897109445489259072365)
                  ·
                    refine ⟨72336416042058472152137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192897109445489259072365 72336416042058472152137)
                    ·
                      refine ⟨54252312031543854114103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72336416042058472152137 54252312031543854114103)
                      ·
                        rfl

theorem cell23_105656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 1, 3, 2].length) (baseStart_105656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105656 prefixEnd_105656 := by exact prefixLift 105656
  have htrace : WordTrace (prefixWord ++ tailWord_105656) baseStart_105656 baseEnd_105656 := by
    simpa [prefixWord, tailWord_105656, baseEnd_105656] using wordTrace_append hprefix tailTrace_105656
  have hstable : (prefixWord ++ tailWord_105656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105656).length < 2 ^ (prefixWord ++ tailWord_105656).sum := by decide
  have hdescent : baseEnd_105656 < baseStart_105656 := by decide
  rcases family_descends (prefixWord ++ tailWord_105656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105709 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 9]
def baseStart_105709 : Nat := 118140960795 + 105709 * 2 ^ 59
def prefixEnd_105709 : Nat := 4983230072969 + 3 ^ 40 * 105709 * 2
def baseEnd_105709 : Nat := 6031058500692460750151

theorem tailTrace_105709 : CollatzResearch.WordTrace tailWord_105709 prefixEnd_105709 6031058500692460750151 := by
  unfold tailWord_105709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855523974041821504984181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2570349316027881003322787 3855523974041821504984181)
  ·
    refine ⟨361455372566420766092267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3855523974041821504984181 361455372566420766092267)
    ·
      refine ⟨542183058849631149138401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361455372566420766092267 542183058849631149138401)
      ·
        refine ⟨406637294137223361853801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542183058849631149138401 406637294137223361853801)
        ·
          refine ⟨304977970602917521390351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406637294137223361853801 304977970602917521390351)
          ·
            refine ⟨457466955904376282085527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304977970602917521390351 457466955904376282085527)
            ·
              refine ⟨686200433856564423128291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457466955904376282085527 686200433856564423128291)
              ·
                refine ⟨1029300650784846634692437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 686200433856564423128291 1029300650784846634692437)
                ·
                  refine ⟨6031058500692460750151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1029300650784846634692437 6031058500692460750151)
                  ·
                    rfl

theorem cell23_105709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_105709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105709 prefixEnd_105709 := by exact prefixLift 105709
  have htrace : WordTrace (prefixWord ++ tailWord_105709) baseStart_105709 baseEnd_105709 := by
    simpa [prefixWord, tailWord_105709, baseEnd_105709] using wordTrace_append hprefix tailTrace_105709
  have hstable : (prefixWord ++ tailWord_105709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105709).length < 2 ^ (prefixWord ++ tailWord_105709).sum := by decide
  have hdescent : baseEnd_105709 < baseStart_105709 := by decide
  rcases family_descends (prefixWord ++ tailWord_105709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105769 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 9, 4]
def baseStart_105769 : Nat := 118140960795 + 105769 * 2 ^ 59
def prefixEnd_105769 : Nat := 4983230072969 + 3 ^ 40 * 105769 * 2
def baseEnd_105769 : Nat := 18103445115167304000361

theorem tailTrace_105769 : CollatzResearch.WordTrace tailWord_105769 prefixEnd_105769 18103445115167304000361 := by
  unfold tailWord_105769
  simp only [CollatzResearch.WordTrace]
  refine ⟨3857712353824451752168361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2571808235882967834778907 3857712353824451752168361)
  ·
    refine ⟨2893284265368338814126271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3857712353824451752168361 2893284265368338814126271)
    ·
      refine ⟨4339926398052508221189407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2893284265368338814126271 4339926398052508221189407)
      ·
        refine ⟨6509889597078762331784111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4339926398052508221189407 6509889597078762331784111)
        ·
          refine ⟨9764834395618143497676167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6509889597078762331784111 9764834395618143497676167)
          ·
            refine ⟨14647251593427215246514251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9764834395618143497676167 14647251593427215246514251)
            ·
              refine ⟨21970877390140822869771377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14647251593427215246514251 21970877390140822869771377)
              ·
                refine ⟨16478158042605617152328533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21970877390140822869771377 16478158042605617152328533)
                ·
                  refine ⟨96551707280892288001925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16478158042605617152328533 96551707280892288001925)
                  ·
                    refine ⟨18103445115167304000361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96551707280892288001925 18103445115167304000361)
                    ·
                      rfl

theorem cell23_105769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_105769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105769 prefixEnd_105769 := by exact prefixLift 105769
  have htrace : WordTrace (prefixWord ++ tailWord_105769) baseStart_105769 baseEnd_105769 := by
    simpa [prefixWord, tailWord_105769, baseEnd_105769] using wordTrace_append hprefix tailTrace_105769
  have hstable : (prefixWord ++ tailWord_105769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105769).length < 2 ^ (prefixWord ++ tailWord_105769).sum := by decide
  have hdescent : baseEnd_105769 < baseStart_105769 := by decide
  rcases family_descends (prefixWord ++ tailWord_105769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105793 : List Nat := [1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_105793 : Nat := 118140960795 + 105793 * 2 ^ 59
def prefixEnd_105793 : Nat := 4983230072969 + 3 ^ 40 * 105793 * 2
def baseEnd_105793 : Nat := 54322658881209818100973

theorem tailTrace_105793 : CollatzResearch.WordTrace tailWord_105793 prefixEnd_105793 54322658881209818100973 := by
  unfold tailWord_105793
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858587705737503851042033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2572391803825002567361355 3858587705737503851042033)
  ·
    refine ⟨2893940779303127888281525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3858587705737503851042033 2893940779303127888281525)
    ·
      refine ⟨271306948059668239526393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2893940779303127888281525 271306948059668239526393)
      ·
        refine ⟨203480211044751179644795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271306948059668239526393 203480211044751179644795)
        ·
          refine ⟨305220316567126769467193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203480211044751179644795 305220316567126769467193)
          ·
            refine ⟨228915237425345077100395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305220316567126769467193 228915237425345077100395)
            ·
              refine ⟨343372856138017615650593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228915237425345077100395 343372856138017615650593)
              ·
                refine ⟨257529642103513211737945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 343372856138017615650593 257529642103513211737945)
                ·
                  refine ⟨193147231577634908803459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257529642103513211737945 193147231577634908803459)
                  ·
                    refine ⟨289720847366452363205189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 193147231577634908803459 289720847366452363205189)
                    ·
                      refine ⟨54322658881209818100973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 289720847366452363205189 54322658881209818100973)
                      ·
                        rfl

theorem cell23_105793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_105793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105793 prefixEnd_105793 := by exact prefixLift 105793
  have htrace : WordTrace (prefixWord ++ tailWord_105793) baseStart_105793 baseEnd_105793 := by
    simpa [prefixWord, tailWord_105793, baseEnd_105793] using wordTrace_append hprefix tailTrace_105793
  have hstable : (prefixWord ++ tailWord_105793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105793).length < 2 ^ (prefixWord ++ tailWord_105793).sum := by decide
  have hdescent : baseEnd_105793 < baseStart_105793 := by decide
  rcases family_descends (prefixWord ++ tailWord_105793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105799 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 8]
def baseStart_105799 : Nat := 118140960795 + 105799 * 2 ^ 59
def prefixEnd_105799 : Nat := 4983230072969 + 3 ^ 40 * 105799 * 2
def baseEnd_105799 : Nat := 6036193307237421625105

theorem tailTrace_105799 : CollatzResearch.WordTrace tailWord_105799 prefixEnd_105799 6036193307237421625105 := by
  unfold tailWord_105799
  simp only [CollatzResearch.WordTrace]
  refine ⟨3858806543715766875760451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2572537695810511250506967 3858806543715766875760451)
  ·
    refine ⟨5788209815573650313640677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3858806543715766875760451 5788209815573650313640677)
    ·
      refine ⟨1085289340420059433807627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5788209815573650313640677 1085289340420059433807627)
      ·
        refine ⟨1627934010630089150711441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085289340420059433807627 1627934010630089150711441)
        ·
          refine ⟨1220950507972566863033581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627934010630089150711441 1220950507972566863033581)
          ·
            refine ⟨457856440489712573637593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1220950507972566863033581 457856440489712573637593)
            ·
              refine ⟨343392330367284430228195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457856440489712573637593 343392330367284430228195)
              ·
                refine ⟨515088495550926645342293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343392330367284430228195 515088495550926645342293)
                ·
                  refine ⟨6036193307237421625105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 515088495550926645342293 6036193307237421625105)
                  ·
                    rfl

theorem cell23_105799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 8].length) (baseStart_105799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105799 prefixEnd_105799 := by exact prefixLift 105799
  have htrace : WordTrace (prefixWord ++ tailWord_105799) baseStart_105799 baseEnd_105799 := by
    simpa [prefixWord, tailWord_105799, baseEnd_105799] using wordTrace_append hprefix tailTrace_105799
  have hstable : (prefixWord ++ tailWord_105799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105799).length < 2 ^ (prefixWord ++ tailWord_105799).sum := by decide
  have hdescent : baseEnd_105799 < baseStart_105799 := by decide
  rcases family_descends (prefixWord ++ tailWord_105799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105853 : List Nat := [1, 4, 1, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_105853 : Nat := 118140960795 + 105853 * 2 ^ 59
def prefixEnd_105853 : Nat := 4983230072969 + 3 ^ 40 * 105853 * 2
def baseEnd_105853 : Nat := 54353467720479583350697

theorem tailTrace_105853 : CollatzResearch.WordTrace tailWord_105853 prefixEnd_105853 54353467720479583350697 := by
  unfold tailWord_105853
  simp only [CollatzResearch.WordTrace]
  refine ⟨3860776085520134098226213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2573850723680089398817475 3860776085520134098226213)
  ·
    refine ⟨723895516035025143417415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3860776085520134098226213 723895516035025143417415)
    ·
      refine ⟨1085843274052537715126123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 723895516035025143417415 1085843274052537715126123)
      ·
        refine ⟨1628764911078806572689185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1085843274052537715126123 1628764911078806572689185)
        ·
          refine ⟨1221573683309104929516889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1628764911078806572689185 1221573683309104929516889)
          ·
            refine ⟨916180262481828697137667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1221573683309104929516889 916180262481828697137667)
            ·
              refine ⟨1374270393722743045706501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916180262481828697137667 1374270393722743045706501)
              ·
                refine ⟨257675698823014321069969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1374270393722743045706501 257675698823014321069969)
                ·
                  refine ⟨193256774117260740802477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257675698823014321069969 193256774117260740802477)
                  ·
                    refine ⟨72471290293972777800929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193256774117260740802477 72471290293972777800929)
                    ·
                      refine ⟨54353467720479583350697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72471290293972777800929 54353467720479583350697)
                      ·
                        rfl

theorem cell23_105853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_105853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105853 prefixEnd_105853 := by exact prefixLift 105853
  have htrace : WordTrace (prefixWord ++ tailWord_105853) baseStart_105853 baseEnd_105853 := by
    simpa [prefixWord, tailWord_105853, baseEnd_105853] using wordTrace_append hprefix tailTrace_105853
  have hstable : (prefixWord ++ tailWord_105853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105853).length < 2 ^ (prefixWord ++ tailWord_105853).sum := by decide
  have hdescent : baseEnd_105853 < baseStart_105853 := by decide
  rcases family_descends (prefixWord ++ tailWord_105853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105854 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_105854 : Nat := 118140960795 + 105854 * 2 ^ 59
def prefixEnd_105854 : Nat := 4983230072969 + 3 ^ 40 * 105854 * 2
def baseEnd_105854 : Nat := 18117993733711359812731

theorem tailTrace_105854 : CollatzResearch.WordTrace tailWord_105854 prefixEnd_105854 18117993733711359812731 := by
  unfold tailWord_105854
  simp only [CollatzResearch.WordTrace]
  refine ⟨482601569814563908626577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2573875039011007512675077 482601569814563908626577)
  ·
    refine ⟨361951177360922931469933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 482601569814563908626577 361951177360922931469933)
    ·
      refine ⟨135731691510346099301225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361951177360922931469933 135731691510346099301225)
      ·
        refine ⟨101798768632759574475919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135731691510346099301225 101798768632759574475919)
        ·
          refine ⟨152698152949139361713879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101798768632759574475919 152698152949139361713879)
          ·
            refine ⟨229047229423709042570819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152698152949139361713879 229047229423709042570819)
            ·
              refine ⟨343570844135563563856229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229047229423709042570819 343570844135563563856229)
              ·
                refine ⟨64419533275418168223043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343570844135563563856229 64419533275418168223043)
                ·
                  refine ⟨96629299913127252334565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64419533275418168223043 96629299913127252334565)
                  ·
                    refine ⟨18117993733711359812731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96629299913127252334565 18117993733711359812731)
                    ·
                      rfl

theorem cell23_105854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_105854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105854 prefixEnd_105854 := by exact prefixLift 105854
  have htrace : WordTrace (prefixWord ++ tailWord_105854) baseStart_105854 baseEnd_105854 := by
    simpa [prefixWord, tailWord_105854, baseEnd_105854] using wordTrace_append hprefix tailTrace_105854
  have hstable : (prefixWord ++ tailWord_105854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105854).length < 2 ^ (prefixWord ++ tailWord_105854).sum := by decide
  have hdescent : baseEnd_105854 < baseStart_105854 := by decide
  rcases family_descends (prefixWord ++ tailWord_105854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105917 : List Nat := [1, 4, 1, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_105917 : Nat := 118140960795 + 105917 * 2 ^ 59
def prefixEnd_105917 : Nat := 4983230072969 + 3 ^ 40 * 105917 * 2
def baseEnd_105917 : Nat := 54386330482367332950403

theorem tailTrace_105917 : CollatzResearch.WordTrace tailWord_105917 prefixEnd_105917 54386330482367332950403 := by
  unfold tailWord_105917
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863110357288273028556005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2575406904858848685704003 3863110357288273028556005)
  ·
    refine ⟨724333191991551192854251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3863110357288273028556005 724333191991551192854251)
    ·
      refine ⟨1086499787987326789281377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 724333191991551192854251 1086499787987326789281377)
      ·
        refine ⟨814874840990495091961033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1086499787987326789281377 814874840990495091961033)
        ·
          refine ⟨611156130742871318970775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 814874840990495091961033 611156130742871318970775)
          ·
            refine ⟨916734196114306978456163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 611156130742871318970775 916734196114306978456163)
            ·
              refine ⟨1375101294171460467684245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 916734196114306978456163 1375101294171460467684245)
              ·
                refine ⟨64457873164287209422699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1375101294171460467684245 64457873164287209422699)
                ·
                  refine ⟨96686809746430814134049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64457873164287209422699 96686809746430814134049)
                  ·
                    refine ⟨72515107309823110600537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96686809746430814134049 72515107309823110600537)
                    ·
                      refine ⟨54386330482367332950403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72515107309823110600537 54386330482367332950403)
                      ·
                        rfl

theorem cell23_105917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_105917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105917 prefixEnd_105917 := by exact prefixLift 105917
  have htrace : WordTrace (prefixWord ++ tailWord_105917) baseStart_105917 baseEnd_105917 := by
    simpa [prefixWord, tailWord_105917, baseEnd_105917] using wordTrace_append hprefix tailTrace_105917
  have hstable : (prefixWord ++ tailWord_105917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105917).length < 2 ^ (prefixWord ++ tailWord_105917).sum := by decide
  have hdescent : baseEnd_105917 < baseStart_105917 := by decide
  rcases family_descends (prefixWord ++ tailWord_105917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105919 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 9]
def baseStart_105919 : Nat := 118140960795 + 105919 * 2 ^ 59
def prefixEnd_105919 : Nat := 4983230072969 + 3 ^ 40 * 105919 * 2
def baseEnd_105919 : Nat := 18129119147892108375131

theorem tailTrace_105919 : CollatzResearch.WordTrace tailWord_105919 prefixEnd_105919 18129119147892108375131 := by
  unfold tailWord_105919
  simp only [CollatzResearch.WordTrace]
  refine ⟨3863183303281027370128811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2575455535520684913419207 3863183303281027370128811)
  ·
    refine ⟨5794774954921541055193217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3863183303281027370128811 5794774954921541055193217)
    ·
      refine ⟨4346081216191155791394913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5794774954921541055193217 4346081216191155791394913)
      ·
        refine ⟨3259560912143366843546185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4346081216191155791394913 3259560912143366843546185)
        ·
          refine ⟨2444670684107525132659639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3259560912143366843546185 2444670684107525132659639)
          ·
            refine ⟨3667006026161287698989459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2444670684107525132659639 3667006026161287698989459)
            ·
              refine ⟨5500509039241931548484189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667006026161287698989459 5500509039241931548484189)
              ·
                refine ⟨2062690889715724330681571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5500509039241931548484189 2062690889715724330681571)
                ·
                  refine ⟨3094036334573586496022357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2062690889715724330681571 3094036334573586496022357)
                  ·
                    refine ⟨18129119147892108375131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 3094036334573586496022357 18129119147892108375131)
                    ·
                      rfl

theorem cell23_105919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 9].length) (baseStart_105919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105919 prefixEnd_105919 := by exact prefixLift 105919
  have htrace : WordTrace (prefixWord ++ tailWord_105919) baseStart_105919 baseEnd_105919 := by
    simpa [prefixWord, tailWord_105919, baseEnd_105919] using wordTrace_append hprefix tailTrace_105919
  have hstable : (prefixWord ++ tailWord_105919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105919).length < 2 ^ (prefixWord ++ tailWord_105919).sum := by decide
  have hdescent : baseEnd_105919 < baseStart_105919 := by decide
  rcases family_descends (prefixWord ++ tailWord_105919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105940 : List Nat := [2, 4, 1, 2, 3, 2, 2, 7]
def baseStart_105940 : Nat := 118140960795 + 105940 * 2 ^ 59
def prefixEnd_105940 : Nat := 4983230072969 + 3 ^ 40 * 105940 * 2
def baseEnd_105940 : Nat := 2014745945830397887511

theorem tailTrace_105940 : CollatzResearch.WordTrace tailWord_105940 prefixEnd_105940 2014745945830397887511 := by
  unfold tailWord_105940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1931974618102473978321637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2575966157469965304428849 1931974618102473978321637)
  ·
    refine ⟨362245240894213870935307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1931974618102473978321637 362245240894213870935307)
    ·
      refine ⟨543367861341320806402961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 362245240894213870935307 543367861341320806402961)
      ·
        refine ⟨407525896005990604802221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543367861341320806402961 407525896005990604802221)
        ·
          refine ⟨152822211002246476800833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 407525896005990604802221 152822211002246476800833)
          ·
            refine ⟨114616658251684857600625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152822211002246476800833 114616658251684857600625)
            ·
              refine ⟨85962493688763643200469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114616658251684857600625 85962493688763643200469)
              ·
                refine ⟨2014745945830397887511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85962493688763643200469 2014745945830397887511)
                ·
                  rfl

theorem cell23_105940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 7].length) (baseStart_105940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105940 prefixEnd_105940 := by exact prefixLift 105940
  have htrace : WordTrace (prefixWord ++ tailWord_105940) baseStart_105940 baseEnd_105940 := by
    simpa [prefixWord, tailWord_105940, baseEnd_105940] using wordTrace_append hprefix tailTrace_105940
  have hstable : (prefixWord ++ tailWord_105940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105940).length < 2 ^ (prefixWord ++ tailWord_105940).sum := by decide
  have hdescent : baseEnd_105940 < baseStart_105940 := by decide
  rcases family_descends (prefixWord ++ tailWord_105940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_105943 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 3, 3, 2]
def baseStart_105943 : Nat := 118140960795 + 105943 * 2 ^ 59
def prefixEnd_105943 : Nat := 4983230072969 + 3 ^ 40 * 105943 * 2
def baseEnd_105943 : Nat := 54399680979384231225283

theorem tailTrace_105943 : CollatzResearch.WordTrace tailWord_105943 prefixEnd_105943 54399680979384231225283 := by
  unfold tailWord_105943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3864058655194079469002483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2576039103462719646001655 3864058655194079469002483)
  ·
    refine ⟨5796087982791119203503725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3864058655194079469002483 5796087982791119203503725)
    ·
      refine ⟨2173532993546669701313897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5796087982791119203503725 2173532993546669701313897)
      ·
        refine ⟨1630149745160002275985423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2173532993546669701313897 1630149745160002275985423)
        ·
          refine ⟨2445224617740003413978135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1630149745160002275985423 2445224617740003413978135)
          ·
            refine ⟨3667836926610005120967203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2445224617740003413978135 3667836926610005120967203)
            ·
              refine ⟨5501755389915007681450805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3667836926610005120967203 5501755389915007681450805)
              ·
                refine ⟨515789567804531970136013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5501755389915007681450805 515789567804531970136013)
                ·
                  refine ⟨193421087926699488801005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 515789567804531970136013 193421087926699488801005)
                  ·
                    refine ⟨72532907972512308300377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193421087926699488801005 72532907972512308300377)
                    ·
                      refine ⟨54399680979384231225283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 72532907972512308300377 54399680979384231225283)
                      ·
                        rfl

theorem cell23_105943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_105943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_105943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_105943 prefixEnd_105943 := by exact prefixLift 105943
  have htrace : WordTrace (prefixWord ++ tailWord_105943) baseStart_105943 baseEnd_105943 := by
    simpa [prefixWord, tailWord_105943, baseEnd_105943] using wordTrace_append hprefix tailTrace_105943
  have hstable : (prefixWord ++ tailWord_105943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_105943).length < 2 ^ (prefixWord ++ tailWord_105943).sum := by decide
  have hdescent : baseEnd_105943 < baseStart_105943 := by decide
  rcases family_descends (prefixWord ++ tailWord_105943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
