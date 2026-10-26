import V185TrunkScan23Chunk0533

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3156957 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 2, 6]
def baseStart_3156957 : Nat := 118140960795 + 3156957 * 2 ^ 59
def prefixEnd_3156957 : Nat := 4983230072969 + 3 ^ 40 * 3156957 * 2
def baseEnd_3156957 : Nat := 540345448858703374972975

theorem tailTrace_3156957 : CollatzResearch.WordTrace tailWord_3156957 prefixEnd_3156957 540345448858703374972975 := by
  unfold tailWord_3156957
  simp only [CollatzResearch.WordTrace]
  refine ⟨115143681223891429175565125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76762454149260952783710083 115143681223891429175565125)
  ·
    refine ⟨21589440229479642970418461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115143681223891429175565125 21589440229479642970418461)
    ·
      refine ⟨8096040086054866113906923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21589440229479642970418461 8096040086054866113906923)
      ·
        refine ⟨12144060129082299170860385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096040086054866113906923 12144060129082299170860385)
        ·
          refine ⟨9108045096811724378145289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12144060129082299170860385 9108045096811724378145289)
          ·
            refine ⟨6831033822608793283608967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9108045096811724378145289 6831033822608793283608967)
            ·
              refine ⟨10246550733913189925413451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831033822608793283608967 10246550733913189925413451)
              ·
                refine ⟨15369826100869784888120177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10246550733913189925413451 15369826100869784888120177)
                ·
                  refine ⟨11527369575652338666090133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15369826100869784888120177 11527369575652338666090133)
                  ·
                    refine ⟨540345448858703374972975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11527369575652338666090133 540345448858703374972975)
                    ·
                      rfl

theorem cell23_3156957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_3156957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156957 prefixEnd_3156957 := by exact prefixLift 3156957
  have htrace : WordTrace (prefixWord ++ tailWord_3156957) baseStart_3156957 baseEnd_3156957 := by
    simpa [prefixWord, tailWord_3156957, baseEnd_3156957] using wordTrace_append hprefix tailTrace_3156957
  have hstable : (prefixWord ++ tailWord_3156957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156957).length < 2 ^ (prefixWord ++ tailWord_3156957).sum := by decide
  have hdescent : baseEnd_3156957 < baseStart_3156957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3156970 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 9]
def baseStart_3156970 : Nat := 118140960795 + 3156970 * 2 ^ 59
def prefixEnd_3156970 : Nat := 4983230072969 + 3 ^ 40 * 3156970 * 2
def baseEnd_3156970 : Nat := 180115891313846508228485

theorem tailTrace_3156970 : CollatzResearch.WordTrace tailWord_3156970 prefixEnd_3156970 180115891313846508228485 := by
  unfold tailWord_3156970
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786038843211083098947091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76762770248562888263858909 28786038843211083098947091)
  ·
    refine ⟨43179058264816624648420637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28786038843211083098947091 43179058264816624648420637)
    ·
      refine ⟨16192146849306234243157739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43179058264816624648420637 16192146849306234243157739)
      ·
        refine ⟨24288220273959351364736609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16192146849306234243157739 24288220273959351364736609)
        ·
          refine ⟨18216165205469513523552457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24288220273959351364736609 18216165205469513523552457)
          ·
            refine ⟨13662123904102135142664343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18216165205469513523552457 13662123904102135142664343)
            ·
              refine ⟨20493185856153202713996515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13662123904102135142664343 20493185856153202713996515)
              ·
                refine ⟨30739778784229804070994773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20493185856153202713996515 30739778784229804070994773)
                ·
                  refine ⟨180115891313846508228485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30739778784229804070994773 180115891313846508228485)
                  ·
                    rfl

theorem cell23_3156970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 9].length) (baseStart_3156970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3156970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3156970 prefixEnd_3156970 := by exact prefixLift 3156970
  have htrace : WordTrace (prefixWord ++ tailWord_3156970) baseStart_3156970 baseEnd_3156970 := by
    simpa [prefixWord, tailWord_3156970, baseEnd_3156970] using wordTrace_append hprefix tailTrace_3156970
  have hstable : (prefixWord ++ tailWord_3156970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3156970).length < 2 ^ (prefixWord ++ tailWord_3156970).sum := by decide
  have hdescent : baseEnd_3156970 < baseStart_3156970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3156970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157050 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_3157050 : Nat := 118140960795 + 3157050 * 2 ^ 59
def prefixEnd_3157050 : Nat := 4983230072969 + 3 ^ 40 * 3157050 * 2
def baseEnd_3157050 : Nat := 1621084100276978261055997

theorem tailTrace_3157050 : CollatzResearch.WordTrace tailWord_3157050 prefixEnd_3157050 1621084100276978261055997 := by
  unfold tailWord_3157050
  simp only [CollatzResearch.WordTrace]
  refine ⟨28786768303138626514675151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76764715475036337372467069 28786768303138626514675151)
  ·
    refine ⟨43180152454707939772012727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28786768303138626514675151 43180152454707939772012727)
    ·
      refine ⟨64770228682061909658019091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43180152454707939772012727 64770228682061909658019091)
      ·
        refine ⟨97155343023092864487028637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64770228682061909658019091 97155343023092864487028637)
        ·
          refine ⟨36433253633659824182635739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97155343023092864487028637 36433253633659824182635739)
          ·
            refine ⟨54649880450489736273953609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36433253633659824182635739 54649880450489736273953609)
            ·
              refine ⟨40987410337867302205465207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54649880450489736273953609 40987410337867302205465207)
              ·
                refine ⟨61481115506800953308197811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40987410337867302205465207 61481115506800953308197811)
                ·
                  refine ⟨92221673260201429962296717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61481115506800953308197811 92221673260201429962296717)
                  ·
                    refine ⟨34583127472575536235861269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92221673260201429962296717 34583127472575536235861269)
                    ·
                      refine ⟨1621084100276978261055997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34583127472575536235861269 1621084100276978261055997)
                      ·
                        rfl

theorem cell23_3157050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_3157050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157050 prefixEnd_3157050 := by exact prefixLift 3157050
  have htrace : WordTrace (prefixWord ++ tailWord_3157050) baseStart_3157050 baseEnd_3157050 := by
    simpa [prefixWord, tailWord_3157050, baseEnd_3157050] using wordTrace_append hprefix tailTrace_3157050
  have hstable : (prefixWord ++ tailWord_3157050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157050).length < 2 ^ (prefixWord ++ tailWord_3157050).sum := by decide
  have hdescent : baseEnd_3157050 < baseStart_3157050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157054 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3157054 : Nat := 118140960795 + 3157054 * 2 ^ 59
def prefixEnd_3157054 : Nat := 4983230072969 + 3 ^ 40 * 3157054 * 2
def baseEnd_3157054 : Nat := 1621086154199596245405979

theorem tailTrace_3157054 : CollatzResearch.WordTrace tailWord_3157054 prefixEnd_3157054 1621086154199596245405979 := by
  unfold tailWord_3157054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14393402388067501842730777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76764812736360009827897477 14393402388067501842730777)
  ·
    refine ⟨10795051791050626382048083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14393402388067501842730777 10795051791050626382048083)
    ·
      refine ⟨16192577686575939573072125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10795051791050626382048083 16192577686575939573072125)
      ·
        refine ⟨6072216632465977339902047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16192577686575939573072125 6072216632465977339902047)
        ·
          refine ⟨9108324948698966009853071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072216632465977339902047 9108324948698966009853071)
          ·
            refine ⟨13662487423048449014779607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108324948698966009853071 13662487423048449014779607)
            ·
              refine ⟨20493731134572673522169411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13662487423048449014779607 20493731134572673522169411)
              ·
                refine ⟨30740596701859010283254117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20493731134572673522169411 30740596701859010283254117)
                ·
                  refine ⟨5763861881598564428110147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30740596701859010283254117 5763861881598564428110147)
                  ·
                    refine ⟨8645792822397846642165221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5763861881598564428110147 8645792822397846642165221)
                    ·
                      refine ⟨1621086154199596245405979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8645792822397846642165221 1621086154199596245405979)
                      ·
                        rfl

theorem cell23_3157054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3157054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157054 prefixEnd_3157054 := by exact prefixLift 3157054
  have htrace : WordTrace (prefixWord ++ tailWord_3157054) baseStart_3157054 baseEnd_3157054 := by
    simpa [prefixWord, tailWord_3157054, baseEnd_3157054] using wordTrace_append hprefix tailTrace_3157054
  have hstable : (prefixWord ++ tailWord_3157054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157054).length < 2 ^ (prefixWord ++ tailWord_3157054).sum := by decide
  have hdescent : baseEnd_3157054 < baseStart_3157054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157077 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 6]
def baseStart_3157077 : Nat := 118140960795 + 3157077 * 2 ^ 59
def prefixEnd_3157077 : Nat := 4983230072969 + 3 ^ 40 * 3157077 * 2
def baseEnd_3157077 : Nat := 180121996028294406157597

theorem tailTrace_3157077 : CollatzResearch.WordTrace tailWord_3157077 prefixEnd_3157077 180121996028294406157597 := by
  unfold tailWord_3157077
  simp only [CollatzResearch.WordTrace]
  refine ⟨115148057983456689669933485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76765371988971126446622323 115148057983456689669933485)
  ·
    refine ⟨43180521743796258626225057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115148057983456689669933485 43180521743796258626225057)
    ·
      refine ⟨32385391307847193969668793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43180521743796258626225057 32385391307847193969668793)
      ·
        refine ⟨24289043480885395477251595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32385391307847193969668793 24289043480885395477251595)
        ·
          refine ⟨36433565221328093215877393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24289043480885395477251595 36433565221328093215877393)
          ·
            refine ⟨27325173915996069911908045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36433565221328093215877393 27325173915996069911908045)
            ·
              refine ⟨10246940218498526216965517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27325173915996069911908045 10246940218498526216965517)
              ·
                refine ⟨3842602581936947331362069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10246940218498526216965517 3842602581936947331362069)
                ·
                  refine ⟨180121996028294406157597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3842602581936947331362069 180121996028294406157597)
                  ·
                    rfl

theorem cell23_3157077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 6].length) (baseStart_3157077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157077 prefixEnd_3157077 := by exact prefixLift 3157077
  have htrace : WordTrace (prefixWord ++ tailWord_3157077) baseStart_3157077 baseEnd_3157077 := by
    simpa [prefixWord, tailWord_3157077, baseEnd_3157077] using wordTrace_append hprefix tailTrace_3157077
  have hstable : (prefixWord ++ tailWord_3157077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157077).length < 2 ^ (prefixWord ++ tailWord_3157077).sum := by decide
  have hdescent : baseEnd_3157077 < baseStart_3157077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157144 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3157144 : Nat := 118140960795 + 3157144 * 2 ^ 59
def prefixEnd_3157144 : Nat := 4983230072969 + 3 ^ 40 * 3157144 * 2
def baseEnd_3157144 : Nat := 1621132367458500893280565

theorem tailTrace_3157144 : CollatzResearch.WordTrace tailWord_3157144 prefixEnd_3157144 1621132367458500893280565 := by
  unfold tailWord_3157144
  simp only [CollatzResearch.WordTrace]
  refine ⟨57575250837106980056311243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76767001116142640075081657 57575250837106980056311243)
  ·
    refine ⟨86362876255660470084466865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57575250837106980056311243 86362876255660470084466865)
    ·
      refine ⟨64772157191745352563350149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86362876255660470084466865 64772157191745352563350149)
      ·
        refine ⟨12144779473452253605628153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64772157191745352563350149 12144779473452253605628153)
        ·
          refine ⟨9108584605089190204221115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12144779473452253605628153 9108584605089190204221115)
          ·
            refine ⟨13662876907633785306331673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9108584605089190204221115 13662876907633785306331673)
            ·
              refine ⟨10247157680725338979748755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13662876907633785306331673 10247157680725338979748755)
              ·
                refine ⟨15370736521088008469623133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247157680725338979748755 15370736521088008469623133)
                ·
                  refine ⟨5764026195408003176108675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15370736521088008469623133 5764026195408003176108675)
                  ·
                    refine ⟨8646039293112004764163013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764026195408003176108675 8646039293112004764163013)
                    ·
                      refine ⟨1621132367458500893280565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8646039293112004764163013 1621132367458500893280565)
                      ·
                        rfl

theorem cell23_3157144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3157144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157144 prefixEnd_3157144 := by exact prefixLift 3157144
  have htrace : WordTrace (prefixWord ++ tailWord_3157144) baseStart_3157144 baseEnd_3157144 := by
    simpa [prefixWord, tailWord_3157144, baseEnd_3157144] using wordTrace_append hprefix tailTrace_3157144
  have hstable : (prefixWord ++ tailWord_3157144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157144).length < 2 ^ (prefixWord ++ tailWord_3157144).sum := by decide
  have hdescent : baseEnd_3157144 < baseStart_3157144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157148 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_3157148 : Nat := 118140960795 + 3157148 * 2 ^ 59
def prefixEnd_3157148 : Nat := 4983230072969 + 3 ^ 40 * 3157148 * 2
def baseEnd_3157148 : Nat := 1621134421381118877630547

theorem tailTrace_3157148 : CollatzResearch.WordTrace tailWord_3157148 prefixEnd_3157148 1621134421381118877630547 := by
  unfold tailWord_3157148
  simp only [CollatzResearch.WordTrace]
  refine ⟨57575323783099734397884049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76767098377466312530512065 57575323783099734397884049)
  ·
    refine ⟨43181492837324800798413037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57575323783099734397884049 43181492837324800798413037)
    ·
      refine ⟨16193059813996800299404889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43181492837324800798413037 16193059813996800299404889)
      ·
        refine ⟨12144794860497600224553667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16193059813996800299404889 12144794860497600224553667)
        ·
          refine ⟨18217192290746400336830501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12144794860497600224553667 18217192290746400336830501)
          ·
            refine ⟨3415723554514950063155719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18217192290746400336830501 3415723554514950063155719)
            ·
              refine ⟨5123585331772425094733579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415723554514950063155719 5123585331772425094733579)
              ·
                refine ⟨7685377997658637642100369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123585331772425094733579 7685377997658637642100369)
                ·
                  refine ⟨5764033498243978231575277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7685377997658637642100369 5764033498243978231575277)
                  ·
                    refine ⟨2161512561841491836840729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5764033498243978231575277 2161512561841491836840729)
                    ·
                      refine ⟨1621134421381118877630547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161512561841491836840729 1621134421381118877630547)
                      ·
                        rfl

theorem cell23_3157148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_3157148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157148 prefixEnd_3157148 := by exact prefixLift 3157148
  have htrace : WordTrace (prefixWord ++ tailWord_3157148) baseStart_3157148 baseEnd_3157148 := by
    simpa [prefixWord, tailWord_3157148, baseEnd_3157148] using wordTrace_append hprefix tailTrace_3157148
  have hstable : (prefixWord ++ tailWord_3157148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157148).length < 2 ^ (prefixWord ++ tailWord_3157148).sum := by decide
  have hdescent : baseEnd_3157148 < baseStart_3157148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157188 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_3157188 : Nat := 118140960795 + 3157188 * 2 ^ 59
def prefixEnd_3157188 : Nat := 4983230072969 + 3 ^ 40 * 3157188 * 2
def baseEnd_3157188 : Nat := 540384986869099573710121

theorem tailTrace_3157188 : CollatzResearch.WordTrace tailWord_3157188 prefixEnd_3157188 540384986869099573710121 := by
  unfold tailWord_3157188
  simp only [CollatzResearch.WordTrace]
  refine ⟨57576053243027277813612109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76768070990703037084816145 57576053243027277813612109)
  ·
    refine ⟨21591019966135229180104541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57576053243027277813612109 21591019966135229180104541)
    ·
      refine ⟨8096632487300710942539203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21591019966135229180104541 8096632487300710942539203)
      ·
        refine ⟨12144948730951066413808805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8096632487300710942539203 12144948730951066413808805)
        ·
          refine ⟨2277177887053324952589151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12144948730951066413808805 2277177887053324952589151)
          ·
            refine ⟨3415766830579987428883727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2277177887053324952589151 3415766830579987428883727)
            ·
              refine ⟨5123650245869981143325591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3415766830579987428883727 5123650245869981143325591)
              ·
                refine ⟨7685475368804971714988387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123650245869981143325591 7685475368804971714988387)
                ·
                  refine ⟨11528213053207457572482581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685475368804971714988387 11528213053207457572482581)
                  ·
                    refine ⟨540384986869099573710121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11528213053207457572482581 540384986869099573710121)
                    ·
                      rfl

theorem cell23_3157188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_3157188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157188 prefixEnd_3157188 := by exact prefixLift 3157188
  have htrace : WordTrace (prefixWord ++ tailWord_3157188) baseStart_3157188 baseEnd_3157188 := by
    simpa [prefixWord, tailWord_3157188, baseEnd_3157188] using wordTrace_append hprefix tailTrace_3157188
  have hstable : (prefixWord ++ tailWord_3157188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157188).length < 2 ^ (prefixWord ++ tailWord_3157188).sum := by decide
  have hdescent : baseEnd_3157188 < baseStart_3157188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157198 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3]
def baseStart_3157198 : Nat := 118140960795 + 3157198 * 2 ^ 59
def prefixEnd_3157198 : Nat := 4983230072969 + 3 ^ 40 * 3157198 * 2
def baseEnd_3157198 : Nat := 1621160095413843682005317

theorem tailTrace_3157198 : CollatzResearch.WordTrace tailWord_3157198 prefixEnd_3157198 1621160095413843682005317 := by
  unfold tailWord_3157198
  simp only [CollatzResearch.WordTrace]
  refine ⟨14394058902002290916886031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76768314144012218223392165 14394058902002290916886031)
  ·
    refine ⟨21591088353003436375329047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14394058902002290916886031 21591088353003436375329047)
    ·
      refine ⟨32386632529505154562993571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21591088353003436375329047 32386632529505154562993571)
      ·
        refine ⟨48579948794257731844490357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32386632529505154562993571 48579948794257731844490357)
        ·
          refine ⟨4554370199461662360420971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48579948794257731844490357 4554370199461662360420971)
          ·
            refine ⟨6831555299192493540631457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554370199461662360420971 6831555299192493540631457)
            ·
              refine ⟨5123666474394370155473593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831555299192493540631457 5123666474394370155473593)
              ·
                refine ⟨3842749855795777616605195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123666474394370155473593 3842749855795777616605195)
                ·
                  refine ⟨5764124783693666424907793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3842749855795777616605195 5764124783693666424907793)
                  ·
                    refine ⟨4323093587770249818680845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5764124783693666424907793 4323093587770249818680845)
                    ·
                      refine ⟨1621160095413843682005317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323093587770249818680845 1621160095413843682005317)
                      ·
                        rfl

theorem cell23_3157198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_3157198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157198 prefixEnd_3157198 := by exact prefixLift 3157198
  have htrace : WordTrace (prefixWord ++ tailWord_3157198) baseStart_3157198 baseEnd_3157198 := by
    simpa [prefixWord, tailWord_3157198, baseEnd_3157198] using wordTrace_append hprefix tailTrace_3157198
  have hstable : (prefixWord ++ tailWord_3157198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157198).length < 2 ^ (prefixWord ++ tailWord_3157198).sum := by decide
  have hdescent : baseEnd_3157198 < baseStart_3157198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157207 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_3157207 : Nat := 118140960795 + 3157207 * 2 ^ 59
def prefixEnd_3157207 : Nat := 4983230072969 + 3 ^ 40 * 3157207 * 2
def baseEnd_3157207 : Nat := 1621164716739734146792775

theorem tailTrace_3157207 : CollatzResearch.WordTrace tailWord_3157207 prefixEnd_3157207 1621164716739734146792775 := by
  unfold tailWord_3157207
  simp only [CollatzResearch.WordTrace]
  refine ⟨115152799472985721872165875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76768532981990481248110583 115152799472985721872165875)
  ·
    refine ⟨172729199209478582808248813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115152799472985721872165875 172729199209478582808248813)
    ·
      refine ⟨64773449703554468553093305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172729199209478582808248813 64773449703554468553093305)
      ·
        refine ⟨48580087277665851414819979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64773449703554468553093305 48580087277665851414819979)
        ·
          refine ⟨72870130916498777122229969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48580087277665851414819979 72870130916498777122229969)
          ·
            refine ⟨54652598187374082841672477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72870130916498777122229969 54652598187374082841672477)
            ·
              refine ⟨20494724320265281065627179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54652598187374082841672477 20494724320265281065627179)
              ·
                refine ⟨30742086480397921598440769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20494724320265281065627179 30742086480397921598440769)
                ·
                  refine ⟨23056564860298441198830577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30742086480397921598440769 23056564860298441198830577)
                  ·
                    refine ⟨17292423645223830899122933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23056564860298441198830577 17292423645223830899122933)
                    ·
                      refine ⟨1621164716739734146792775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17292423645223830899122933 1621164716739734146792775)
                      ·
                        rfl

theorem cell23_3157207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_3157207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157207 prefixEnd_3157207 := by exact prefixLift 3157207
  have htrace : WordTrace (prefixWord ++ tailWord_3157207) baseStart_3157207 baseEnd_3157207 := by
    simpa [prefixWord, tailWord_3157207, baseEnd_3157207] using wordTrace_append hprefix tailTrace_3157207
  have hstable : (prefixWord ++ tailWord_3157207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157207).length < 2 ^ (prefixWord ++ tailWord_3157207).sum := by decide
  have hdescent : baseEnd_3157207 < baseStart_3157207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157257 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 9]
def baseStart_3157257 : Nat := 118140960795 + 3157257 * 2 ^ 59
def prefixEnd_3157257 : Nat := 4983230072969 + 3 ^ 40 * 3157257 * 2
def baseEnd_3157257 : Nat := 180132265641384327907505

theorem tailTrace_3157257 : CollatzResearch.WordTrace tailWord_3157257 prefixEnd_3157257 180132265641384327907505 := by
  unfold tailWord_3157257
  simp only [CollatzResearch.WordTrace]
  refine ⟨115154623122804580411486025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76769748748536386940990683 115154623122804580411486025)
  ·
    refine ⟨86365967342103435308614519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115154623122804580411486025 86365967342103435308614519)
    ·
      refine ⟨129548951013155152962921779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86365967342103435308614519 129548951013155152962921779)
      ·
        refine ⟨194323426519732729444382669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129548951013155152962921779 194323426519732729444382669)
        ·
          refine ⟨72871284944899773541643501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194323426519732729444382669 72871284944899773541643501)
          ·
            refine ⟨27326731854337415078116313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72871284944899773541643501 27326731854337415078116313)
            ·
              refine ⟨20495048890753061308587235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27326731854337415078116313 20495048890753061308587235)
              ·
                refine ⟨30742573336129591962880853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20495048890753061308587235 30742573336129591962880853)
                ·
                  refine ⟨180132265641384327907505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30742573336129591962880853 180132265641384327907505)
                  ·
                    rfl

theorem cell23_3157257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 9].length) (baseStart_3157257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157257 prefixEnd_3157257 := by exact prefixLift 3157257
  have htrace : WordTrace (prefixWord ++ tailWord_3157257) baseStart_3157257 baseEnd_3157257 := by
    simpa [prefixWord, tailWord_3157257, baseEnd_3157257] using wordTrace_append hprefix tailTrace_3157257
  have hstable : (prefixWord ++ tailWord_3157257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157257).length < 2 ^ (prefixWord ++ tailWord_3157257).sum := by decide
  have hdescent : baseEnd_3157257 < baseStart_3157257 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157285 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 2, 2, 2]
def baseStart_3157285 : Nat := 118140960795 + 3157285 * 2 ^ 59
def prefixEnd_3157285 : Nat := 4983230072969 + 3 ^ 40 * 3157285 * 2
def baseEnd_3157285 : Nat := 1621204768230784841617417

theorem tailTrace_3157285 : CollatzResearch.WordTrace tailWord_3157285 prefixEnd_3157285 1621204768230784841617417 := by
  unfold tailWord_3157285
  simp only [CollatzResearch.WordTrace]
  refine ⟨115155644366703141193505309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76770429577802094129003539 115155644366703141193505309)
  ·
    refine ⟨43183366637513677947564491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115155644366703141193505309 43183366637513677947564491)
    ·
      refine ⟨64775049956270516921346737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43183366637513677947564491 64775049956270516921346737)
      ·
        refine ⟨48581287467202887691010053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64775049956270516921346737 48581287467202887691010053)
        ·
          refine ⟨9108991400100541442064385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48581287467202887691010053 9108991400100541442064385)
          ·
            refine ⟨6831743550075406081548289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9108991400100541442064385 6831743550075406081548289)
            ·
              refine ⟨5123807662556554561161217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831743550075406081548289 5123807662556554561161217)
              ·
                refine ⟨3842855746917415920870913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5123807662556554561161217 3842855746917415920870913)
                ·
                  refine ⟨2882141810188061940653185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3842855746917415920870913 2882141810188061940653185)
                  ·
                    refine ⟨2161606357641046455489889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2882141810188061940653185 2161606357641046455489889)
                    ·
                      refine ⟨1621204768230784841617417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161606357641046455489889 1621204768230784841617417)
                      ·
                        rfl

theorem cell23_3157285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_3157285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157285 prefixEnd_3157285 := by exact prefixLift 3157285
  have htrace : WordTrace (prefixWord ++ tailWord_3157285) baseStart_3157285 baseEnd_3157285 := by
    simpa [prefixWord, tailWord_3157285, baseEnd_3157285] using wordTrace_append hprefix tailTrace_3157285
  have hstable : (prefixWord ++ tailWord_3157285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157285).length < 2 ^ (prefixWord ++ tailWord_3157285).sum := by decide
  have hdescent : baseEnd_3157285 < baseStart_3157285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157301 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_3157301 : Nat := 118140960795 + 3157301 * 2 ^ 59
def prefixEnd_3157301 : Nat := 4983230072969 + 3 ^ 40 * 3157301 * 2
def baseEnd_3157301 : Nat := 1621212983921256779017343

theorem tailTrace_3157301 : CollatzResearch.WordTrace tailWord_3157301 prefixEnd_3157301 1621212983921256779017343 := by
  unfold tailWord_3157301
  simp only [CollatzResearch.WordTrace]
  refine ⟨115156227934645175926087757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76770818623096783950725171 115156227934645175926087757)
  ·
    refine ⟨43183585475491940972282909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115156227934645175926087757 43183585475491940972282909)
    ·
      refine ⟨16193844553309477864606091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43183585475491940972282909 16193844553309477864606091)
      ·
        refine ⟨24290766829964216796909137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16193844553309477864606091 24290766829964216796909137)
        ·
          refine ⟨18218075122473162597681853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24290766829964216796909137 18218075122473162597681853)
          ·
            refine ⟨6831778170927435974130695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18218075122473162597681853 6831778170927435974130695)
            ·
              refine ⟨10247667256391153961196043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6831778170927435974130695 10247667256391153961196043)
              ·
                refine ⟨15371500884586730941794065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10247667256391153961196043 15371500884586730941794065)
                ·
                  refine ⟨11528625663440048206345549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15371500884586730941794065 11528625663440048206345549)
                  ·
                    refine ⟨4323234623790018077379581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11528625663440048206345549 4323234623790018077379581)
                    ·
                      refine ⟨1621212983921256779017343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323234623790018077379581 1621212983921256779017343)
                      ·
                        rfl

theorem cell23_3157301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_3157301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157301 prefixEnd_3157301 := by exact prefixLift 3157301
  have htrace : WordTrace (prefixWord ++ tailWord_3157301) baseStart_3157301 baseEnd_3157301 := by
    simpa [prefixWord, tailWord_3157301, baseEnd_3157301] using wordTrace_append hprefix tailTrace_3157301
  have hstable : (prefixWord ++ tailWord_3157301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157301).length < 2 ^ (prefixWord ++ tailWord_3157301).sum := by decide
  have hdescent : baseEnd_3157301 < baseStart_3157301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157302 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_3157302 : Nat := 118140960795 + 3157302 * 2 ^ 59
def prefixEnd_3157302 : Nat := 4983230072969 + 3 ^ 40 * 3157302 * 2
def baseEnd_3157302 : Nat := 1621213497401911275104839

theorem tailTrace_3157302 : CollatzResearch.WordTrace tailWord_3157302 prefixEnd_3157302 1621213497401911275104839 := by
  unfold tailWord_3157302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197266525477597068554635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76770842938427702064582773 7197266525477597068554635)
  ·
    refine ⟨10795899788216395602831953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7197266525477597068554635 10795899788216395602831953)
    ·
      refine ⟨8096924841162296702123965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10795899788216395602831953 8096924841162296702123965)
      ·
        refine ⟨3036346815435861263296487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8096924841162296702123965 3036346815435861263296487)
        ·
          refine ⟨4554520223153791894944731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3036346815435861263296487 4554520223153791894944731)
          ·
            refine ⟨6831780334730687842417097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554520223153791894944731 6831780334730687842417097)
            ·
              refine ⟨5123835251048015881812823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6831780334730687842417097 5123835251048015881812823)
              ·
                refine ⟨7685752876572023822719235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5123835251048015881812823 7685752876572023822719235)
                ·
                  refine ⟨11528629314858035734078853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7685752876572023822719235 11528629314858035734078853)
                  ·
                    refine ⟨2161617996535881700139785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11528629314858035734078853 2161617996535881700139785)
                    ·
                      refine ⟨1621213497401911275104839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161617996535881700139785 1621213497401911275104839)
                      ·
                        rfl

theorem cell23_3157302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_3157302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157302 prefixEnd_3157302 := by exact prefixLift 3157302
  have htrace : WordTrace (prefixWord ++ tailWord_3157302) baseStart_3157302 baseEnd_3157302 := by
    simpa [prefixWord, tailWord_3157302, baseEnd_3157302] using wordTrace_append hprefix tailTrace_3157302
  have hstable : (prefixWord ++ tailWord_3157302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157302).length < 2 ^ (prefixWord ++ tailWord_3157302).sum := by decide
  have hdescent : baseEnd_3157302 < baseStart_3157302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157431 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_3157431 : Nat := 118140960795 + 3157431 * 2 ^ 59
def prefixEnd_3157431 : Nat := 4983230072969 + 3 ^ 40 * 3157431 * 2
def baseEnd_3157431 : Nat := 1621279736406341270391745

theorem tailTrace_3157431 : CollatzResearch.WordTrace tailWord_3157431 prefixEnd_3157431 1621279736406341270391745 := by
  unfold tailWord_3157431
  simp only [CollatzResearch.WordTrace]
  refine ⟨115160969424174208128320147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76773979616116138752213431 115160969424174208128320147)
  ·
    refine ⟨172741454136261312192480221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115160969424174208128320147 172741454136261312192480221)
    ·
      refine ⟨64778045301097992072180083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172741454136261312192480221 64778045301097992072180083)
      ·
        refine ⟨97167067951646988108270125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64778045301097992072180083 97167067951646988108270125)
        ·
          refine ⟨36437650481867620540601297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97167067951646988108270125 36437650481867620540601297)
          ·
            refine ⟨27328237861400715405450973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36437650481867620540601297 27328237861400715405450973)
            ·
              refine ⟨10248089198025268277044115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27328237861400715405450973 10248089198025268277044115)
              ·
                refine ⟨15372133797037902415566173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248089198025268277044115 15372133797037902415566173)
                ·
                  refine ⟨5764550173889213405837315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15372133797037902415566173 5764550173889213405837315)
                  ·
                    refine ⟨8646825260833820108755973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764550173889213405837315 8646825260833820108755973)
                    ·
                      refine ⟨1621279736406341270391745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8646825260833820108755973 1621279736406341270391745)
                      ·
                        rfl

theorem cell23_3157431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_3157431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157431 prefixEnd_3157431 := by exact prefixLift 3157431
  have htrace : WordTrace (prefixWord ++ tailWord_3157431) baseStart_3157431 baseEnd_3157431 := by
    simpa [prefixWord, tailWord_3157431, baseEnd_3157431] using wordTrace_append hprefix tailTrace_3157431
  have hstable : (prefixWord ++ tailWord_3157431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157431).length < 2 ^ (prefixWord ++ tailWord_3157431).sum := by decide
  have hdescent : baseEnd_3157431 < baseStart_3157431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157434 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_3157434 : Nat := 118140960795 + 3157434 * 2 ^ 59
def prefixEnd_3157434 : Nat := 4983230072969 + 3 ^ 40 * 3157434 * 2
def baseEnd_3157434 : Nat := 1621281276848304758654231

theorem tailTrace_3157434 : CollatzResearch.WordTrace tailWord_3157434 prefixEnd_3157434 1621281276848304758654231 := by
  unfold tailWord_3157434
  simp only [CollatzResearch.WordTrace]
  refine ⟨28790269710790834910169839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76774052562108893093786237 28790269710790834910169839)
  ·
    refine ⟨43185404566186252365254759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28790269710790834910169839 43185404566186252365254759)
    ·
      refine ⟨64778106849279378547882139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43185404566186252365254759 64778106849279378547882139)
      ·
        refine ⟨97167160273919067821823209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64778106849279378547882139 97167160273919067821823209)
        ·
          refine ⟨72875370205439300866367407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97167160273919067821823209 72875370205439300866367407)
          ·
            refine ⟨109313055308158951299551111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72875370205439300866367407 109313055308158951299551111)
            ·
              refine ⟨163969582962238426949326667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109313055308158951299551111 163969582962238426949326667)
              ·
                refine ⟨245954374443357640423990001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163969582962238426949326667 245954374443357640423990001)
                ·
                  refine ⟨184465780832518230317992501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245954374443357640423990001 184465780832518230317992501)
                  ·
                    refine ⟨17293666953048584092311797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184465780832518230317992501 17293666953048584092311797)
                    ·
                      refine ⟨1621281276848304758654231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17293666953048584092311797 1621281276848304758654231)
                      ·
                        rfl

theorem cell23_3157434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_3157434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157434 prefixEnd_3157434 := by exact prefixLift 3157434
  have htrace : WordTrace (prefixWord ++ tailWord_3157434) baseStart_3157434 baseEnd_3157434 := by
    simpa [prefixWord, tailWord_3157434, baseEnd_3157434] using wordTrace_append hprefix tailTrace_3157434
  have hstable : (prefixWord ++ tailWord_3157434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157434).length < 2 ^ (prefixWord ++ tailWord_3157434).sum := by decide
  have hdescent : baseEnd_3157434 < baseStart_3157434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157451 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 5]
def baseStart_3157451 : Nat := 118140960795 + 3157451 * 2 ^ 59
def prefixEnd_3157451 : Nat := 4983230072969 + 3 ^ 40 * 3157451 * 2
def baseEnd_3157451 : Nat := 1621290006019431192141653

theorem tailTrace_3157451 : CollatzResearch.WordTrace tailWord_3157451 prefixEnd_3157451 1621290006019431192141653 := by
  unfold tailWord_3157451
  simp only [CollatzResearch.WordTrace]
  refine ⟨115161698884101751544048207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76774465922734501029365471 115161698884101751544048207)
  ·
    refine ⟨172742548326152627316072311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115161698884101751544048207 172742548326152627316072311)
    ·
      refine ⟨259113822489228940974108467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172742548326152627316072311 259113822489228940974108467)
      ·
        refine ⟨388670733733843411461162701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259113822489228940974108467 388670733733843411461162701)
        ·
          refine ⟨145751525150191279297936013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 388670733733843411461162701 145751525150191279297936013)
          ·
            refine ⟨54656821931321729736726005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145751525150191279297936013 54656821931321729736726005)
            ·
              refine ⟨5124077056061412162818063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54656821931321729736726005 5124077056061412162818063)
              ·
                refine ⟨7686115584092118244227095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124077056061412162818063 7686115584092118244227095)
                ·
                  refine ⟨11529173376138177366340643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686115584092118244227095 11529173376138177366340643)
                  ·
                    refine ⟨17293760064207266049510965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11529173376138177366340643 17293760064207266049510965)
                    ·
                      refine ⟨1621290006019431192141653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17293760064207266049510965 1621290006019431192141653)
                      ·
                        rfl

theorem cell23_3157451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 5].length) (baseStart_3157451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157451 prefixEnd_3157451 := by exact prefixLift 3157451
  have htrace : WordTrace (prefixWord ++ tailWord_3157451) baseStart_3157451 baseEnd_3157451 := by
    simpa [prefixWord, tailWord_3157451, baseEnd_3157451] using wordTrace_append hprefix tailTrace_3157451
  have hstable : (prefixWord ++ tailWord_3157451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157451).length < 2 ^ (prefixWord ++ tailWord_3157451).sum := by decide
  have hdescent : baseEnd_3157451 < baseStart_3157451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157461 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3157461 : Nat := 118140960795 + 3157461 * 2 ^ 59
def prefixEnd_3157461 : Nat := 4983230072969 + 3 ^ 40 * 3157461 * 2
def baseEnd_3157461 : Nat := 1621295140825976153016607

theorem tailTrace_3157461 : CollatzResearch.WordTrace tailWord_3157461 prefixEnd_3157461 1621295140825976153016607 := by
  unfold tailWord_3157461
  simp only [CollatzResearch.WordTrace]
  refine ⟨115162063614065523251912237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76774709076043682167941491 115162063614065523251912237)
  ·
    refine ⟨43185773855274571219467089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115162063614065523251912237 43185773855274571219467089)
    ·
      refine ⟨32389330391455928414600317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43185773855274571219467089 32389330391455928414600317)
      ·
        refine ⟨12145998896795973155475119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32389330391455928414600317 12145998896795973155475119)
        ·
          refine ⟨18218998345193959733212679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12145998896795973155475119 18218998345193959733212679)
          ·
            refine ⟨27328497517790939599819019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18218998345193959733212679 27328497517790939599819019)
            ·
              refine ⟨40992746276686409399728529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27328497517790939599819019 40992746276686409399728529)
              ·
                refine ⟨30744559707514807049796397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40992746276686409399728529 30744559707514807049796397)
                ·
                  refine ⟨11529209890318052643673649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30744559707514807049796397 11529209890318052643673649)
                  ·
                    refine ⟨8646907417738539482755237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11529209890318052643673649 8646907417738539482755237)
                    ·
                      refine ⟨1621295140825976153016607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8646907417738539482755237 1621295140825976153016607)
                      ·
                        rfl

theorem cell23_3157461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3157461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157461 prefixEnd_3157461 := by exact prefixLift 3157461
  have htrace : WordTrace (prefixWord ++ tailWord_3157461) baseStart_3157461 baseEnd_3157461 := by
    simpa [prefixWord, tailWord_3157461, baseEnd_3157461] using wordTrace_append hprefix tailTrace_3157461
  have hstable : (prefixWord ++ tailWord_3157461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157461).length < 2 ^ (prefixWord ++ tailWord_3157461).sum := by decide
  have hdescent : baseEnd_3157461 < baseStart_3157461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157482 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_3157482 : Nat := 118140960795 + 3157482 * 2 ^ 59
def prefixEnd_3157482 : Nat := 4983230072969 + 3 ^ 40 * 3157482 * 2
def baseEnd_3157482 : Nat := 1621305923919720570854011

theorem tailTrace_3157482 : CollatzResearch.WordTrace tailWord_3157482 prefixEnd_3157482 1621305923919720570854011 := by
  unfold tailWord_3157482
  simp only [CollatzResearch.WordTrace]
  refine ⟨28790707386747360959606675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76775219697992962558951133 28790707386747360959606675)
  ·
    refine ⟨43186061080121041439410013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28790707386747360959606675 43186061080121041439410013)
    ·
      refine ⟨16194772905045390539778755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43186061080121041439410013 16194772905045390539778755)
      ·
        refine ⟨24292159357568085809668133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16194772905045390539778755 24292159357568085809668133)
        ·
          refine ⟨4554779879544016089312775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24292159357568085809668133 4554779879544016089312775)
          ·
            refine ⟨6832169819316024133969163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554779879544016089312775 6832169819316024133969163)
            ·
              refine ⟨10248254728974036200953745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832169819316024133969163 10248254728974036200953745)
              ·
                refine ⟨7686191046730527150715309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10248254728974036200953745 7686191046730527150715309)
                ·
                  refine ⟨2882321642523947681518241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7686191046730527150715309 2882321642523947681518241)
                  ·
                    refine ⟨2161741231892960761138681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2882321642523947681518241 2161741231892960761138681)
                    ·
                      refine ⟨1621305923919720570854011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161741231892960761138681 1621305923919720570854011)
                      ·
                        rfl

theorem cell23_3157482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_3157482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157482 prefixEnd_3157482 := by exact prefixLift 3157482
  have htrace : WordTrace (prefixWord ++ tailWord_3157482) baseStart_3157482 baseEnd_3157482 := by
    simpa [prefixWord, tailWord_3157482, baseEnd_3157482] using wordTrace_append hprefix tailTrace_3157482
  have hstable : (prefixWord ++ tailWord_3157482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157482).length < 2 ^ (prefixWord ++ tailWord_3157482).sum := by decide
  have hdescent : baseEnd_3157482 < baseStart_3157482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157498 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3]
def baseStart_3157498 : Nat := 118140960795 + 3157498 * 2 ^ 59
def prefixEnd_3157498 : Nat := 4983230072969 + 3 ^ 40 * 3157498 * 2
def baseEnd_3157498 : Nat := 1621314139610192508253937

theorem tailTrace_3157498 : CollatzResearch.WordTrace tailWord_3157498 prefixEnd_3157498 1621314139610192508253937 := by
  unfold tailWord_3157498
  simp only [CollatzResearch.WordTrace]
  refine ⟨28790853278732869642752287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76775608743287652380672765 28790853278732869642752287)
  ·
    refine ⟨43186279918099304464128431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28790853278732869642752287 43186279918099304464128431)
    ·
      refine ⟨64779419877148956696192647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43186279918099304464128431 64779419877148956696192647)
      ·
        refine ⟨97169129815723435044288971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64779419877148956696192647 97169129815723435044288971)
        ·
          refine ⟨145753694723585152566433457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97169129815723435044288971 145753694723585152566433457)
          ·
            refine ⟨109315271042688864424825093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145753694723585152566433457 109315271042688864424825093)
            ·
              refine ⟨20496613320504162079654705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109315271042688864424825093 20496613320504162079654705)
              ·
                refine ⟨15372459990378121559741029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20496613320504162079654705 15372459990378121559741029)
                ·
                  refine ⟨2882336248195897792451443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15372459990378121559741029 2882336248195897792451443)
                  ·
                    refine ⟨4323504372293846688677165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882336248195897792451443 4323504372293846688677165)
                    ·
                      refine ⟨1621314139610192508253937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323504372293846688677165 1621314139610192508253937)
                      ·
                        rfl

theorem cell23_3157498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 4, 1, 3].length) (baseStart_3157498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157498 prefixEnd_3157498 := by exact prefixLift 3157498
  have htrace : WordTrace (prefixWord ++ tailWord_3157498) baseStart_3157498 baseEnd_3157498 := by
    simpa [prefixWord, tailWord_3157498, baseEnd_3157498] using wordTrace_append hprefix tailTrace_3157498
  have hstable : (prefixWord ++ tailWord_3157498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157498).length < 2 ^ (prefixWord ++ tailWord_3157498).sum := by decide
  have hdescent : baseEnd_3157498 < baseStart_3157498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157515 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 3]
def baseStart_3157515 : Nat := 118140960795 + 3157515 * 2 ^ 59
def prefixEnd_3157515 : Nat := 4983230072969 + 3 ^ 40 * 3157515 * 2
def baseEnd_3157515 : Nat := 1621322868781318941741359

theorem tailTrace_3157515 : CollatzResearch.WordTrace tailWord_3157515 prefixEnd_3157515 1621322868781318941741359 := by
  unfold tailWord_3157515
  simp only [CollatzResearch.WordTrace]
  refine ⟨115164033155869890474377999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76776022103913260316251999 115164033155869890474377999)
  ·
    refine ⟨172746049733804835711566999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115164033155869890474377999 172746049733804835711566999)
    ·
      refine ⟨259119074600707253567350499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172746049733804835711566999 259119074600707253567350499)
      ·
        refine ⟨388678611901060880351025749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259119074600707253567350499 388678611901060880351025749)
        ·
          refine ⟨4554827483215557191613583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 388678611901060880351025749 4554827483215557191613583)
          ·
            refine ⟨6832241224823335787420375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554827483215557191613583 6832241224823335787420375)
            ·
              refine ⟨10248361837235003681130563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832241224823335787420375 10248361837235003681130563)
              ·
                refine ⟨15372542755852505521695845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248361837235003681130563 15372542755852505521695845)
                ·
                  refine ⟨2882351766722344785317971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15372542755852505521695845 2882351766722344785317971)
                  ·
                    refine ⟨4323527650083517177976957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882351766722344785317971 4323527650083517177976957)
                    ·
                      refine ⟨1621322868781318941741359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323527650083517177976957 1621322868781318941741359)
                      ·
                        rfl

theorem cell23_3157515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 1, 3].length) (baseStart_3157515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157515 prefixEnd_3157515 := by exact prefixLift 3157515
  have htrace : WordTrace (prefixWord ++ tailWord_3157515) baseStart_3157515 baseEnd_3157515 := by
    simpa [prefixWord, tailWord_3157515, baseEnd_3157515] using wordTrace_append hprefix tailTrace_3157515
  have hstable : (prefixWord ++ tailWord_3157515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157515).length < 2 ^ (prefixWord ++ tailWord_3157515).sum := by decide
  have hdescent : baseEnd_3157515 < baseStart_3157515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157532 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_3157532 : Nat := 118140960795 + 3157532 * 2 ^ 59
def prefixEnd_3157532 : Nat := 4983230072969 + 3 ^ 40 * 3157532 * 2
def baseEnd_3157532 : Nat := 1621331597952445375228781

theorem tailTrace_3157532 : CollatzResearch.WordTrace tailWord_3157532 prefixEnd_3157532 1621331597952445375228781 := by
  unfold tailWord_3157532
  simp only [CollatzResearch.WordTrace]
  refine ⟨57582326598404151188873425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76776435464538868251831233 57582326598404151188873425)
  ·
    refine ⟨43186744948803113391655069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57582326598404151188873425 43186744948803113391655069)
    ·
      refine ⟨16195029355801167521870651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43186744948803113391655069 16195029355801167521870651)
      ·
        refine ⟨24292544033701751282805977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16195029355801167521870651 24292544033701751282805977)
        ·
          refine ⟨18219408025276313462104483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24292544033701751282805977 18219408025276313462104483)
          ·
            refine ⟨27329112037914470193156725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18219408025276313462104483 27329112037914470193156725)
            ·
              refine ⟨2562104253554481580608443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27329112037914470193156725 2562104253554481580608443)
              ·
                refine ⟨3843156380331722370912665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562104253554481580608443 3843156380331722370912665)
                ·
                  refine ⟨2882367285248791778184499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3843156380331722370912665 2882367285248791778184499)
                  ·
                    refine ⟨4323550927873187667276749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882367285248791778184499 4323550927873187667276749)
                    ·
                      refine ⟨1621331597952445375228781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323550927873187667276749 1621331597952445375228781)
                      ·
                        rfl

theorem cell23_3157532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_3157532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157532 prefixEnd_3157532 := by exact prefixLift 3157532
  have htrace : WordTrace (prefixWord ++ tailWord_3157532) baseStart_3157532 baseEnd_3157532 := by
    simpa [prefixWord, tailWord_3157532, baseEnd_3157532] using wordTrace_append hprefix tailTrace_3157532
  have hstable : (prefixWord ++ tailWord_3157532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157532).length < 2 ^ (prefixWord ++ tailWord_3157532).sum := by decide
  have hdescent : baseEnd_3157532 < baseStart_3157532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157541 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_3157541 : Nat := 118140960795 + 3157541 * 2 ^ 59
def prefixEnd_3157541 : Nat := 4983230072969 + 3 ^ 40 * 3157541 * 2
def baseEnd_3157541 : Nat := 1621336219278335840016239

theorem tailTrace_3157541 : CollatzResearch.WordTrace tailWord_3157541 prefixEnd_3157541 1621336219278335840016239 := by
  unfold tailWord_3157541
  simp only [CollatzResearch.WordTrace]
  refine ⟨115164981453775696914824477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76776654302517131276549651 115164981453775696914824477)
  ·
    refine ⟨43186868045165886343059179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115164981453775696914824477 43186868045165886343059179)
    ·
      refine ⟨64780302067748829514588769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43186868045165886343059179 64780302067748829514588769)
      ·
        refine ⟨48585226550811622135941577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64780302067748829514588769 48585226550811622135941577)
        ·
          refine ⟨36438919913108716601956183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48585226550811622135941577 36438919913108716601956183)
          ·
            refine ⟨54658379869663074902934275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36438919913108716601956183 54658379869663074902934275)
            ·
              refine ⟨81987569804494612354401413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54658379869663074902934275 81987569804494612354401413)
              ·
                refine ⟨15372669338342739816450265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81987569804494612354401413 15372669338342739816450265)
                ·
                  refine ⟨11529502003757054862337699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15372669338342739816450265 11529502003757054862337699)
                  ·
                    refine ⟨17294253005635582293506549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11529502003757054862337699 17294253005635582293506549)
                    ·
                      refine ⟨1621336219278335840016239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17294253005635582293506549 1621336219278335840016239)
                      ·
                        rfl

theorem cell23_3157541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_3157541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157541 prefixEnd_3157541 := by exact prefixLift 3157541
  have htrace : WordTrace (prefixWord ++ tailWord_3157541) baseStart_3157541 baseEnd_3157541 := by
    simpa [prefixWord, tailWord_3157541, baseEnd_3157541] using wordTrace_append hprefix tailTrace_3157541
  have hstable : (prefixWord ++ tailWord_3157541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157541).length < 2 ^ (prefixWord ++ tailWord_3157541).sum := by decide
  have hdescent : baseEnd_3157541 < baseStart_3157541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157555 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 4, 2, 2]
def baseStart_3157555 : Nat := 118140960795 + 3157555 * 2 ^ 59
def prefixEnd_3157555 : Nat := 4983230072969 + 3 ^ 40 * 3157555 * 2
def baseEnd_3157555 : Nat := 1621343408007498785241175

theorem tailTrace_3157555 : CollatzResearch.WordTrace tailWord_3157555 prefixEnd_3157555 1621343408007498785241175 := by
  unfold tailWord_3157555
  simp only [CollatzResearch.WordTrace]
  refine ⟨115165492075724977305834119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76776994717149984870556079 115165492075724977305834119)
  ·
    refine ⟨172748238113587465958751179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115165492075724977305834119 172748238113587465958751179)
    ·
      refine ⟨259122357170381198938126769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172748238113587465958751179 259122357170381198938126769)
      ·
        refine ⟨194341767877785899203595077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259122357170381198938126769 194341767877785899203595077)
        ·
          refine ⟨36439081477084856100674077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194341767877785899203595077 36439081477084856100674077)
          ·
            refine ⟨13664655553906821037752779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36439081477084856100674077 13664655553906821037752779)
            ·
              refine ⟨20496983330860231556629169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13664655553906821037752779 20496983330860231556629169)
              ·
                refine ⟨15372737498145173667471877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20496983330860231556629169 15372737498145173667471877)
                ·
                  refine ⟨2882388280902220062650977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15372737498145173667471877 2882388280902220062650977)
                  ·
                    refine ⟨2161791210676665046988233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2882388280902220062650977 2161791210676665046988233)
                    ·
                      refine ⟨1621343408007498785241175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161791210676665046988233 1621343408007498785241175)
                      ·
                        rfl

theorem cell23_3157555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 2, 2].length) (baseStart_3157555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157555 prefixEnd_3157555 := by exact prefixLift 3157555
  have htrace : WordTrace (prefixWord ++ tailWord_3157555) baseStart_3157555 baseEnd_3157555 := by
    simpa [prefixWord, tailWord_3157555, baseEnd_3157555] using wordTrace_append hprefix tailTrace_3157555
  have hstable : (prefixWord ++ tailWord_3157555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157555).length < 2 ^ (prefixWord ++ tailWord_3157555).sum := by decide
  have hdescent : baseEnd_3157555 < baseStart_3157555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157588 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3157588 : Nat := 118140960795 + 3157588 * 2 ^ 59
def prefixEnd_3157588 : Nat := 4983230072969 + 3 ^ 40 * 3157588 * 2
def baseEnd_3157588 : Nat := 1621360352869097156128523

theorem tailTrace_3157588 : CollatzResearch.WordTrace tailWord_3157588 prefixEnd_3157588 1621360352869097156128523 := by
  unfold tailWord_3157588
  simp only [CollatzResearch.WordTrace]
  refine ⟨57583347842302711970892709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76777797123070282627856945 57583347842302711970892709)
  ·
    refine ⟨10796877720431758494542383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57583347842302711970892709 10796877720431758494542383)
    ·
      refine ⟨16195316580647637741813575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10796877720431758494542383 16195316580647637741813575)
      ·
        refine ⟨24292974870971456612720363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16195316580647637741813575 24292974870971456612720363)
        ·
          refine ⟨36439462306457184919080545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24292974870971456612720363 36439462306457184919080545)
          ·
            refine ⟨27329596729842888689310409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36439462306457184919080545 27329596729842888689310409)
            ·
              refine ⟨20497197547382166516982807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27329596729842888689310409 20497197547382166516982807)
              ·
                refine ⟨30745796321073249775474211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20497197547382166516982807 30745796321073249775474211)
                ·
                  refine ⟨46118694481609874663211317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30745796321073249775474211 46118694481609874663211317)
                  ·
                    refine ⟨4323627607650925749676061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46118694481609874663211317 4323627607650925749676061)
                    ·
                      refine ⟨1621360352869097156128523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323627607650925749676061 1621360352869097156128523)
                      ·
                        rfl

theorem cell23_3157588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3157588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157588 prefixEnd_3157588 := by exact prefixLift 3157588
  have htrace : WordTrace (prefixWord ++ tailWord_3157588) baseStart_3157588 baseEnd_3157588 := by
    simpa [prefixWord, tailWord_3157588, baseEnd_3157588] using wordTrace_append hprefix tailTrace_3157588
  have hstable : (prefixWord ++ tailWord_3157588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157588).length < 2 ^ (prefixWord ++ tailWord_3157588).sum := by decide
  have hdescent : baseEnd_3157588 < baseStart_3157588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157601 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_3157601 : Nat := 118140960795 + 3157601 * 2 ^ 59
def prefixEnd_3157601 : Nat := 4983230072969 + 3 ^ 40 * 3157601 * 2
def baseEnd_3157601 : Nat := 1621367028117605605265963

theorem tailTrace_3157601 : CollatzResearch.WordTrace tailWord_3157601 prefixEnd_3157601 1621367028117605605265963 := by
  unfold tailWord_3157601
  simp only [CollatzResearch.WordTrace]
  refine ⟨115167169833558327162008657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76778113222372218108005771 115167169833558327162008657)
  ·
    refine ⟨86375377375168745371506493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115167169833558327162008657 86375377375168745371506493)
    ·
      refine ⟨32390766515688279514314935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86375377375168745371506493 32390766515688279514314935)
      ·
        refine ⟨48586149773532419271472403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32390766515688279514314935 48586149773532419271472403)
        ·
          refine ⟨72879224660298628907208605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48586149773532419271472403 72879224660298628907208605)
          ·
            refine ⟨27329709247611985840203227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72879224660298628907208605 27329709247611985840203227)
            ·
              refine ⟨40994563871417978760304841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27329709247611985840203227 40994563871417978760304841)
              ·
                refine ⟨30745922903563484070228631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40994563871417978760304841 30745922903563484070228631)
                ·
                  refine ⟨46118884355345226105342947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30745922903563484070228631 46118884355345226105342947)
                  ·
                    refine ⟨69178326533017839158014421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46118884355345226105342947 69178326533017839158014421)
                    ·
                      refine ⟨1621367028117605605265963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69178326533017839158014421 1621367028117605605265963)
                      ·
                        rfl

theorem cell23_3157601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_3157601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157601 prefixEnd_3157601 := by exact prefixLift 3157601
  have htrace : WordTrace (prefixWord ++ tailWord_3157601) baseStart_3157601 baseEnd_3157601 := by
    simpa [prefixWord, tailWord_3157601, baseEnd_3157601] using wordTrace_append hprefix tailTrace_3157601
  have hstable : (prefixWord ++ tailWord_3157601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157601).length < 2 ^ (prefixWord ++ tailWord_3157601).sum := by decide
  have hdescent : baseEnd_3157601 < baseStart_3157601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157611 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4]
def baseStart_3157611 : Nat := 118140960795 + 3157611 * 2 ^ 59
def prefixEnd_3157611 : Nat := 4983230072969 + 3 ^ 40 * 3157611 * 2
def baseEnd_3157611 : Nat := 1621372162924150566140917

theorem tailTrace_3157611 : CollatzResearch.WordTrace tailWord_3157611 prefixEnd_3157611 1621372162924150566140917 := by
  unfold tailWord_3157611
  simp only [CollatzResearch.WordTrace]
  refine ⟨115167534563522098869872687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76778356375681399246581791 115167534563522098869872687)
  ·
    refine ⟨172751301845283148304809031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115167534563522098869872687 172751301845283148304809031)
    ·
      refine ⟨259126952767924722457213547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172751301845283148304809031 259126952767924722457213547)
      ·
        refine ⟨388690429151887083685820321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259126952767924722457213547 388690429151887083685820321)
        ·
          refine ⟨291517821863915312764365241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388690429151887083685820321 291517821863915312764365241)
          ·
            refine ⟨218638366397936484573273931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291517821863915312764365241 218638366397936484573273931)
            ·
              refine ⟨327957549596904726859910897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218638366397936484573273931 327957549596904726859910897)
              ·
                refine ⟨245968162197678545144933173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327957549596904726859910897 245968162197678545144933173)
                ·
                  refine ⟨23059515206032363607337485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245968162197678545144933173 23059515206032363607337485)
                  ·
                    refine ⟨8647318202262136352751557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23059515206032363607337485 8647318202262136352751557)
                    ·
                      refine ⟨1621372162924150566140917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8647318202262136352751557 1621372162924150566140917)
                      ·
                        rfl

theorem cell23_3157611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 4].length) (baseStart_3157611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157611 prefixEnd_3157611 := by exact prefixLift 3157611
  have htrace : WordTrace (prefixWord ++ tailWord_3157611) baseStart_3157611 baseEnd_3157611 := by
    simpa [prefixWord, tailWord_3157611, baseEnd_3157611] using wordTrace_append hprefix tailTrace_3157611
  have hstable : (prefixWord ++ tailWord_3157611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157611).length < 2 ^ (prefixWord ++ tailWord_3157611).sum := by decide
  have hdescent : baseEnd_3157611 < baseStart_3157611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157618 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3157618 : Nat := 118140960795 + 3157618 * 2 ^ 59
def prefixEnd_3157618 : Nat := 4983230072969 + 3 ^ 40 * 3157618 * 2
def baseEnd_3157618 : Nat := 1621375757288732038753385

theorem tailTrace_3157618 : CollatzResearch.WordTrace tailWord_3157618 prefixEnd_3157618 1621375757288732038753385 := by
  unfold tailWord_3157618
  simp only [CollatzResearch.WordTrace]
  refine ⟨28791947468624184766344377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76778526582997826043585005 28791947468624184766344377)
  ·
    refine ⟨21593960601468138574758283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28791947468624184766344377 21593960601468138574758283)
    ·
      refine ⟨32390940902202207862137425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21593960601468138574758283 32390940902202207862137425)
      ·
        refine ⟨24293205676651655896603069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32390940902202207862137425 24293205676651655896603069)
        ·
          refine ⟨9109952128744370961226151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24293205676651655896603069 9109952128744370961226151)
          ·
            refine ⟨13664928193116556441839227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109952128744370961226151 13664928193116556441839227)
            ·
              refine ⟨20497392289674834662758841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13664928193116556441839227 20497392289674834662758841)
              ·
                refine ⟨15373044217256125997069131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20497392289674834662758841 15373044217256125997069131)
                ·
                  refine ⟨23059566325884188995603697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15373044217256125997069131 23059566325884188995603697)
                  ·
                    refine ⟨17294674744413141746702773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23059566325884188995603697 17294674744413141746702773)
                    ·
                      refine ⟨1621375757288732038753385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17294674744413141746702773 1621375757288732038753385)
                      ·
                        rfl

theorem cell23_3157618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3157618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157618 prefixEnd_3157618 := by exact prefixLift 3157618
  have htrace : WordTrace (prefixWord ++ tailWord_3157618) baseStart_3157618 baseEnd_3157618 := by
    simpa [prefixWord, tailWord_3157618, baseEnd_3157618] using wordTrace_append hprefix tailTrace_3157618
  have hstable : (prefixWord ++ tailWord_3157618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157618).length < 2 ^ (prefixWord ++ tailWord_3157618).sum := by decide
  have hdescent : baseEnd_3157618 < baseStart_3157618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157648 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3]
def baseStart_3157648 : Nat := 118140960795 + 3157648 * 2 ^ 59
def prefixEnd_3157648 : Nat := 4983230072969 + 3 ^ 40 * 3157648 * 2
def baseEnd_3157648 : Nat := 1621391161708366921378247

theorem tailTrace_3157648 : CollatzResearch.WordTrace tailWord_3157648 prefixEnd_3157648 1621391161708366921378247 := by
  unfold tailWord_3157648
  simp only [CollatzResearch.WordTrace]
  refine ⟨57584442032194027094484799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76779256042925369459313065 57584442032194027094484799)
  ·
    refine ⟨86376663048291040641727199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57584442032194027094484799 86376663048291040641727199)
    ·
      refine ⟨129564994572436560962590799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86376663048291040641727199 129564994572436560962590799)
      ·
        refine ⟨194347491858654841443886199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129564994572436560962590799 194347491858654841443886199)
        ·
          refine ⟨291521237787982262165829299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194347491858654841443886199 291521237787982262165829299)
          ·
            refine ⟨437281856681973393248743949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291521237787982262165829299 437281856681973393248743949)
            ·
              refine ⟨163980696255740022468278981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 437281856681973393248743949 163980696255740022468278981)
              ·
                refine ⟨30746380547951254212802309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163980696255740022468278981 30746380547951254212802309)
                ·
                  refine ⟨5764946352740860164900433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30746380547951254212802309 5764946352740860164900433)
                  ·
                    refine ⟨4323709764555645123675325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5764946352740860164900433 4323709764555645123675325)
                    ·
                      refine ⟨1621391161708366921378247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323709764555645123675325 1621391161708366921378247)
                      ·
                        rfl

theorem cell23_3157648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 3].length) (baseStart_3157648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157648 prefixEnd_3157648 := by exact prefixLift 3157648
  have htrace : WordTrace (prefixWord ++ tailWord_3157648) baseStart_3157648 baseEnd_3157648 := by
    simpa [prefixWord, tailWord_3157648, baseEnd_3157648] using wordTrace_append hprefix tailTrace_3157648
  have hstable : (prefixWord ++ tailWord_3157648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157648).length < 2 ^ (prefixWord ++ tailWord_3157648).sum := by decide
  have hdescent : baseEnd_3157648 < baseStart_3157648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157655 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 3, 4]
def baseStart_3157655 : Nat := 118140960795 + 3157655 * 2 ^ 59
def prefixEnd_3157655 : Nat := 4983230072969 + 3 ^ 40 * 3157655 * 2
def baseEnd_3157655 : Nat := 540464918690982797996905

theorem tailTrace_3157655 : CollatzResearch.WordTrace tailWord_3157655 prefixEnd_3157655 540464918690982797996905 := by
  unfold tailWord_3157655
  simp only [CollatzResearch.WordTrace]
  refine ⟨115169139375362694384474419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76779426250241796256316279 115169139375362694384474419)
  ·
    refine ⟨172753709063044041576711629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115169139375362694384474419 172753709063044041576711629)
    ·
      refine ⟨64782640898641515591266861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172753709063044041576711629 64782640898641515591266861)
      ·
        refine ⟨24293490336990568346725073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64782640898641515591266861 24293490336990568346725073)
        ·
          refine ⟨18220117752742926260043805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24293490336990568346725073 18220117752742926260043805)
          ·
            refine ⟨6832544157278597347516427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18220117752742926260043805 6832544157278597347516427)
            ·
              refine ⟨10248816235917896021274641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832544157278597347516427 10248816235917896021274641)
              ·
                refine ⟨7686612176938422015955981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10248816235917896021274641 7686612176938422015955981)
                ·
                  refine ⟨2882479566351908255983493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7686612176938422015955981 2882479566351908255983493)
                  ·
                    refine ⟨540464918690982797996905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882479566351908255983493 540464918690982797996905)
                    ·
                      rfl

theorem cell23_3157655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_3157655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157655 prefixEnd_3157655 := by exact prefixLift 3157655
  have htrace : WordTrace (prefixWord ++ tailWord_3157655) baseStart_3157655 baseEnd_3157655 := by
    simpa [prefixWord, tailWord_3157655, baseEnd_3157655] using wordTrace_append hprefix tailTrace_3157655
  have hstable : (prefixWord ++ tailWord_3157655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157655).length < 2 ^ (prefixWord ++ tailWord_3157655).sum := by decide
  have hdescent : baseEnd_3157655 < baseStart_3157655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157662 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_3157662 : Nat := 118140960795 + 3157662 * 2 ^ 59
def prefixEnd_3157662 : Nat := 4983230072969 + 3 ^ 40 * 3157662 * 2
def baseEnd_3157662 : Nat := 1621398350437529866603183

theorem tailTrace_3157662 : CollatzResearch.WordTrace tailWord_3157662 prefixEnd_3157662 1621398350437529866603183 := by
  unfold tailWord_3157662
  simp only [CollatzResearch.WordTrace]
  refine ⟨14396174335792166822497405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76779596457558223053319493 14396174335792166822497405)
  ·
    refine ⟨5398565375922062558436527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14396174335792166822497405 5398565375922062558436527)
    ·
      refine ⟨8097848063883093837654791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5398565375922062558436527 8097848063883093837654791)
      ·
        refine ⟨12146772095824640756482187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8097848063883093837654791 12146772095824640756482187)
        ·
          refine ⟨18220158143736961134723281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12146772095824640756482187 18220158143736961134723281)
          ·
            refine ⟨13665118607802720851042461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18220158143736961134723281 13665118607802720851042461)
            ·
              refine ⟨5124419477926020319140923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13665118607802720851042461 5124419477926020319140923)
              ·
                refine ⟨7686629216889030478711385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124419477926020319140923 7686629216889030478711385)
                ·
                  refine ⟨5764971912666772859033539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7686629216889030478711385 5764971912666772859033539)
                  ·
                    refine ⟨8647457869000159288550309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5764971912666772859033539 8647457869000159288550309)
                    ·
                      refine ⟨1621398350437529866603183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8647457869000159288550309 1621398350437529866603183)
                      ·
                        rfl

theorem cell23_3157662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_3157662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157662 prefixEnd_3157662 := by exact prefixLift 3157662
  have htrace : WordTrace (prefixWord ++ tailWord_3157662) baseStart_3157662 baseEnd_3157662 := by
    simpa [prefixWord, tailWord_3157662, baseEnd_3157662] using wordTrace_append hprefix tailTrace_3157662
  have hstable : (prefixWord ++ tailWord_3157662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157662).length < 2 ^ (prefixWord ++ tailWord_3157662).sum := by decide
  have hdescent : baseEnd_3157662 < baseStart_3157662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157665 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3157665 : Nat := 118140960795 + 3157665 * 2 ^ 59
def prefixEnd_3157665 : Nat := 4983230072969 + 3 ^ 40 * 3157665 * 2
def baseEnd_3157665 : Nat := 1621399890879493354865669

theorem tailTrace_3157665 : CollatzResearch.WordTrace tailWord_3157665 prefixEnd_3157665 1621399890879493354865669 := by
  unfold tailWord_3157665
  simp only [CollatzResearch.WordTrace]
  refine ⟨115169504105326466092338449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76779669403550977394892299 115169504105326466092338449)
  ·
    refine ⟨86377128078994849569253837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115169504105326466092338449 86377128078994849569253837)
    ·
      refine ⟨32391423029623068588470189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86377128078994849569253837 32391423029623068588470189)
      ·
        refine ⟨12146783636108650720676321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32391423029623068588470189 12146783636108650720676321)
        ·
          refine ⟨9110087727081488040507241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12146783636108650720676321 9110087727081488040507241)
          ·
            refine ⟨6832565795311116030380431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110087727081488040507241 6832565795311116030380431)
            ·
              refine ⟨10248848692966674045570647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832565795311116030380431 10248848692966674045570647)
              ·
                refine ⟨15373273039450011068355971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248848692966674045570647 15373273039450011068355971)
                ·
                  refine ⟨23059909559175016602533957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15373273039450011068355971 23059909559175016602533957)
                  ·
                    refine ⟨4323733042345315612975117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23059909559175016602533957 4323733042345315612975117)
                    ·
                      refine ⟨1621399890879493354865669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323733042345315612975117 1621399890879493354865669)
                      ·
                        rfl

theorem cell23_3157665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3157665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157665 prefixEnd_3157665 := by exact prefixLift 3157665
  have htrace : WordTrace (prefixWord ++ tailWord_3157665) baseStart_3157665 baseEnd_3157665 := by
    simpa [prefixWord, tailWord_3157665, baseEnd_3157665] using wordTrace_append hprefix tailTrace_3157665
  have hstable : (prefixWord ++ tailWord_3157665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157665).length < 2 ^ (prefixWord ++ tailWord_3157665).sum := by decide
  have hdescent : baseEnd_3157665 < baseStart_3157665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157685 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 8]
def baseStart_3157685 : Nat := 118140960795 + 3157685 * 2 ^ 59
def prefixEnd_3157685 : Nat := 4983230072969 + 3 ^ 40 * 3157685 * 2
def baseEnd_3157685 : Nat := 180156684499175919623953

theorem tailTrace_3157685 : CollatzResearch.WordTrace tailWord_3157685 prefixEnd_3157685 180156684499175919623953 := by
  unfold tailWord_3157685
  simp only [CollatzResearch.WordTrace]
  refine ⟨115170233565254009508066509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76780155710169339672044339 115170233565254009508066509)
  ·
    refine ⟨43188837586970253565524941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115170233565254009508066509 43188837586970253565524941)
    ·
      refine ⟨16195814095113845087071853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43188837586970253565524941 16195814095113845087071853)
      ·
        refine ⟨6073430285667691907651945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16195814095113845087071853 6073430285667691907651945)
        ·
          refine ⟨4555072714250768930738959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6073430285667691907651945 4555072714250768930738959)
          ·
            refine ⟨6832609071376153396108439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555072714250768930738959 6832609071376153396108439)
            ·
              refine ⟨10248913607064230094162659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6832609071376153396108439 10248913607064230094162659)
              ·
                refine ⟨15373370410596345141243989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10248913607064230094162659 15373370410596345141243989)
                ·
                  refine ⟨180156684499175919623953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15373370410596345141243989 180156684499175919623953)
                  ·
                    rfl

theorem cell23_3157685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 8].length) (baseStart_3157685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157685 prefixEnd_3157685 := by exact prefixLift 3157685
  have htrace : WordTrace (prefixWord ++ tailWord_3157685) baseStart_3157685 baseEnd_3157685 := by
    simpa [prefixWord, tailWord_3157685, baseEnd_3157685] using wordTrace_append hprefix tailTrace_3157685
  have hstable : (prefixWord ++ tailWord_3157685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157685).length < 2 ^ (prefixWord ++ tailWord_3157685).sum := by decide
  have hdescent : baseEnd_3157685 < baseStart_3157685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157728 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 1, 6]
def baseStart_3157728 : Nat := 118140960795 + 3157728 * 2 ^ 59
def prefixEnd_3157728 : Nat := 4983230072969 + 3 ^ 40 * 3157728 * 2
def baseEnd_3157728 : Nat := 540477413386908869459293

theorem tailTrace_3157728 : CollatzResearch.WordTrace tailWord_3157728 prefixEnd_3157728 540477413386908869459293 := by
  unfold tailWord_3157728
  simp only [CollatzResearch.WordTrace]
  refine ⟨57585900952049113925940919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76781201269398818567921225 57585900952049113925940919)
  ·
    refine ⟨86378851428073670888911379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57585900952049113925940919 86378851428073670888911379)
    ·
      refine ⟨129568277142110506333367069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86378851428073670888911379 129568277142110506333367069)
      ·
        refine ⟨48588103928291439875012651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129568277142110506333367069 48588103928291439875012651)
        ·
          refine ⟨72882155892437159812518977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48588103928291439875012651 72882155892437159812518977)
          ·
            refine ⟨54661616919327869859389233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72882155892437159812518977 54661616919327869859389233)
            ·
              refine ⟨40996212689495902394541925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54661616919327869859389233 40996212689495902394541925)
              ·
                refine ⟨7686789879280481698976611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40996212689495902394541925 7686789879280481698976611)
                ·
                  refine ⟨11530184818920722548464917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7686789879280481698976611 11530184818920722548464917)
                  ·
                    refine ⟨540477413386908869459293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11530184818920722548464917 540477413386908869459293)
                    ·
                      rfl

theorem cell23_3157728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 1, 6].length) (baseStart_3157728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157728 prefixEnd_3157728 := by exact prefixLift 3157728
  have htrace : WordTrace (prefixWord ++ tailWord_3157728) baseStart_3157728 baseEnd_3157728 := by
    simpa [prefixWord, tailWord_3157728, baseEnd_3157728] using wordTrace_append hprefix tailTrace_3157728
  have hstable : (prefixWord ++ tailWord_3157728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157728).length < 2 ^ (prefixWord ++ tailWord_3157728).sum := by decide
  have hdescent : baseEnd_3157728 < baseStart_3157728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157745 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 4, 4]
def baseStart_3157745 : Nat := 118140960795 + 3157745 * 2 ^ 59
def prefixEnd_3157745 : Nat := 4983230072969 + 3 ^ 40 * 3157745 * 2
def baseEnd_3157745 : Nat := 540480323110617680621767

theorem tailTrace_3157745 : CollatzResearch.WordTrace tailWord_3157745 prefixEnd_3157745 540480323110617680621767 := by
  unfold tailWord_3157745
  simp only [CollatzResearch.WordTrace]
  refine ⟨115172421945036639755250689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76781614630024426503500459 115172421945036639755250689)
  ·
    refine ⟨86379316458777479816438017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115172421945036639755250689 86379316458777479816438017)
    ·
      refine ⟨64784487344083109862328513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86379316458777479816438017 64784487344083109862328513)
      ·
        refine ⟨48588365508062332396746385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64784487344083109862328513 48588365508062332396746385)
        ·
          refine ⟨36441274131046749297559789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48588365508062332396746385 36441274131046749297559789)
          ·
            refine ⟨13665477799142530986584921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36441274131046749297559789 13665477799142530986584921)
            ·
              refine ⟨10249108349356898239938691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13665477799142530986584921 10249108349356898239938691)
              ·
                refine ⟨15373662524035347359908037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10249108349356898239938691 15373662524035347359908037)
                ·
                  refine ⟨2882561723256627629982757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15373662524035347359908037 2882561723256627629982757)
                  ·
                    refine ⟨540480323110617680621767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882561723256627629982757 540480323110617680621767)
                    ·
                      rfl

theorem cell23_3157745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 4, 4].length) (baseStart_3157745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157745 prefixEnd_3157745 := by exact prefixLift 3157745
  have htrace : WordTrace (prefixWord ++ tailWord_3157745) baseStart_3157745 baseEnd_3157745 := by
    simpa [prefixWord, tailWord_3157745, baseEnd_3157745] using wordTrace_append hprefix tailTrace_3157745
  have hstable : (prefixWord ++ tailWord_3157745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157745).length < 2 ^ (prefixWord ++ tailWord_3157745).sum := by decide
  have hdescent : baseEnd_3157745 < baseStart_3157745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157746 : List Nat := [3, 2, 1, 3, 1, 1, 5, 2, 1, 1, 3]
def baseStart_3157746 : Nat := 118140960795 + 3157746 * 2 ^ 59
def prefixEnd_3157746 : Nat := 4983230072969 + 3 ^ 40 * 3157746 * 2
def baseEnd_3157746 : Nat := 1621441482812507537952797

theorem tailTrace_3157746 : CollatzResearch.WordTrace tailWord_3157746 prefixEnd_3157746 1621441482812507537952797 := by
  unfold tailWord_3157746
  simp only [CollatzResearch.WordTrace]
  refine ⟨28793114604508254231509273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76781638945355344617358061 28793114604508254231509273)
  ·
    refine ⟨21594835953381190673631955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28793114604508254231509273 21594835953381190673631955)
    ·
      refine ⟨32392253930071786010447933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21594835953381190673631955 32392253930071786010447933)
      ·
        refine ⟨12147095223776919753917975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32392253930071786010447933 12147095223776919753917975)
        ·
          refine ⟨18220642835665379630876963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12147095223776919753917975 18220642835665379630876963)
          ·
            refine ⟨27330964253498069446315445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18220642835665379630876963 27330964253498069446315445)
            ·
              refine ⟨2562277898765444010592073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27330964253498069446315445 2562277898765444010592073)
              ·
                refine ⟨1921708424074083007944055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562277898765444010592073 1921708424074083007944055)
                ·
                  refine ⟨2882562636111124511916083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921708424074083007944055 2882562636111124511916083)
                  ·
                    refine ⟨4323843954166686767874125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882562636111124511916083 4323843954166686767874125)
                    ·
                      refine ⟨1621441482812507537952797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323843954166686767874125 1621441482812507537952797)
                      ·
                        rfl

theorem cell23_3157746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_3157746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157746 prefixEnd_3157746 := by exact prefixLift 3157746
  have htrace : WordTrace (prefixWord ++ tailWord_3157746) baseStart_3157746 baseEnd_3157746 := by
    simpa [prefixWord, tailWord_3157746, baseEnd_3157746] using wordTrace_append hprefix tailTrace_3157746
  have hstable : (prefixWord ++ tailWord_3157746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157746).length < 2 ^ (prefixWord ++ tailWord_3157746).sum := by decide
  have hdescent : baseEnd_3157746 < baseStart_3157746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157752 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 3, 2, 2]
def baseStart_3157752 : Nat := 118140960795 + 3157752 * 2 ^ 59
def prefixEnd_3157752 : Nat := 4983230072969 + 3 ^ 40 * 3157752 * 2
def baseEnd_3157752 : Nat := 1621444563696434514477769

theorem tailTrace_3157752 : CollatzResearch.WordTrace tailWord_3157752 prefixEnd_3157752 1621444563696434514477769 := by
  unfold tailWord_3157752
  simp only [CollatzResearch.WordTrace]
  refine ⟨57586338628005639975377755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76781784837340853300503673 57586338628005639975377755)
  ·
    refine ⟨86379507942008459963066633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57586338628005639975377755 86379507942008459963066633)
    ·
      refine ⟨64784630956506344972299975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86379507942008459963066633 64784630956506344972299975)
      ·
        refine ⟨97176946434759517458449963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64784630956506344972299975 97176946434759517458449963)
        ·
          refine ⟨145765419652139276187674945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97176946434759517458449963 145765419652139276187674945)
          ·
            refine ⟨109324064739104457140756209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145765419652139276187674945 109324064739104457140756209)
            ·
              refine ⟨81993048554328342855567157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109324064739104457140756209 81993048554328342855567157)
              ·
                refine ⟨7686848301968282142709421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81993048554328342855567157 7686848301968282142709421)
                ·
                  refine ⟨2882568113238105803516033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7686848301968282142709421 2882568113238105803516033)
                  ·
                    refine ⟨2161926084928579352637025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2882568113238105803516033 2161926084928579352637025)
                    ·
                      refine ⟨1621444563696434514477769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2161926084928579352637025 1621444563696434514477769)
                      ·
                        rfl

theorem cell23_3157752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 2, 2].length) (baseStart_3157752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157752 prefixEnd_3157752 := by exact prefixLift 3157752
  have htrace : WordTrace (prefixWord ++ tailWord_3157752) baseStart_3157752 baseEnd_3157752 := by
    simpa [prefixWord, tailWord_3157752, baseEnd_3157752] using wordTrace_append hprefix tailTrace_3157752
  have hstable : (prefixWord ++ tailWord_3157752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157752).length < 2 ^ (prefixWord ++ tailWord_3157752).sum := by decide
  have hdescent : baseEnd_3157752 < baseStart_3157752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157772 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_3157772 : Nat := 118140960795 + 3157772 * 2 ^ 59
def prefixEnd_3157772 : Nat := 4983230072969 + 3 ^ 40 * 3157772 * 2
def baseEnd_3157772 : Nat := 1621454833309524436227677

theorem tailTrace_3157772 : CollatzResearch.WordTrace tailWord_3157772 prefixEnd_3157772 1621454833309524436227677 := by
  unfold tailWord_3157772
  simp only [CollatzResearch.WordTrace]
  refine ⟨57586703357969411683241785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76782271143959215577655713 57586703357969411683241785)
  ·
    refine ⟨43190027518477058762431339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57586703357969411683241785 43190027518477058762431339)
    ·
      refine ⟨64785041277715588143647009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43190027518477058762431339 64785041277715588143647009)
      ·
        refine ⟨48588780958286691107735257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64785041277715588143647009 48588780958286691107735257)
        ·
          refine ⟨36441585718715018330801443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48588780958286691107735257 36441585718715018330801443)
          ·
            refine ⟨54662378578072527496202165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36441585718715018330801443 54662378578072527496202165)
            ·
              refine ⟨5124597991694299452768953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54662378578072527496202165 5124597991694299452768953)
              ·
                refine ⟨3843448493770724589576715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5124597991694299452768953 3843448493770724589576715)
                ·
                  refine ⟨5765172740656086884365073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3843448493770724589576715 5765172740656086884365073)
                  ·
                    refine ⟨4323879555492065163273805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5765172740656086884365073 4323879555492065163273805)
                    ·
                      refine ⟨1621454833309524436227677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4323879555492065163273805 1621454833309524436227677)
                      ·
                        rfl

theorem cell23_3157772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_3157772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157772 prefixEnd_3157772 := by exact prefixLift 3157772
  have htrace : WordTrace (prefixWord ++ tailWord_3157772) baseStart_3157772 baseEnd_3157772 := by
    simpa [prefixWord, tailWord_3157772, baseEnd_3157772] using wordTrace_append hprefix tailTrace_3157772
  have hstable : (prefixWord ++ tailWord_3157772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157772).length < 2 ^ (prefixWord ++ tailWord_3157772).sum := by decide
  have hdescent : baseEnd_3157772 < baseStart_3157772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157855 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 4]
def baseStart_3157855 : Nat := 118140960795 + 3157855 * 2 ^ 59
def prefixEnd_3157855 : Nat := 4983230072969 + 3 ^ 40 * 3157855 * 2
def baseEnd_3157855 : Nat := 1621497452203847611489795

theorem tailTrace_3157855 : CollatzResearch.WordTrace tailWord_3157855 prefixEnd_3157855 1621497452203847611489795 := by
  unfold tailWord_3157855
  simp only [CollatzResearch.WordTrace]
  refine ⟨115176433974638128541755019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76784289316425419027836679 115176433974638128541755019)
  ·
    refine ⟨172764650961957192812632529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115176433974638128541755019 172764650961957192812632529)
    ·
      refine ⟨129573488221467894609474397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172764650961957192812632529 129573488221467894609474397)
      ·
        refine ⟨48590058083050460478552899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129573488221467894609474397 48590058083050460478552899)
        ·
          refine ⟨72885087124575690717829349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48590058083050460478552899 72885087124575690717829349)
          ·
            refine ⟨13665953835857942009593003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72885087124575690717829349 13665953835857942009593003)
            ·
              refine ⟨20498930753786913014389505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13665953835857942009593003 20498930753786913014389505)
              ·
                refine ⟨15374198065340184760792129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20498930753786913014389505 15374198065340184760792129)
                ·
                  refine ⟨11530648549005138570594097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15374198065340184760792129 11530648549005138570594097)
                  ·
                    refine ⟨8647986411753853927945573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11530648549005138570594097 8647986411753853927945573)
                    ·
                      refine ⟨1621497452203847611489795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8647986411753853927945573 1621497452203847611489795)
                      ·
                        rfl

theorem cell23_3157855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_3157855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157855 prefixEnd_3157855 := by exact prefixLift 3157855
  have htrace : WordTrace (prefixWord ++ tailWord_3157855) baseStart_3157855 baseEnd_3157855 := by
    simpa [prefixWord, tailWord_3157855, baseEnd_3157855] using wordTrace_append hprefix tailTrace_3157855
  have hstable : (prefixWord ++ tailWord_3157855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157855).length < 2 ^ (prefixWord ++ tailWord_3157855).sum := by decide
  have hdescent : baseEnd_3157855 < baseStart_3157855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157916 : List Nat := [2, 2, 3, 3, 1, 2, 3, 2, 5]
def baseStart_3157916 : Nat := 118140960795 + 3157916 * 2 ^ 59
def prefixEnd_3157916 : Nat := 4983230072969 + 3 ^ 40 * 3157916 * 2
def baseEnd_3157916 : Nat := 180169863835974652536335

theorem tailTrace_3157916 : CollatzResearch.WordTrace tailWord_3157916 prefixEnd_3157916 180169863835974652536335 := by
  unfold tailWord_3157916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57589329413708567979862801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76785772551611423973150401 57589329413708567979862801)
  ·
    refine ⟨43191997060281425984897101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57589329413708567979862801 43191997060281425984897101)
    ·
      refine ⟨16196998897605534744336413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43191997060281425984897101 16196998897605534744336413)
      ·
        refine ⟨6073874586602075529126155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16196998897605534744336413 6073874586602075529126155)
        ·
          refine ⟨9110811879903113293689233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6073874586602075529126155 9110811879903113293689233)
          ·
            refine ⟨6833108909927334970266925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110811879903113293689233 6833108909927334970266925)
            ·
              refine ⟨2562415841222750613850097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6833108909927334970266925 2562415841222750613850097)
              ·
                refine ⟨1921811880917062960387573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562415841222750613850097 1921811880917062960387573)
                ·
                  refine ⟨180169863835974652536335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1921811880917062960387573 180169863835974652536335)
                  ·
                    rfl

theorem cell23_3157916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_3157916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157916 prefixEnd_3157916 := by exact prefixLift 3157916
  have htrace : WordTrace (prefixWord ++ tailWord_3157916) baseStart_3157916 baseEnd_3157916 := by
    simpa [prefixWord, tailWord_3157916, baseEnd_3157916] using wordTrace_append hprefix tailTrace_3157916
  have hstable : (prefixWord ++ tailWord_3157916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157916).length < 2 ^ (prefixWord ++ tailWord_3157916).sum := by decide
  have hdescent : baseEnd_3157916 < baseStart_3157916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157949 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 4]
def baseStart_3157949 : Nat := 118140960795 + 3157949 * 2 ^ 59
def prefixEnd_3157949 : Nat := 4983230072969 + 3 ^ 40 * 3157949 * 2
def baseEnd_3157949 : Nat := 1621545719385370243714363

theorem tailTrace_3157949 : CollatzResearch.WordTrace tailWord_3157949 prefixEnd_3157949 1621545719385370243714363 := by
  unfold tailWord_3157949
  simp only [CollatzResearch.WordTrace]
  refine ⟨115179862436297582595676901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76786574957531721730451267 115179862436297582595676901)
  ·
    refine ⟨21596224206805796736689419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115179862436297582595676901 21596224206805796736689419)
    ·
      refine ⟨32394336310208695105034129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21596224206805796736689419 32394336310208695105034129)
      ·
        refine ⟨24295752232656521328775597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32394336310208695105034129 24295752232656521328775597)
        ·
          refine ⟨9110907087246195498290849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24295752232656521328775597 9110907087246195498290849)
          ·
            refine ⟨6833180315434646623718137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9110907087246195498290849 6833180315434646623718137)
            ·
              refine ⟨5124885236575984967788603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6833180315434646623718137 5124885236575984967788603)
              ·
                refine ⟨7687327854863977451682905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5124885236575984967788603 7687327854863977451682905)
                ·
                  refine ⟨5765495891147983088762179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7687327854863977451682905 5765495891147983088762179)
                  ·
                    refine ⟨8648243836721974633143269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5765495891147983088762179 8648243836721974633143269)
                    ·
                      refine ⟨1621545719385370243714363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8648243836721974633143269 1621545719385370243714363)
                      ·
                        rfl

theorem cell23_3157949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_3157949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157949 prefixEnd_3157949 := by exact prefixLift 3157949
  have htrace : WordTrace (prefixWord ++ tailWord_3157949) baseStart_3157949 baseEnd_3157949 := by
    simpa [prefixWord, tailWord_3157949, baseEnd_3157949] using wordTrace_append hprefix tailTrace_3157949
  have hstable : (prefixWord ++ tailWord_3157949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157949).length < 2 ^ (prefixWord ++ tailWord_3157949).sum := by decide
  have hdescent : baseEnd_3157949 < baseStart_3157949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157959 : List Nat := [1, 1, 4, 1, 1, 2, 1, 7, 1, 4]
def baseStart_3157959 : Nat := 118140960795 + 3157959 * 2 ^ 59
def prefixEnd_3157959 : Nat := 4983230072969 + 3 ^ 40 * 3157959 * 2
def baseEnd_3157959 : Nat := 540516951397305068196439

theorem tailTrace_3157959 : CollatzResearch.WordTrace tailWord_3157959 prefixEnd_3157959 540516951397305068196439 := by
  unfold tailWord_3157959
  simp only [CollatzResearch.WordTrace]
  refine ⟨115180227166261354303540931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76786818110840902869027287 115180227166261354303540931)
  ·
    refine ⟨172770340749392031455311397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115180227166261354303540931 172770340749392031455311397)
    ·
      refine ⟨32394438890511005897870887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172770340749392031455311397 32394438890511005897870887)
      ·
        refine ⟨48591658335766508846806331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32394438890511005897870887 48591658335766508846806331)
        ·
          refine ⟨72887487503649763270209497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48591658335766508846806331 72887487503649763270209497)
          ·
            refine ⟨54665615627737322452657123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72887487503649763270209497 54665615627737322452657123)
            ·
              refine ⟨81998423441605983678985685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54665615627737322452657123 81998423441605983678985685)
              ·
                refine ⟨1921838049412640242476227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 81998423441605983678985685 1921838049412640242476227)
                ·
                  refine ⟨2882757074118960363714341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1921838049412640242476227 2882757074118960363714341)
                  ·
                    refine ⟨540516951397305068196439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882757074118960363714341 540516951397305068196439)
                    ·
                      rfl

theorem cell23_3157959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_3157959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157959 prefixEnd_3157959 := by exact prefixLift 3157959
  have htrace : WordTrace (prefixWord ++ tailWord_3157959) baseStart_3157959 baseEnd_3157959 := by
    simpa [prefixWord, tailWord_3157959, baseEnd_3157959] using wordTrace_append hprefix tailTrace_3157959
  have hstable : (prefixWord ++ tailWord_3157959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157959).length < 2 ^ (prefixWord ++ tailWord_3157959).sum := by decide
  have hdescent : baseEnd_3157959 < baseStart_3157959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157975 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_3157975 : Nat := 118140960795 + 3157975 * 2 ^ 59
def prefixEnd_3157975 : Nat := 4983230072969 + 3 ^ 40 * 3157975 * 2
def baseEnd_3157975 : Nat := 1621559069882387141989243

theorem tailTrace_3157975 : CollatzResearch.WordTrace tailWord_3157975 prefixEnd_3157975 1621559069882387141989243 := by
  unfold tailWord_3157975
  simp only [CollatzResearch.WordTrace]
  refine ⟨115180810734203389036123379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76787207156135592690748919 115180810734203389036123379)
  ·
    refine ⟨172771216101305083554185069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115180810734203389036123379 172771216101305083554185069)
    ·
      refine ⟨64789206037989406332819401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172771216101305083554185069 64789206037989406332819401)
      ·
        refine ⟨48591904528492054749614551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64789206037989406332819401 48591904528492054749614551)
        ·
          refine ⟨72887856792738082124421827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48591904528492054749614551 72887856792738082124421827)
          ·
            refine ⟨109331785189107123186632741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72887856792738082124421827 109331785189107123186632741)
            ·
              refine ⟨20499709722957585597493639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109331785189107123186632741 20499709722957585597493639)
              ·
                refine ⟨30749564584436378396240459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20499709722957585597493639 30749564584436378396240459)
                ·
                  refine ⟨46124346876654567594360689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30749564584436378396240459 46124346876654567594360689)
                  ·
                    refine ⟨34593260157490925695770517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46124346876654567594360689 34593260157490925695770517)
                    ·
                      refine ⟨1621559069882387141989243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34593260157490925695770517 1621559069882387141989243)
                      ·
                        rfl

theorem cell23_3157975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_3157975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157975 prefixEnd_3157975 := by exact prefixLift 3157975
  have htrace : WordTrace (prefixWord ++ tailWord_3157975) baseStart_3157975 baseEnd_3157975 := by
    simpa [prefixWord, tailWord_3157975, baseEnd_3157975] using wordTrace_append hprefix tailTrace_3157975
  have hstable : (prefixWord ++ tailWord_3157975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157975).length < 2 ^ (prefixWord ++ tailWord_3157975).sum := by decide
  have hdescent : baseEnd_3157975 < baseStart_3157975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3157999 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 3]
def baseStart_3157999 : Nat := 118140960795 + 3157999 * 2 ^ 59
def prefixEnd_3157999 : Nat := 4983230072969 + 3 ^ 40 * 3157999 * 2
def baseEnd_3157999 : Nat := 1621571393418095048089133

theorem tailTrace_3157999 : CollatzResearch.WordTrace tailWord_3157999 prefixEnd_3157999 1621571393418095048089133 := by
  unfold tailWord_3157999
  simp only [CollatzResearch.WordTrace]
  refine ⟨115181686086116441134997051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76787790724077627423331367 115181686086116441134997051)
  ·
    refine ⟨172772529129174661702495577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115181686086116441134997051 172772529129174661702495577)
    ·
      refine ⟨129579396846880996276871683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172772529129174661702495577 129579396846880996276871683)
      ·
        refine ⟨194369095270321494415307525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129579396846880996276871683 194369095270321494415307525)
        ·
          refine ⟨36444205363185280202870161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194369095270321494415307525 36444205363185280202870161)
          ·
            refine ⟨27333154022388960152152621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36444205363185280202870161 27333154022388960152152621)
            ·
              refine ⟨10249932758395860057057233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27333154022388960152152621 10249932758395860057057233)
              ·
                refine ⟨7687449568796895042792925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10249932758395860057057233 7687449568796895042792925)
                ·
                  refine ⟨2882793588298835641047347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7687449568796895042792925 2882793588298835641047347)
                  ·
                    refine ⟨4324190382448253461571021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882793588298835641047347 4324190382448253461571021)
                    ·
                      refine ⟨1621571393418095048089133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4324190382448253461571021 1621571393418095048089133)
                      ·
                        rfl

theorem cell23_3157999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_3157999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3157999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3157999 prefixEnd_3157999 := by exact prefixLift 3157999
  have htrace : WordTrace (prefixWord ++ tailWord_3157999) baseStart_3157999 baseEnd_3157999 := by
    simpa [prefixWord, tailWord_3157999, baseEnd_3157999] using wordTrace_append hprefix tailTrace_3157999
  have hstable : (prefixWord ++ tailWord_3157999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3157999).length < 2 ^ (prefixWord ++ tailWord_3157999).sum := by decide
  have hdescent : baseEnd_3157999 < baseStart_3157999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3157999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158009 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 1, 5, 2]
def baseStart_3158009 : Nat := 118140960795 + 3158009 * 2 ^ 59
def prefixEnd_3158009 : Nat := 4983230072969 + 3 ^ 40 * 3158009 * 2
def baseEnd_3158009 : Nat := 1621576528224640008964087

theorem tailTrace_3158009 : CollatzResearch.WordTrace tailWord_3158009 prefixEnd_3158009 1621576528224640008964087 := by
  unfold tailWord_3158009
  simp only [CollatzResearch.WordTrace]
  refine ⟨115182050816080212842861081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76788033877386808561907387 115182050816080212842861081)
  ·
    refine ⟨86386538112060159632145811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115182050816080212842861081 86386538112060159632145811)
    ·
      refine ⟨129579807168090239448218717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86386538112060159632145811 129579807168090239448218717)
      ·
        refine ⟨48592427688033839793082019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129579807168090239448218717 48592427688033839793082019)
        ·
          refine ⟨72888641532050759689623029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48592427688033839793082019 72888641532050759689623029)
          ·
            refine ⟨6833310143629758720902159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72888641532050759689623029 6833310143629758720902159)
            ·
              refine ⟨10249965215444638081353239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833310143629758720902159 10249965215444638081353239)
              ·
                refine ⟨15374947823166957122029859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10249965215444638081353239 15374947823166957122029859)
                ·
                  refine ⟨23062421734750435683044789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15374947823166957122029859 23062421734750435683044789)
                  ·
                    refine ⟨2162102037632853345285449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23062421734750435683044789 2162102037632853345285449)
                    ·
                      refine ⟨1621576528224640008964087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162102037632853345285449 1621576528224640008964087)
                      ·
                        rfl

theorem cell23_3158009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_3158009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158009 prefixEnd_3158009 := by exact prefixLift 3158009
  have htrace : WordTrace (prefixWord ++ tailWord_3158009) baseStart_3158009 baseEnd_3158009 := by
    simpa [prefixWord, tailWord_3158009, baseEnd_3158009] using wordTrace_append hprefix tailTrace_3158009
  have hstable : (prefixWord ++ tailWord_3158009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158009).length < 2 ^ (prefixWord ++ tailWord_3158009).sum := by decide
  have hdescent : baseEnd_3158009 < baseStart_3158009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158032 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 4, 4]
def baseStart_3158032 : Nat := 118140960795 + 3158032 * 2 ^ 59
def prefixEnd_3158032 : Nat := 4983230072969 + 3 ^ 40 * 3158032 * 2
def baseEnd_3158032 : Nat := 540529446093231139658827

theorem tailTrace_3158032 : CollatzResearch.WordTrace tailWord_3158032 prefixEnd_3158032 540529446093231139658827 := by
  unfold tailWord_3158032
  simp only [CollatzResearch.WordTrace]
  refine ⟨57591444847498443885474175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76788593129997925180632233 57591444847498443885474175)
  ·
    refine ⟨86387167271247665828211263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57591444847498443885474175 86387167271247665828211263)
    ·
      refine ⟨129580750906871498742316895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86387167271247665828211263 129580750906871498742316895)
      ·
        refine ⟨194371126360307248113475343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129580750906871498742316895 194371126360307248113475343)
        ·
          refine ⟨291556689540460872170213015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194371126360307248113475343 291556689540460872170213015)
          ·
            refine ⟨437335034310691308255319523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291556689540460872170213015 437335034310691308255319523)
            ·
              refine ⟨656002551466036962382979285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437335034310691308255319523 656002551466036962382979285)
              ·
                refine ⟨15375059799985241305851077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 656002551466036962382979285 15375059799985241305851077)
                ·
                  refine ⟨2882823712497232744847077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15375059799985241305851077 2882823712497232744847077)
                  ·
                    refine ⟨540529446093231139658827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2882823712497232744847077 540529446093231139658827)
                    ·
                      rfl

theorem cell23_3158032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 4, 4].length) (baseStart_3158032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158032 prefixEnd_3158032 := by exact prefixLift 3158032
  have htrace : WordTrace (prefixWord ++ tailWord_3158032) baseStart_3158032 baseEnd_3158032 := by
    simpa [prefixWord, tailWord_3158032, baseEnd_3158032] using wordTrace_append hprefix tailTrace_3158032
  have hstable : (prefixWord ++ tailWord_3158032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158032).length < 2 ^ (prefixWord ++ tailWord_3158032).sum := by decide
  have hdescent : baseEnd_3158032 < baseStart_3158032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158042 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5]
def baseStart_3158042 : Nat := 118140960795 + 3158042 * 2 ^ 59
def prefixEnd_3158042 : Nat := 4983230072969 + 3 ^ 40 * 3158042 * 2
def baseEnd_3158042 : Nat := 1621593473086238379851435

theorem tailTrace_3158042 : CollatzResearch.WordTrace tailWord_3158042 prefixEnd_3158042 1621593473086238379851435 := by
  unfold tailWord_3158042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28795813606240164869703095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76788836283307106319208253 28795813606240164869703095)
  ·
    refine ⟨43193720409360247304554643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28795813606240164869703095 43193720409360247304554643)
    ·
      refine ⟨64790580614040370956831965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43193720409360247304554643 64790580614040370956831965)
      ·
        refine ⟨24296467730265139108811987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64790580614040370956831965 24296467730265139108811987)
        ·
          refine ⟨36444701595397708663217981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24296467730265139108811987 36444701595397708663217981)
          ·
            refine ⟨13666763098274140748706743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36444701595397708663217981 13666763098274140748706743)
            ·
              refine ⟨20500144647411211123060115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13666763098274140748706743 20500144647411211123060115)
              ·
                refine ⟨30750216971116816684590173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20500144647411211123060115 30750216971116816684590173)
                ·
                  refine ⟨11531331364168806256721315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30750216971116816684590173 11531331364168806256721315)
                  ·
                    refine ⟨17296997046253209385081973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11531331364168806256721315 17296997046253209385081973)
                    ·
                      refine ⟨1621593473086238379851435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17296997046253209385081973 1621593473086238379851435)
                      ·
                        rfl

theorem cell23_3158042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_3158042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158042 prefixEnd_3158042 := by exact prefixLift 3158042
  have htrace : WordTrace (prefixWord ++ tailWord_3158042) baseStart_3158042 baseEnd_3158042 := by
    simpa [prefixWord, tailWord_3158042, baseEnd_3158042] using wordTrace_append hprefix tailTrace_3158042
  have hstable : (prefixWord ++ tailWord_3158042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158042).length < 2 ^ (prefixWord ++ tailWord_3158042).sum := by decide
  have hdescent : baseEnd_3158042 < baseStart_3158042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158089 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 3]
def baseStart_3158089 : Nat := 118140960795 + 3158089 * 2 ^ 59
def prefixEnd_3158089 : Nat := 4983230072969 + 3 ^ 40 * 3158089 * 2
def baseEnd_3158089 : Nat := 1621617606676999695963719

theorem tailTrace_3158089 : CollatzResearch.WordTrace tailWord_3158089 prefixEnd_3158089 1621617606676999695963719 := by
  unfold tailWord_3158089
  simp only [CollatzResearch.WordTrace]
  refine ⟨115184968655790386505773321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76789979103860257670515547 115184968655790386505773321)
  ·
    refine ⟨86388726491842789879329991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115184968655790386505773321 86388726491842789879329991)
    ·
      refine ⟨129583089737764184818994987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86388726491842789879329991 129583089737764184818994987)
      ·
        refine ⟨194374634606646277228492481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129583089737764184818994987 194374634606646277228492481)
        ·
          refine ⟨145780975954984707921369361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194374634606646277228492481 145780975954984707921369361)
          ·
            refine ⟨109335731966238530941027021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145780975954984707921369361 109335731966238530941027021)
            ·
              refine ⟨41000899487339449102885133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109335731966238530941027021 41000899487339449102885133)
              ·
                refine ⟨15375337307752293413581925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41000899487339449102885133 15375337307752293413581925)
                ·
                  refine ⟨2882875745203555015046611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15375337307752293413581925 2882875745203555015046611)
                  ·
                    refine ⟨4324313617805332522569917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882875745203555015046611 4324313617805332522569917)
                    ·
                      refine ⟨1621617606676999695963719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4324313617805332522569917 1621617606676999695963719)
                      ·
                        rfl

theorem cell23_3158089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 1, 3].length) (baseStart_3158089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158089 prefixEnd_3158089 := by exact prefixLift 3158089
  have htrace : WordTrace (prefixWord ++ tailWord_3158089) baseStart_3158089 baseEnd_3158089 := by
    simpa [prefixWord, tailWord_3158089, baseEnd_3158089] using wordTrace_append hprefix tailTrace_3158089
  have hstable : (prefixWord ++ tailWord_3158089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158089).length < 2 ^ (prefixWord ++ tailWord_3158089).sum := by decide
  have hdescent : baseEnd_3158089 < baseStart_3158089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158106 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3]
def baseStart_3158106 : Nat := 118140960795 + 3158106 * 2 ^ 59
def prefixEnd_3158106 : Nat := 4983230072969 + 3 ^ 40 * 3158106 * 2
def baseEnd_3158106 : Nat := 1621626335848126129451141

theorem tailTrace_3158106 : CollatzResearch.WordTrace tailWord_3158106 prefixEnd_3158106 1621626335848126129451141 := by
  unfold tailWord_3158106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28796397174182199602285543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76790392464485865606094781 28796397174182199602285543)
  ·
    refine ⟨43194595761273299403428315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28796397174182199602285543 43194595761273299403428315)
    ·
      refine ⟨64791893641909949105142473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43194595761273299403428315 64791893641909949105142473)
      ·
        refine ⟨48593920231432461828856855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64791893641909949105142473 48593920231432461828856855)
        ·
          refine ⟨72890880347148692743285283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48593920231432461828856855 72890880347148692743285283)
          ·
            refine ⟨109336320520723039114927925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72890880347148692743285283 109336320520723039114927925)
            ·
              refine ⟨10250280048817784917024493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109336320520723039114927925 10250280048817784917024493)
              ·
                refine ⟨3843855018306669343884185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10250280048817784917024493 3843855018306669343884185)
                ·
                  refine ⟨2882891263730002007913139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3843855018306669343884185 2882891263730002007913139)
                  ·
                    refine ⟨4324336895595003011869709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2882891263730002007913139 4324336895595003011869709)
                    ·
                      refine ⟨1621626335848126129451141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4324336895595003011869709 1621626335848126129451141)
                      ·
                        rfl

theorem cell23_3158106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_3158106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158106 prefixEnd_3158106 := by exact prefixLift 3158106
  have htrace : WordTrace (prefixWord ++ tailWord_3158106) baseStart_3158106 baseEnd_3158106 := by
    simpa [prefixWord, tailWord_3158106, baseEnd_3158106] using wordTrace_append hprefix tailTrace_3158106
  have hstable : (prefixWord ++ tailWord_3158106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158106).length < 2 ^ (prefixWord ++ tailWord_3158106).sum := by decide
  have hdescent : baseEnd_3158106 < baseStart_3158106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158110 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_3158110 : Nat := 118140960795 + 3158110 * 2 ^ 59
def prefixEnd_3158110 : Nat := 4983230072969 + 3 ^ 40 * 3158110 * 2
def baseEnd_3158110 : Nat := 1621628389770744113801123

theorem tailTrace_3158110 : CollatzResearch.WordTrace tailWord_3158110 prefixEnd_3158110 1621628389770744113801123 := by
  unfold tailWord_3158110
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398216823589288386535973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76790489725809538061525189 14398216823589288386535973)
  ·
    refine ⟨2699665654422991572475495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14398216823589288386535973 2699665654422991572475495)
    ·
      refine ⟨4049498481634487358713243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699665654422991572475495 4049498481634487358713243)
      ·
        refine ⟨6074247722451731038069865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049498481634487358713243 6074247722451731038069865)
        ·
          refine ⟨4555685791838798278552399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074247722451731038069865 4555685791838798278552399)
          ·
            refine ⟨6833528687758197417828599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555685791838798278552399 6833528687758197417828599)
            ·
              refine ⟨10250293031637296126742899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833528687758197417828599 10250293031637296126742899)
              ·
                refine ⟨15375439547455944190114349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10250293031637296126742899 15375439547455944190114349)
                ·
                  refine ⟨5765789830295979071292881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15375439547455944190114349 5765789830295979071292881)
                  ·
                    refine ⟨4324342372721984303469661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5765789830295979071292881 4324342372721984303469661)
                    ·
                      refine ⟨1621628389770744113801123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4324342372721984303469661 1621628389770744113801123)
                      ·
                        rfl

theorem cell23_3158110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_3158110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158110 prefixEnd_3158110 := by exact prefixLift 3158110
  have htrace : WordTrace (prefixWord ++ tailWord_3158110) baseStart_3158110 baseEnd_3158110 := by
    simpa [prefixWord, tailWord_3158110, baseEnd_3158110] using wordTrace_append hprefix tailTrace_3158110
  have hstable : (prefixWord ++ tailWord_3158110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158110).length < 2 ^ (prefixWord ++ tailWord_3158110).sum := by decide
  have hdescent : baseEnd_3158110 < baseStart_3158110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158149 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_3158149 : Nat := 118140960795 + 3158149 * 2 ^ 59
def prefixEnd_3158149 : Nat := 4983230072969 + 3 ^ 40 * 3158149 * 2
def baseEnd_3158149 : Nat := 1621648415516269461213443

theorem tailTrace_3158149 : CollatzResearch.WordTrace tailWord_3158149 prefixEnd_3158149 1621648415516269461213443 := by
  unfold tailWord_3158149
  simp only [CollatzResearch.WordTrace]
  refine ⟨115187157035573016752957501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76791438023715344501971667 115187157035573016752957501)
  ·
    refine ⟨43195183888339881282359063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115187157035573016752957501 43195183888339881282359063)
    ·
      refine ⟨64792775832509821923538595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43195183888339881282359063 64792775832509821923538595)
      ·
        refine ⟨97189163748764732885307893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64792775832509821923538595 97189163748764732885307893)
        ·
          refine ⟨9111484101446693707997615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97189163748764732885307893 9111484101446693707997615)
          ·
            refine ⟨13667226152170040561996423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9111484101446693707997615 13667226152170040561996423)
            ·
              refine ⟨20500839228255060842994635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13667226152170040561996423 20500839228255060842994635)
              ·
                refine ⟨30751258842382591264491953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20500839228255060842994635 30751258842382591264491953)
                ·
                  refine ⟨23063444131786943448368965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30751258842382591264491953 23063444131786943448368965)
                  ·
                    refine ⟨4324395774710051896569181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23063444131786943448368965 4324395774710051896569181)
                    ·
                      refine ⟨1621648415516269461213443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4324395774710051896569181 1621648415516269461213443)
                      ·
                        rfl

theorem cell23_3158149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_3158149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158149 prefixEnd_3158149 := by exact prefixLift 3158149
  have htrace : WordTrace (prefixWord ++ tailWord_3158149) baseStart_3158149 baseEnd_3158149 := by
    simpa [prefixWord, tailWord_3158149, baseEnd_3158149] using wordTrace_append hprefix tailTrace_3158149
  have hstable : (prefixWord ++ tailWord_3158149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158149).length < 2 ^ (prefixWord ++ tailWord_3158149).sum := by decide
  have hdescent : baseEnd_3158149 < baseStart_3158149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158253 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 4]
def baseStart_3158253 : Nat := 118140960795 + 3158253 * 2 ^ 59
def prefixEnd_3158253 : Nat := 4983230072969 + 3 ^ 40 * 3158253 * 2
def baseEnd_3158253 : Nat := 1621701817504337054312965

theorem tailTrace_3158253 : CollatzResearch.WordTrace tailWord_3158253 prefixEnd_3158253 1621701817504337054312965 := by
  unfold tailWord_3158253
  simp only [CollatzResearch.WordTrace]
  refine ⟨115190950227196242514743413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76793966818130828343162275 115190950227196242514743413)
  ·
    refine ⟨10799151583799647735757195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115190950227196242514743413 10799151583799647735757195)
    ·
      refine ⟨16198727375699471603635793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799151583799647735757195 16198727375699471603635793)
      ·
        refine ⟨12149045531774603702726845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16198727375699471603635793 12149045531774603702726845)
        ·
          refine ⟨4555892074415476388522567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12149045531774603702726845 4555892074415476388522567)
          ·
            refine ⟨6833838111623214582783851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555892074415476388522567 6833838111623214582783851)
            ·
              refine ⟨10250757167434821874175777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6833838111623214582783851 10250757167434821874175777)
              ·
                refine ⟨7688067875576116405631833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10250757167434821874175777 7688067875576116405631833)
                ·
                  refine ⟨5766050906682087304223875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7688067875576116405631833 5766050906682087304223875)
                  ·
                    refine ⟨8649076360023130956335813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766050906682087304223875 8649076360023130956335813)
                    ·
                      refine ⟨1621701817504337054312965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8649076360023130956335813 1621701817504337054312965)
                      ·
                        rfl

theorem cell23_3158253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_3158253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158253 prefixEnd_3158253 := by exact prefixLift 3158253
  have htrace : WordTrace (prefixWord ++ tailWord_3158253) baseStart_3158253 baseEnd_3158253 := by
    simpa [prefixWord, tailWord_3158253, baseEnd_3158253] using wordTrace_append hprefix tailTrace_3158253
  have hstable : (prefixWord ++ tailWord_3158253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158253).length < 2 ^ (prefixWord ++ tailWord_3158253).sum := by decide
  have hdescent : baseEnd_3158253 < baseStart_3158253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158259 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 6]
def baseStart_3158259 : Nat := 118140960795 + 3158259 * 2 ^ 59
def prefixEnd_3158259 : Nat := 4983230072969 + 3 ^ 40 * 3158259 * 2
def baseEnd_3158259 : Nat := 180189433154251558981993

theorem tailTrace_3158259 : CollatzResearch.WordTrace tailWord_3158259 prefixEnd_3158259 180189433154251558981993 := by
  unfold tailWord_3158259
  simp only [CollatzResearch.WordTrace]
  refine ⟨115191169065174505539461831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76794112710116337026307887 115191169065174505539461831)
  ·
    refine ⟨172786753597761758309192747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115191169065174505539461831 172786753597761758309192747)
    ·
      refine ⟨259180130396642637463789121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172786753597761758309192747 259180130396642637463789121)
      ·
        refine ⟨194385097797481978097841841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259180130396642637463789121 194385097797481978097841841)
        ·
          refine ⟨145788823348111483573381381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194385097797481978097841841 145788823348111483573381381)
          ·
            refine ⟨27335404377770903170009009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145788823348111483573381381 27335404377770903170009009)
            ·
              refine ⟨20501553283328177377506757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27335404377770903170009009 20501553283328177377506757)
              ·
                refine ⟨3844041240624033258282517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20501553283328177377506757 3844041240624033258282517)
                ·
                  refine ⟨180189433154251558981993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3844041240624033258282517 180189433154251558981993)
                  ·
                    rfl

theorem cell23_3158259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 6].length) (baseStart_3158259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158259 prefixEnd_3158259 := by exact prefixLift 3158259
  have htrace : WordTrace (prefixWord ++ tailWord_3158259) baseStart_3158259 baseEnd_3158259 := by
    simpa [prefixWord, tailWord_3158259, baseEnd_3158259] using wordTrace_append hprefix tailTrace_3158259
  have hstable : (prefixWord ++ tailWord_3158259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158259).length < 2 ^ (prefixWord ++ tailWord_3158259).sum := by decide
  have hdescent : baseEnd_3158259 < baseStart_3158259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158314 : List Nat := [3, 1, 4, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3158314 : Nat := 118140960795 + 3158314 * 2 ^ 59
def prefixEnd_3158314 : Nat := 4983230072969 + 3 ^ 40 * 3158314 * 2
def baseEnd_3158314 : Nat := 540577713274753771883395

theorem tailTrace_3158314 : CollatzResearch.WordTrace tailWord_3158314 prefixEnd_3158314 540577713274753771883395 := by
  unfold tailWord_3158314
  simp only [CollatzResearch.WordTrace]
  refine ⟨28798293769993812483178499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76795450053316833288475997 28798293769993812483178499)
  ·
    refine ⟨43197440654990718724767749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28798293769993812483178499 43197440654990718724767749)
    ·
      refine ⟨8099520122810759760893953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43197440654990718724767749 8099520122810759760893953)
      ·
        refine ⟨6074640092108069820670465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8099520122810759760893953 6074640092108069820670465)
        ·
          refine ⟨4555980069081052365502849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074640092108069820670465 4555980069081052365502849)
          ·
            refine ⟨3416985051810789274127137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4555980069081052365502849 3416985051810789274127137)
            ·
              refine ⟨2562738788858091955595353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3416985051810789274127137 2562738788858091955595353)
              ·
                refine ⟨1922054091643568966696515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2562738788858091955595353 1922054091643568966696515)
                ·
                  refine ⟨2883081137465353450044773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922054091643568966696515 2883081137465353450044773)
                  ·
                    refine ⟨540577713274753771883395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883081137465353450044773 540577713274753771883395)
                    ·
                      rfl

theorem cell23_3158314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3158314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158314 prefixEnd_3158314 := by exact prefixLift 3158314
  have htrace : WordTrace (prefixWord ++ tailWord_3158314) baseStart_3158314 baseEnd_3158314 := by
    simpa [prefixWord, tailWord_3158314, baseEnd_3158314] using wordTrace_append hprefix tailTrace_3158314
  have hstable : (prefixWord ++ tailWord_3158314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158314).length < 2 ^ (prefixWord ++ tailWord_3158314).sum := by decide
  have hdescent : baseEnd_3158314 < baseStart_3158314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158339 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6]
def baseStart_3158339 : Nat := 118140960795 + 3158339 * 2 ^ 59
def prefixEnd_3158339 : Nat := 4983230072969 + 3 ^ 40 * 3158339 * 2
def baseEnd_3158339 : Nat := 1621745976840623717837569

theorem tailTrace_3158339 : CollatzResearch.WordTrace tailWord_3158339 prefixEnd_3158339 1621745976840623717837569 := by
  unfold tailWord_3158339
  simp only [CollatzResearch.WordTrace]
  refine ⟨115194086904884679202374071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76796057936589786134916047 115194086904884679202374071)
  ·
    refine ⟨172791130357327018803561107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115194086904884679202374071 172791130357327018803561107)
    ·
      refine ⟨259186695535990528205341661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172791130357327018803561107 259186695535990528205341661)
      ·
        refine ⟨97195010825996448077003123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259186695535990528205341661 97195010825996448077003123)
        ·
          refine ⟨145792516238994672115504685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97195010825996448077003123 145792516238994672115504685)
          ·
            refine ⟨54672193589623002043314257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145792516238994672115504685 54672193589623002043314257)
            ·
              refine ⟨41004145192217251532485693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54672193589623002043314257 41004145192217251532485693)
              ·
                refine ⟨15376554447081469324682135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41004145192217251532485693 15376554447081469324682135)
                ·
                  refine ⟨23064831670622203987023203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15376554447081469324682135 23064831670622203987023203)
                  ·
                    refine ⟨34597247505933305980534805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23064831670622203987023203 34597247505933305980534805)
                    ·
                      refine ⟨1621745976840623717837569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34597247505933305980534805 1621745976840623717837569)
                      ·
                        rfl

theorem cell23_3158339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_3158339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158339 prefixEnd_3158339 := by exact prefixLift 3158339
  have htrace : WordTrace (prefixWord ++ tailWord_3158339) baseStart_3158339 baseEnd_3158339 := by
    simpa [prefixWord, tailWord_3158339, baseEnd_3158339] using wordTrace_append hprefix tailTrace_3158339
  have hstable : (prefixWord ++ tailWord_3158339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158339).length < 2 ^ (prefixWord ++ tailWord_3158339).sum := by decide
  have hdescent : baseEnd_3158339 < baseStart_3158339 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158357 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 1, 5]
def baseStart_3158357 : Nat := 118140960795 + 3158357 * 2 ^ 59
def prefixEnd_3158357 : Nat := 4983230072969 + 3 ^ 40 * 3158357 * 2
def baseEnd_3158357 : Nat := 540585073164134882470829

theorem tailTrace_3158357 : CollatzResearch.WordTrace tailWord_3158357 prefixEnd_3158357 540585073164134882470829 := by
  unfold tailWord_3158357
  simp only [CollatzResearch.WordTrace]
  refine ⟨115194743418819468276529325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76796495612546312184352883 115194743418819468276529325)
  ·
    refine ⟨43198028782057300603698497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115194743418819468276529325 43198028782057300603698497)
    ·
      refine ⟨32398521586542975452773873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43198028782057300603698497 32398521586542975452773873)
      ·
        refine ⟨24298891189907231589580405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32398521586542975452773873 24298891189907231589580405)
        ·
          refine ⟨2278021049053802961523163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24298891189907231589580405 2278021049053802961523163)
          ·
            refine ⟨3417031573580704442284745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278021049053802961523163 3417031573580704442284745)
            ·
              refine ⟨2562773680185528331713559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417031573580704442284745 2562773680185528331713559)
              ·
                refine ⟨3844160520278292497570339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2562773680185528331713559 3844160520278292497570339)
                ·
                  refine ⟨5766240780417438746355509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844160520278292497570339 5766240780417438746355509)
                  ·
                    refine ⟨540585073164134882470829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5766240780417438746355509 540585073164134882470829)
                    ·
                      rfl

theorem cell23_3158357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 1, 5].length) (baseStart_3158357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158357 prefixEnd_3158357 := by exact prefixLift 3158357
  have htrace : WordTrace (prefixWord ++ tailWord_3158357) baseStart_3158357 baseEnd_3158357 := by
    simpa [prefixWord, tailWord_3158357, baseEnd_3158357] using wordTrace_append hprefix tailTrace_3158357
  have hstable : (prefixWord ++ tailWord_3158357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158357).length < 2 ^ (prefixWord ++ tailWord_3158357).sum := by decide
  have hdescent : baseEnd_3158357 < baseStart_3158357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158369 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_3158369 : Nat := 118140960795 + 3158369 * 2 ^ 59
def prefixEnd_3158369 : Nat := 4983230072969 + 3 ^ 40 * 3158369 * 2
def baseEnd_3158369 : Nat := 1621761381260258600462431

theorem tailTrace_3158369 : CollatzResearch.WordTrace tailWord_3158369 prefixEnd_3158369 1621761381260258600462431 := by
  unfold tailWord_3158369
  simp only [CollatzResearch.WordTrace]
  refine ⟨115195181094775994325966161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76796787396517329550644107 115195181094775994325966161)
  ·
    refine ⟨86396385821081995744474621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115195181094775994325966161 86396385821081995744474621)
    ·
      refine ⟨32398644682905748404177983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86396385821081995744474621 32398644682905748404177983)
      ·
        refine ⟨48597967024358622606266975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32398644682905748404177983 48597967024358622606266975)
        ·
          refine ⟨72896950536537933909400463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48597967024358622606266975 72896950536537933909400463)
          ·
            refine ⟨109345425804806900864100695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72896950536537933909400463 109345425804806900864100695)
            ·
              refine ⟨164018138707210351296151043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109345425804806900864100695 164018138707210351296151043)
              ·
                refine ⟨246027208060815526944226565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164018138707210351296151043 246027208060815526944226565)
                ·
                  refine ⟨46130101511402911302042481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246027208060815526944226565 46130101511402911302042481)
                  ·
                    refine ⟨34597576133552183476531861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46130101511402911302042481 34597576133552183476531861)
                    ·
                      refine ⟨1621761381260258600462431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34597576133552183476531861 1621761381260258600462431)
                      ·
                        rfl

theorem cell23_3158369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_3158369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158369 prefixEnd_3158369 := by exact prefixLift 3158369
  have htrace : WordTrace (prefixWord ++ tailWord_3158369) baseStart_3158369 baseEnd_3158369 := by
    simpa [prefixWord, tailWord_3158369, baseEnd_3158369] using wordTrace_append hprefix tailTrace_3158369
  have hstable : (prefixWord ++ tailWord_3158369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158369).length < 2 ^ (prefixWord ++ tailWord_3158369).sum := by decide
  have hdescent : baseEnd_3158369 < baseStart_3158369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158370 : List Nat := [3, 3, 2, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3158370 : Nat := 118140960795 + 3158370 * 2 ^ 59
def prefixEnd_3158370 : Nat := 4983230072969 + 3 ^ 40 * 3158370 * 2
def baseEnd_3158370 : Nat := 540587298246971032183309

theorem tailTrace_3158370 : CollatzResearch.WordTrace tailWord_3158370 prefixEnd_3158370 540587298246971032183309 := by
  unfold tailWord_3158370
  simp only [CollatzResearch.WordTrace]
  refine ⟨28798804391943092874188141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76796811711848247664501709 28798804391943092874188141)
  ·
    refine ⟨10799551646978659827820553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28798804391943092874188141 10799551646978659827820553)
    ·
      refine ⟨8099663735233994870865415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10799551646978659827820553 8099663735233994870865415)
      ·
        refine ⟨12149495602850992306298123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099663735233994870865415 12149495602850992306298123)
        ·
          refine ⟨18224243404276488459447185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12149495602850992306298123 18224243404276488459447185)
          ·
            refine ⟨13668182553207366344585389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18224243404276488459447185 13668182553207366344585389)
            ·
              refine ⟨5125568457452762379219521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13668182553207366344585389 5125568457452762379219521)
              ·
                refine ⟨3844176343089571784414641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5125568457452762379219521 3844176343089571784414641)
                ·
                  refine ⟨2883132257317178838310981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844176343089571784414641 2883132257317178838310981)
                  ·
                    refine ⟨540587298246971032183309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883132257317178838310981 540587298246971032183309)
                    ·
                      rfl

theorem cell23_3158370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3158370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158370 prefixEnd_3158370 := by exact prefixLift 3158370
  have htrace : WordTrace (prefixWord ++ tailWord_3158370) baseStart_3158370 baseEnd_3158370 := by
    simpa [prefixWord, tailWord_3158370, baseEnd_3158370] using wordTrace_append hprefix tailTrace_3158370
  have hstable : (prefixWord ++ tailWord_3158370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158370).length < 2 ^ (prefixWord ++ tailWord_3158370).sum := by decide
  have hdescent : baseEnd_3158370 < baseStart_3158370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158390 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6]
def baseStart_3158390 : Nat := 118140960795 + 3158390 * 2 ^ 59
def prefixEnd_3158390 : Nat := 4983230072969 + 3 ^ 40 * 3158390 * 2
def baseEnd_3158390 : Nat := 1621772164354003018299835

theorem tailTrace_3158390 : CollatzResearch.WordTrace tailWord_3158390 prefixEnd_3158390 1621772164354003018299835 := by
  unfold tailWord_3158390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199746689231244682030039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76797298018466609941653749 7199746689231244682030039)
  ·
    refine ⟨10799620033846867023045059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7199746689231244682030039 10799620033846867023045059)
    ·
      refine ⟨16199430050770300534567589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799620033846867023045059 16199430050770300534567589)
      ·
        refine ⟨3037393134519431350231423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16199430050770300534567589 3037393134519431350231423)
        ·
          refine ⟨4556089701779147025347135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037393134519431350231423 4556089701779147025347135)
          ·
            refine ⟨6834134552668720538020703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556089701779147025347135 6834134552668720538020703)
            ·
              refine ⟨10251201829003080807031055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834134552668720538020703 10251201829003080807031055)
              ·
                refine ⟨15376802743504621210546583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10251201829003080807031055 15376802743504621210546583)
                ·
                  refine ⟨23065204115256931815819875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15376802743504621210546583 23065204115256931815819875)
                  ·
                    refine ⟨34597806172885397723729813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23065204115256931815819875 34597806172885397723729813)
                    ·
                      refine ⟨1621772164354003018299835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34597806172885397723729813 1621772164354003018299835)
                      ·
                        rfl

theorem cell23_3158390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_3158390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158390 prefixEnd_3158390 := by exact prefixLift 3158390
  have htrace : WordTrace (prefixWord ++ tailWord_3158390) baseStart_3158390 baseEnd_3158390 := by
    simpa [prefixWord, tailWord_3158390, baseEnd_3158390] using wordTrace_append hprefix tailTrace_3158390
  have hstable : (prefixWord ++ tailWord_3158390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158390).length < 2 ^ (prefixWord ++ tailWord_3158390).sum := by decide
  have hdescent : baseEnd_3158390 < baseStart_3158390 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158484 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_3158484 : Nat := 118140960795 + 3158484 * 2 ^ 59
def prefixEnd_3158484 : Nat := 4983230072969 + 3 ^ 40 * 3158484 * 2
def baseEnd_3158484 : Nat := 1621820431535525650524403

theorem tailTrace_3158484 : CollatzResearch.WordTrace tailWord_3158484 prefixEnd_3158484 1621820431535525650524403 := by
  unfold tailWord_3158484
  simp only [CollatzResearch.WordTrace]
  refine ⟨57599687744679684483201253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76799583659572912644268337 57599687744679684483201253)
  ·
    refine ⟨10799941452127440840600235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57599687744679684483201253 10799941452127440840600235)
    ·
      refine ⟨16199912178191161260900353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799941452127440840600235 16199912178191161260900353)
      ·
        refine ⟨12149934133643370945675265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16199912178191161260900353 12149934133643370945675265)
        ·
          refine ⟨9112450600232528209256449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12149934133643370945675265 9112450600232528209256449)
          ·
            refine ⟨6834337950174396156942337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9112450600232528209256449 6834337950174396156942337)
            ·
              refine ⟨5125753462630797117706753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6834337950174396156942337 5125753462630797117706753)
              ·
                refine ⟨3844315096973097838280065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5125753462630797117706753 3844315096973097838280065)
                ·
                  refine ⟨2883236322729823378710049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844315096973097838280065 2883236322729823378710049)
                  ·
                    refine ⟨2162427242047367534032537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883236322729823378710049 2162427242047367534032537)
                    ·
                      refine ⟨1621820431535525650524403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162427242047367534032537 1621820431535525650524403)
                      ·
                        rfl

theorem cell23_3158484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_3158484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158484 prefixEnd_3158484 := by exact prefixLift 3158484
  have htrace : WordTrace (prefixWord ++ tailWord_3158484) baseStart_3158484 baseEnd_3158484 := by
    simpa [prefixWord, tailWord_3158484, baseEnd_3158484] using wordTrace_append hprefix tailTrace_3158484
  have hstable : (prefixWord ++ tailWord_3158484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158484).length < 2 ^ (prefixWord ++ tailWord_3158484).sum := by decide
  have hdescent : baseEnd_3158484 < baseStart_3158484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158496 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5]
def baseStart_3158496 : Nat := 118140960795 + 3158496 * 2 ^ 59
def prefixEnd_3158496 : Nat := 4983230072969 + 3 ^ 40 * 3158496 * 2
def baseEnd_3158496 : Nat := 1621826593303379603574347

theorem tailTrace_3158496 : CollatzResearch.WordTrace tailWord_3158496 prefixEnd_3158496 1621826593303379603574347 := by
  unfold tailWord_3158496
  simp only [CollatzResearch.WordTrace]
  refine ⟨57599906582657947507919671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76799875443543930010559561 57599906582657947507919671)
  ·
    refine ⟨86399859873986921261879507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57599906582657947507919671 86399859873986921261879507)
    ·
      refine ⟨129599789810980381892819261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86399859873986921261879507 129599789810980381892819261)
      ·
        refine ⟨48599921179117643209807223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129599789810980381892819261 48599921179117643209807223)
        ·
          refine ⟨72899881768676464814710835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48599921179117643209807223 72899881768676464814710835)
          ·
            refine ⟨109349822653014697222066253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72899881768676464814710835 109349822653014697222066253)
            ·
              refine ⟨41006183494880511458274845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109349822653014697222066253 41006183494880511458274845)
              ·
                refine ⟨15377318810580191796853067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41006183494880511458274845 15377318810580191796853067)
                ·
                  refine ⟨23065978215870287695279601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15377318810580191796853067 23065978215870287695279601)
                  ·
                    refine ⟨17299483661902715771459701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23065978215870287695279601 17299483661902715771459701)
                    ·
                      refine ⟨1621826593303379603574347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17299483661902715771459701 1621826593303379603574347)
                      ·
                        rfl

theorem cell23_3158496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_3158496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158496 prefixEnd_3158496 := by exact prefixLift 3158496
  have htrace : WordTrace (prefixWord ++ tailWord_3158496) baseStart_3158496 baseEnd_3158496 := by
    simpa [prefixWord, tailWord_3158496, baseEnd_3158496] using wordTrace_append hprefix tailTrace_3158496
  have hstable : (prefixWord ++ tailWord_3158496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158496).length < 2 ^ (prefixWord ++ tailWord_3158496).sum := by decide
  have hdescent : baseEnd_3158496 < baseStart_3158496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158523 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 6, 4, 2]
def baseStart_3158523 : Nat := 118140960795 + 3158523 * 2 ^ 59
def prefixEnd_3158523 : Nat := 4983230072969 + 3 ^ 40 * 3158523 * 2
def baseEnd_3158523 : Nat := 1621840457281050997936723

theorem tailTrace_3158523 : CollatzResearch.WordTrace tailWord_3158523 prefixEnd_3158523 1621840457281050997936723 := by
  unfold tailWord_3158523
  simp only [CollatzResearch.WordTrace]
  refine ⟨115200797936218078627072223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76800531957478719084714815 115200797936218078627072223)
  ·
    refine ⟨172801196904327117940608335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115200797936218078627072223 172801196904327117940608335)
    ·
      refine ⟨259201795356490676910912503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172801196904327117940608335 259201795356490676910912503)
      ·
        refine ⟨388802693034736015366368755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259201795356490676910912503 388802693034736015366368755)
        ·
          refine ⟨583204039552104023049553133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388802693034736015366368755 583204039552104023049553133)
          ·
            refine ⟨218701514832039008643582425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 583204039552104023049553133 218701514832039008643582425)
            ·
              refine ⟨164026136124029256482686819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218701514832039008643582425 164026136124029256482686819)
              ·
                refine ⟨246039204186043884724030229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164026136124029256482686819 246039204186043884724030229)
                ·
                  refine ⟨11533087696220807096438917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 246039204186043884724030229 11533087696220807096438917)
                  ·
                    refine ⟨2162453943041401330582297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11533087696220807096438917 2162453943041401330582297)
                    ·
                      refine ⟨1621840457281050997936723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162453943041401330582297 1621840457281050997936723)
                      ·
                        rfl

theorem cell23_3158523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 4, 2].length) (baseStart_3158523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158523 prefixEnd_3158523 := by exact prefixLift 3158523
  have htrace : WordTrace (prefixWord ++ tailWord_3158523) baseStart_3158523 baseEnd_3158523 := by
    simpa [prefixWord, tailWord_3158523, baseEnd_3158523] using wordTrace_append hprefix tailTrace_3158523
  have hstable : (prefixWord ++ tailWord_3158523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158523).length < 2 ^ (prefixWord ++ tailWord_3158523).sum := by decide
  have hdescent : baseEnd_3158523 < baseStart_3158523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158534 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_3158534 : Nat := 118140960795 + 3158534 * 2 ^ 59
def prefixEnd_3158534 : Nat := 4983230072969 + 3 ^ 40 * 3158534 * 2
def baseEnd_3158534 : Nat := 1621846105568250454899173

theorem tailTrace_3158534 : CollatzResearch.WordTrace tailWord_3158534 prefixEnd_3158534 1621846105568250454899173 := by
  unfold tailWord_3158534
  simp only [CollatzResearch.WordTrace]
  refine ⟨3600037473099319609553833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76800799426118818337148437 3600037473099319609553833)
  ·
    refine ⟨2700028104824489707165375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3600037473099319609553833 2700028104824489707165375)
    ·
      refine ⟨4050042157236734560748063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700028104824489707165375 4050042157236734560748063)
      ·
        refine ⟨6075063235855101841122095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050042157236734560748063 6075063235855101841122095)
        ·
          refine ⟨9112594853782652761683143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075063235855101841122095 9112594853782652761683143)
          ·
            refine ⟨13668892280673979142524715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9112594853782652761683143 13668892280673979142524715)
            ·
              refine ⟨20503338421010968713787073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13668892280673979142524715 20503338421010968713787073)
              ·
                refine ⟨15377503815758226535340305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20503338421010968713787073 15377503815758226535340305)
                ·
                  refine ⟨11533127861818669901505229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15377503815758226535340305 11533127861818669901505229)
                  ·
                    refine ⟨4324922948182001213064461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11533127861818669901505229 4324922948182001213064461)
                    ·
                      refine ⟨1621846105568250454899173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4324922948182001213064461 1621846105568250454899173)
                      ·
                        rfl

theorem cell23_3158534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_3158534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158534 prefixEnd_3158534 := by exact prefixLift 3158534
  have htrace : WordTrace (prefixWord ++ tailWord_3158534) baseStart_3158534 baseEnd_3158534 := by
    simpa [prefixWord, tailWord_3158534, baseEnd_3158534] using wordTrace_append hprefix tailTrace_3158534
  have hstable : (prefixWord ++ tailWord_3158534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158534).length < 2 ^ (prefixWord ++ tailWord_3158534).sum := by decide
  have hdescent : baseEnd_3158534 < baseStart_3158534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158540 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 2, 4, 2]
def baseStart_3158540 : Nat := 118140960795 + 3158540 * 2 ^ 59
def prefixEnd_3158540 : Nat := 4983230072969 + 3 ^ 40 * 3158540 * 2
def baseEnd_3158540 : Nat := 1621849186452177431424145

theorem tailTrace_3158540 : CollatzResearch.WordTrace tailWord_3158540 prefixEnd_3158540 1621849186452177431424145 := by
  unfold tailWord_3158540
  simp only [CollatzResearch.WordTrace]
  refine ⟨57600708988578245265220537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76800945318104327020294049 57600708988578245265220537)
  ·
    refine ⟨43200531741433683948915403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57600708988578245265220537 43200531741433683948915403)
    ·
      refine ⟨64800797612150525923373105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43200531741433683948915403 64800797612150525923373105)
      ·
        refine ⟨48600598209112894442529829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64800797612150525923373105 48600598209112894442529829)
        ·
          refine ⟨9112612164208667707974343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48600598209112894442529829 9112612164208667707974343)
          ·
            refine ⟨13668918246313001561961515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9112612164208667707974343 13668918246313001561961515)
            ·
              refine ⟨20503377369469502342942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13668918246313001561961515 20503377369469502342942273)
              ·
                refine ⟨15377533027102126757206705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20503377369469502342942273 15377533027102126757206705)
                ·
                  refine ⟨11533149770326595067905029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15377533027102126757206705 11533149770326595067905029)
                  ·
                    refine ⟨2162465581936236575232193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11533149770326595067905029 2162465581936236575232193)
                    ·
                      refine ⟨1621849186452177431424145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162465581936236575232193 1621849186452177431424145)
                      ·
                        rfl

theorem cell23_3158540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_3158540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158540 prefixEnd_3158540 := by exact prefixLift 3158540
  have htrace : WordTrace (prefixWord ++ tailWord_3158540) baseStart_3158540 baseEnd_3158540 := by
    simpa [prefixWord, tailWord_3158540, baseEnd_3158540] using wordTrace_append hprefix tailTrace_3158540
  have hstable : (prefixWord ++ tailWord_3158540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158540).length < 2 ^ (prefixWord ++ tailWord_3158540).sum := by decide
  have hdescent : baseEnd_3158540 < baseStart_3158540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158607 : List Nat := [1, 1, 2, 1, 1, 2, 4, 6, 1, 1, 3]
def baseStart_3158607 : Nat := 118140960795 + 3158607 * 2 ^ 59
def prefixEnd_3158607 : Nat := 4983230072969 + 3 ^ 40 * 3158607 * 2
def baseEnd_3158607 : Nat := 1621883589656028669286337

theorem tailTrace_3158607 : CollatzResearch.WordTrace tailWord_3158607 prefixEnd_3158607 1621883589656028669286337 := by
  unfold tailWord_3158607
  simp only [CollatzResearch.WordTrace]
  refine ⟨115203861667913760973130075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76802574445275840648753383 115203861667913760973130075)
  ·
    refine ⟨172805792501870641459695113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115203861667913760973130075 172805792501870641459695113)
    ·
      refine ⟨129604344376402981094771335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172805792501870641459695113 129604344376402981094771335)
      ·
        refine ⟨194406516564604471642157003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129604344376402981094771335 194406516564604471642157003)
        ·
          refine ⟨291609774846906707463235505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194406516564604471642157003 291609774846906707463235505)
          ·
            refine ⟨218707331135180030597426629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 291609774846906707463235505 218707331135180030597426629)
            ·
              refine ⟨41007624587846255737017493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218707331135180030597426629 41007624587846255737017493)
              ·
                refine ⟨1922232402555293237672695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41007624587846255737017493 1922232402555293237672695)
                ·
                  refine ⟨2883348603832939856509043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922232402555293237672695 2883348603832939856509043)
                  ·
                    refine ⟨4325022905749409784763565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2883348603832939856509043 4325022905749409784763565)
                    ·
                      refine ⟨1621883589656028669286337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4325022905749409784763565 1621883589656028669286337)
                      ·
                        rfl

theorem cell23_3158607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 6, 1, 1, 3].length) (baseStart_3158607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158607 prefixEnd_3158607 := by exact prefixLift 3158607
  have htrace : WordTrace (prefixWord ++ tailWord_3158607) baseStart_3158607 baseEnd_3158607 := by
    simpa [prefixWord, tailWord_3158607, baseEnd_3158607] using wordTrace_append hprefix tailTrace_3158607
  have hstable : (prefixWord ++ tailWord_3158607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158607).length < 2 ^ (prefixWord ++ tailWord_3158607).sum := by decide
  have hdescent : baseEnd_3158607 < baseStart_3158607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158640 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 1, 6]
def baseStart_3158640 : Nat := 118140960795 + 3158640 * 2 ^ 59
def prefixEnd_3158640 : Nat := 4983230072969 + 3 ^ 40 * 3158640 * 2
def baseEnd_3158640 : Nat := 540633511505875680057895

theorem tailTrace_3158640 : CollatzResearch.WordTrace tailWord_3158640 prefixEnd_3158640 540633511505875680057895 := by
  unfold tailWord_3158640
  simp only [CollatzResearch.WordTrace]
  refine ⟨57602532638397103804540687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76803376851196138406054249 57602532638397103804540687)
  ·
    refine ⟨86403798957595655706811031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57602532638397103804540687 86403798957595655706811031)
    ·
      refine ⟨129605698436393483560216547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86403798957595655706811031 129605698436393483560216547)
      ·
        refine ⟨194408547654590225340324821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129605698436393483560216547 194408547654590225340324821)
        ·
          refine ⟨4556450335654458406413863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194408547654590225340324821 4556450335654458406413863)
          ·
            refine ⟨6834675503481687609620795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556450335654458406413863 6834675503481687609620795)
            ·
              refine ⟨10252013255222531414431193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6834675503481687609620795 10252013255222531414431193)
              ·
                refine ⟨7689009941416898560823395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10252013255222531414431193 7689009941416898560823395)
                ·
                  refine ⟨11533514912125347841235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7689009941416898560823395 11533514912125347841235093)
                  ·
                    refine ⟨540633511505875680057895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11533514912125347841235093 540633511505875680057895)
                    ·
                      rfl

theorem cell23_3158640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 1, 6].length) (baseStart_3158640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158640 prefixEnd_3158640 := by exact prefixLift 3158640
  have htrace : WordTrace (prefixWord ++ tailWord_3158640) baseStart_3158640 baseEnd_3158640 := by
    simpa [prefixWord, tailWord_3158640, baseEnd_3158640] using wordTrace_append hprefix tailTrace_3158640
  have hstable : (prefixWord ++ tailWord_3158640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158640).length < 2 ^ (prefixWord ++ tailWord_3158640).sum := by decide
  have hdescent : baseEnd_3158640 < baseStart_3158640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158653 : List Nat := [1, 4, 1, 1, 5, 11]
def baseStart_3158653 : Nat := 118140960795 + 3158653 * 2 ^ 59
def prefixEnd_3158653 : Nat := 4983230072969 + 3 ^ 40 * 3158653 * 2
def baseEnd_3158653 : Nat := 6674515266527306540375

theorem tailTrace_3158653 : CollatzResearch.WordTrace tailWord_3158653 prefixEnd_3158653 6674515266527306540375 := by
  unfold tailWord_3158653
  simp only [CollatzResearch.WordTrace]
  refine ⟨115205539425747110829304613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76803692950498073886203075 115205539425747110829304613)
  ·
    refine ⟨21601038642327583280494615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115205539425747110829304613 21601038642327583280494615)
    ·
      refine ⟨32401557963491374920741923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21601038642327583280494615 32401557963491374920741923)
      ·
        refine ⟨48602336945237062381112885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32401557963491374920741923 48602336945237062381112885)
        ·
          refine ⟨4556469088615974598229333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48602336945237062381112885 4556469088615974598229333)
          ·
            refine ⟨6674515266527306540375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4556469088615974598229333 6674515266527306540375)
            ·
              rfl

theorem cell23_3158653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 11].length) (baseStart_3158653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158653 prefixEnd_3158653 := by exact prefixLift 3158653
  have htrace : WordTrace (prefixWord ++ tailWord_3158653) baseStart_3158653 baseEnd_3158653 := by
    simpa [prefixWord, tailWord_3158653, baseEnd_3158653] using wordTrace_append hprefix tailTrace_3158653
  have hstable : (prefixWord ++ tailWord_3158653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158653).length < 2 ^ (prefixWord ++ tailWord_3158653).sum := by decide
  have hdescent : baseEnd_3158653 < baseStart_3158653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158657 : List Nat := [1, 2, 4, 2, 1, 1, 4, 2, 2, 4]
def baseStart_3158657 : Nat := 118140960795 + 3158657 * 2 ^ 59
def prefixEnd_3158657 : Nat := 4983230072969 + 3 ^ 40 * 3158657 * 2
def baseEnd_3158657 : Nat := 540636421229584491220369

theorem tailTrace_3158657 : CollatzResearch.WordTrace tailWord_3158657 prefixEnd_3158657 540636421229584491220369 := by
  unfold tailWord_3158657
  simp only [CollatzResearch.WordTrace]
  refine ⟨115205685317732619512450225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76803790211821746341633483 115205685317732619512450225)
  ·
    refine ⟨86404263988299464634337669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115205685317732619512450225 86404263988299464634337669)
    ·
      refine ⟨16200799497806149618938313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86404263988299464634337669 16200799497806149618938313)
      ·
        refine ⟨12150599623354612214203735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16200799497806149618938313 12150599623354612214203735)
        ·
          refine ⟨18225899435031918321305603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150599623354612214203735 18225899435031918321305603)
          ·
            refine ⟨27338849152547877481958405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18225899435031918321305603 27338849152547877481958405)
            ·
              refine ⟨5126034216102727027867201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27338849152547877481958405 5126034216102727027867201)
              ·
                refine ⟨3844525662077045270900401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5126034216102727027867201 3844525662077045270900401)
                ·
                  refine ⟨2883394246557783953175301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844525662077045270900401 2883394246557783953175301)
                  ·
                    refine ⟨540636421229584491220369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883394246557783953175301 540636421229584491220369)
                    ·
                      rfl

theorem cell23_3158657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_3158657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158657 prefixEnd_3158657 := by exact prefixLift 3158657
  have htrace : WordTrace (prefixWord ++ tailWord_3158657) baseStart_3158657 baseEnd_3158657 := by
    simpa [prefixWord, tailWord_3158657, baseEnd_3158657] using wordTrace_append hprefix tailTrace_3158657
  have hstable : (prefixWord ++ tailWord_3158657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158657).length < 2 ^ (prefixWord ++ tailWord_3158657).sum := by decide
  have hdescent : baseEnd_3158657 < baseStart_3158657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158693 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_3158693 : Nat := 118140960795 + 3158693 * 2 ^ 59
def prefixEnd_3158693 : Nat := 4983230072969 + 3 ^ 40 * 3158693 * 2
def baseEnd_3158693 : Nat := 1621927748992315332810941

theorem tailTrace_3158693 : CollatzResearch.WordTrace tailWord_3158693 prefixEnd_3158693 1621927748992315332810941 := by
  unfold tailWord_3158693
  simp only [CollatzResearch.WordTrace]
  refine ⟨115206998345602197660760733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76804665563734798440507155 115206998345602197660760733)
  ·
    refine ⟨43202624379600824122785275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115206998345602197660760733 43202624379600824122785275)
    ·
      refine ⟨64803936569401236184177913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43202624379600824122785275 64803936569401236184177913)
      ·
        refine ⟨48602952427050927138133435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64803936569401236184177913 48602952427050927138133435)
        ·
          refine ⟨72904428640576390707200153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48602952427050927138133435 72904428640576390707200153)
          ·
            refine ⟨54678321480432293030400115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72904428640576390707200153 54678321480432293030400115)
            ·
              refine ⟨82017482220648439545600173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54678321480432293030400115 82017482220648439545600173)
              ·
                refine ⟨30756555832743164829600065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82017482220648439545600173 30756555832743164829600065)
                ·
                  refine ⟨23067416874557373622200049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30756555832743164829600065 23067416874557373622200049)
                  ·
                    refine ⟨17300562655918030216650037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23067416874557373622200049 17300562655918030216650037)
                    ·
                      refine ⟨1621927748992315332810941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17300562655918030216650037 1621927748992315332810941)
                      ·
                        rfl

theorem cell23_3158693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_3158693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158693 prefixEnd_3158693 := by exact prefixLift 3158693
  have htrace : WordTrace (prefixWord ++ tailWord_3158693) baseStart_3158693 baseEnd_3158693 := by
    simpa [prefixWord, tailWord_3158693, baseEnd_3158693] using wordTrace_append hprefix tailTrace_3158693
  have hstable : (prefixWord ++ tailWord_3158693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158693).length < 2 ^ (prefixWord ++ tailWord_3158693).sum := by decide
  have hdescent : baseEnd_3158693 < baseStart_3158693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158698 : List Nat := [3, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_3158698 : Nat := 118140960795 + 3158698 * 2 ^ 59
def prefixEnd_3158698 : Nat := 4983230072969 + 3 ^ 40 * 3158698 * 2
def baseEnd_3158698 : Nat := 1621930316395587813248419

theorem tailTrace_3158698 : CollatzResearch.WordTrace tailWord_3158698 prefixEnd_3158698 1621930316395587813248419 := by
  unfold tailWord_3158698
  simp only [CollatzResearch.WordTrace]
  refine ⟨28801795177646020878673187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76804787140389389009795165 28801795177646020878673187)
  ·
    refine ⟨43202692766469031318009781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28801795177646020878673187 43202692766469031318009781)
    ·
      refine ⟨4050252446856471686063417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43202692766469031318009781 4050252446856471686063417)
      ·
        refine ⟨3037689335142353764547563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4050252446856471686063417 3037689335142353764547563)
        ·
          refine ⟨4556534002713530646821345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037689335142353764547563 4556534002713530646821345)
          ·
            refine ⟨3417400502035147985116009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4556534002713530646821345 3417400502035147985116009)
            ·
              refine ⟨2563050376526360988837007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417400502035147985116009 2563050376526360988837007)
              ·
                refine ⟨3844575564789541483255511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563050376526360988837007 3844575564789541483255511)
                ·
                  refine ⟨5766863347184312224883267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844575564789541483255511 5766863347184312224883267)
                  ·
                    refine ⟨8650295020776468337324901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5766863347184312224883267 8650295020776468337324901)
                    ·
                      refine ⟨1621930316395587813248419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8650295020776468337324901 1621930316395587813248419)
                      ·
                        rfl

theorem cell23_3158698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_3158698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158698 prefixEnd_3158698 := by exact prefixLift 3158698
  have htrace : WordTrace (prefixWord ++ tailWord_3158698) baseStart_3158698 baseEnd_3158698 := by
    simpa [prefixWord, tailWord_3158698, baseEnd_3158698] using wordTrace_append hprefix tailTrace_3158698
  have hstable : (prefixWord ++ tailWord_3158698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158698).length < 2 ^ (prefixWord ++ tailWord_3158698).sum := by decide
  have hdescent : baseEnd_3158698 < baseStart_3158698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158701 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_3158701 : Nat := 118140960795 + 3158701 * 2 ^ 59
def prefixEnd_3158701 : Nat := 4983230072969 + 3 ^ 40 * 3158701 * 2
def baseEnd_3158701 : Nat := 1621931856837551301510905

theorem tailTrace_3158701 : CollatzResearch.WordTrace tailWord_3158701 prefixEnd_3158701 1621931856837551301510905 := by
  unfold tailWord_3158701
  simp only [CollatzResearch.WordTrace]
  refine ⟨115207290129573215027051957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76804860086382143351367971 115207290129573215027051957)
  ·
    refine ⟨10800683449647488908786121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115207290129573215027051957 10800683449647488908786121)
    ·
      refine ⟨8100512587235616681589591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10800683449647488908786121 8100512587235616681589591)
      ·
        refine ⟨12150768880853425022384387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8100512587235616681589591 12150768880853425022384387)
        ·
          refine ⟨18226153321280137533576581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12150768880853425022384387 18226153321280137533576581)
          ·
            refine ⟨3417403747740025787545609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18226153321280137533576581 3417403747740025787545609)
            ·
              refine ⟨2563052810805019340659207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417403747740025787545609 2563052810805019340659207)
              ·
                refine ⟨3844579216207529010988811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563052810805019340659207 3844579216207529010988811)
                ·
                  refine ⟨5766868824311293516483217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3844579216207529010988811 5766868824311293516483217)
                  ·
                    refine ⟨4325151618233470137362413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5766868824311293516483217 4325151618233470137362413)
                    ·
                      refine ⟨1621931856837551301510905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4325151618233470137362413 1621931856837551301510905)
                      ·
                        rfl

theorem cell23_3158701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_3158701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158701 prefixEnd_3158701 := by exact prefixLift 3158701
  have htrace : WordTrace (prefixWord ++ tailWord_3158701) baseStart_3158701 baseEnd_3158701 := by
    simpa [prefixWord, tailWord_3158701, baseEnd_3158701] using wordTrace_append hprefix tailTrace_3158701
  have hstable : (prefixWord ++ tailWord_3158701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158701).length < 2 ^ (prefixWord ++ tailWord_3158701).sum := by decide
  have hdescent : baseEnd_3158701 < baseStart_3158701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158730 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 2, 6]
def baseStart_3158730 : Nat := 118140960795 + 3158730 * 2 ^ 59
def prefixEnd_3158730 : Nat := 4983230072969 + 3 ^ 40 * 3158730 * 2
def baseEnd_3158730 : Nat := 540648915925510562682757

theorem tailTrace_3158730 : CollatzResearch.WordTrace tailWord_3158730 prefixEnd_3158730 540648915925510562682757 := by
  unfold tailWord_3158730
  simp only [CollatzResearch.WordTrace]
  refine ⟨28802086961617038244964411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76805565230978768653238429 28802086961617038244964411)
  ·
    refine ⟨43203130442425557367446617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28802086961617038244964411 43203130442425557367446617)
    ·
      refine ⟨32402347831819168025584963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43203130442425557367446617 32402347831819168025584963)
      ·
        refine ⟨48603521747728752038377445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32402347831819168025584963 48603521747728752038377445)
        ·
          refine ⟨9113160327699141007195771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48603521747728752038377445 9113160327699141007195771)
          ·
            refine ⟨13669740491548711510793657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113160327699141007195771 13669740491548711510793657)
            ·
              refine ⟨10252305368661533633095243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13669740491548711510793657 10252305368661533633095243)
              ·
                refine ⟨15378458052992300449642865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10252305368661533633095243 15378458052992300449642865)
                ·
                  refine ⟨11533843539744225337232149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15378458052992300449642865 11533843539744225337232149)
                  ·
                    refine ⟨540648915925510562682757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11533843539744225337232149 540648915925510562682757)
                    ·
                      rfl

theorem cell23_3158730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 2, 6].length) (baseStart_3158730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158730 prefixEnd_3158730 := by exact prefixLift 3158730
  have htrace : WordTrace (prefixWord ++ tailWord_3158730) baseStart_3158730 baseEnd_3158730 := by
    simpa [prefixWord, tailWord_3158730, baseEnd_3158730] using wordTrace_append hprefix tailTrace_3158730
  have hstable : (prefixWord ++ tailWord_3158730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158730).length < 2 ^ (prefixWord ++ tailWord_3158730).sum := by decide
  have hdescent : baseEnd_3158730 < baseStart_3158730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158871 : List Nat := [1, 1, 3, 2, 4, 2, 2, 3, 1, 4]
def baseStart_3158871 : Nat := 118140960795 + 3158871 * 2 ^ 59
def prefixEnd_3158871 : Nat := 4983230072969 + 3 ^ 40 * 3158871 * 2
def baseEnd_3158871 : Nat := 540673049516271878795041

theorem tailTrace_3158871 : CollatzResearch.WordTrace tailWord_3158871 prefixEnd_3158871 540673049516271878795041 := by
  unfold tailWord_3158871
  simp only [CollatzResearch.WordTrace]
  refine ⟨115213490538957334060740467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76808993692638222707160311 115213490538957334060740467)
  ·
    refine ⟨172820235808436001091110701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115213490538957334060740467 172820235808436001091110701)
    ·
      refine ⟨64807588428163500409166513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172820235808436001091110701 64807588428163500409166513)
      ·
        refine ⟨48605691321122625306874885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64807588428163500409166513 48605691321122625306874885)
        ·
          refine ⟨9113567122710492245039041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48605691321122625306874885 9113567122710492245039041)
          ·
            refine ⟨6835175342032869183779281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9113567122710492245039041 6835175342032869183779281)
            ·
              refine ⟨5126381506524651887834461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6835175342032869183779281 5126381506524651887834461)
              ·
                refine ⟨1922393064946744457937923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5126381506524651887834461 1922393064946744457937923)
                ·
                  refine ⟨2883589597420116686906885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922393064946744457937923 2883589597420116686906885)
                  ·
                    refine ⟨540673049516271878795041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883589597420116686906885 540673049516271878795041)
                    ·
                      rfl

theorem cell23_3158871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_3158871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158871 prefixEnd_3158871 := by exact prefixLift 3158871
  have htrace : WordTrace (prefixWord ++ tailWord_3158871) baseStart_3158871 baseEnd_3158871 := by
    simpa [prefixWord, tailWord_3158871, baseEnd_3158871] using wordTrace_append hprefix tailTrace_3158871
  have hstable : (prefixWord ++ tailWord_3158871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158871).length < 2 ^ (prefixWord ++ tailWord_3158871).sum := by decide
  have hdescent : baseEnd_3158871 < baseStart_3158871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158884 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 6]
def baseStart_3158884 : Nat := 118140960795 + 3158884 * 2 ^ 59
def prefixEnd_3158884 : Nat := 4983230072969 + 3 ^ 40 * 3158884 * 2
def baseEnd_3158884 : Nat := 180225091533036009502507

theorem tailTrace_3158884 : CollatzResearch.WordTrace tailWord_3158884 prefixEnd_3158884 180225091533036009502507 := by
  unfold tailWord_3158884
  simp only [CollatzResearch.WordTrace]
  refine ⟨57606982343955118640481853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76809309791940158187309137 57606982343955118640481853)
  ·
    refine ⟨21602618378983169490180695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57606982343955118640481853 21602618378983169490180695)
    ·
      refine ⟨32403927568474754235271043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21602618378983169490180695 32403927568474754235271043)
      ·
        refine ⟨48605891352712131352906565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32403927568474754235271043 48605891352712131352906565)
        ·
          refine ⟨9113604628633524628669981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48605891352712131352906565 9113604628633524628669981)
          ·
            refine ⟨3417601735737571735751243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9113604628633524628669981 3417601735737571735751243)
            ·
              refine ⟨5126402603606357603626865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417601735737571735751243 5126402603606357603626865)
              ·
                refine ⟨3844801952704768202720149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5126402603606357603626865 3844801952704768202720149)
                ·
                  refine ⟨180225091533036009502507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3844801952704768202720149 180225091533036009502507)
                  ·
                    rfl

theorem cell23_3158884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_3158884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158884 prefixEnd_3158884 := by exact prefixLift 3158884
  have htrace : WordTrace (prefixWord ++ tailWord_3158884) baseStart_3158884 baseEnd_3158884 := by
    simpa [prefixWord, tailWord_3158884, baseEnd_3158884] using wordTrace_append hprefix tailTrace_3158884
  have hstable : (prefixWord ++ tailWord_3158884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158884).length < 2 ^ (prefixWord ++ tailWord_3158884).sum := by decide
  have hdescent : baseEnd_3158884 < baseStart_3158884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158937 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 3]
def baseStart_3158937 : Nat := 118140960795 + 3158937 * 2 ^ 59
def prefixEnd_3158937 : Nat := 4983230072969 + 3 ^ 40 * 3158937 * 2
def baseEnd_3158937 : Nat := 1622053038272012378159819

theorem tailTrace_3158937 : CollatzResearch.WordTrace tailWord_3158937 prefixEnd_3158937 1622053038272012378159819 := by
  unfold tailWord_3158937
  simp only [CollatzResearch.WordTrace]
  refine ⟨115215897756718227332643065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76810598504478818221762043 115215897756718227332643065)
  ·
    refine ⟨86411923317538670499482299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115215897756718227332643065 86411923317538670499482299)
    ·
      refine ⟨129617884976308005749223449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86411923317538670499482299 129617884976308005749223449)
      ·
        refine ⟨97213413732231004311917587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129617884976308005749223449 97213413732231004311917587)
        ·
          refine ⟨145820120598346506467876381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97213413732231004311917587 145820120598346506467876381)
          ·
            refine ⟨54682545224379939925453643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145820120598346506467876381 54682545224379939925453643)
            ·
              refine ⟨82023817836569909888180465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54682545224379939925453643 82023817836569909888180465)
              ·
                refine ⟨61517863377427432416135349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82023817836569909888180465 61517863377427432416135349)
                ·
                  refine ⟨5767299691633821789012689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61517863377427432416135349 5767299691633821789012689)
                  ·
                    refine ⟨4325474768725366341759517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767299691633821789012689 4325474768725366341759517)
                    ·
                      refine ⟨1622053038272012378159819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4325474768725366341759517 1622053038272012378159819)
                      ·
                        rfl

theorem cell23_3158937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2, 3].length) (baseStart_3158937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158937 prefixEnd_3158937 := by exact prefixLift 3158937
  have htrace : WordTrace (prefixWord ++ tailWord_3158937) baseStart_3158937 baseEnd_3158937 := by
    simpa [prefixWord, tailWord_3158937, baseEnd_3158937] using wordTrace_append hprefix tailTrace_3158937
  have hstable : (prefixWord ++ tailWord_3158937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158937).length < 2 ^ (prefixWord ++ tailWord_3158937).sum := by decide
  have hdescent : baseEnd_3158937 < baseStart_3158937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158945 : List Nat := [1, 2, 3, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_3158945 : Nat := 118140960795 + 3158945 * 2 ^ 59
def prefixEnd_3158945 : Nat := 4983230072969 + 3 ^ 40 * 3158945 * 2
def baseEnd_3158945 : Nat := 1622057146117248346859783

theorem tailTrace_3158945 : CollatzResearch.WordTrace tailWord_3158945 prefixEnd_3158945 1622057146117248346859783 := by
  unfold tailWord_3158945
  simp only [CollatzResearch.WordTrace]
  refine ⟨115216189540689244698934289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76810793027126163132622859 115216189540689244698934289)
  ·
    refine ⟨86412142155516933524200717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115216189540689244698934289 86412142155516933524200717)
    ·
      refine ⟨32404553308318850071575269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86412142155516933524200717 32404553308318850071575269)
      ·
        refine ⟨6075853745309784388420363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32404553308318850071575269 6075853745309784388420363)
        ·
          refine ⟨9113780617964676582630545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6075853745309784388420363 9113780617964676582630545)
          ·
            refine ⟨6835335463473507436972909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9113780617964676582630545 6835335463473507436972909)
            ·
              refine ⟨2563250798802565288864841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6835335463473507436972909 2563250798802565288864841)
              ·
                refine ⟨1922438099101923966648631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563250798802565288864841 1922438099101923966648631)
                ·
                  refine ⟨2883657148652885949972947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922438099101923966648631 2883657148652885949972947)
                  ·
                    refine ⟨4325485722979328924959421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2883657148652885949972947 4325485722979328924959421)
                    ·
                      refine ⟨1622057146117248346859783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4325485722979328924959421 1622057146117248346859783)
                      ·
                        rfl

theorem cell23_3158945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_3158945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158945 prefixEnd_3158945 := by exact prefixLift 3158945
  have htrace : WordTrace (prefixWord ++ tailWord_3158945) baseStart_3158945 baseEnd_3158945 := by
    simpa [prefixWord, tailWord_3158945, baseEnd_3158945] using wordTrace_append hprefix tailTrace_3158945
  have hstable : (prefixWord ++ tailWord_3158945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158945).length < 2 ^ (prefixWord ++ tailWord_3158945).sum := by decide
  have hdescent : baseEnd_3158945 < baseStart_3158945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3158961 : List Nat := [1, 2, 2, 4, 3, 1, 1, 3, 2, 4]
def baseStart_3158961 : Nat := 118140960795 + 3158961 * 2 ^ 59
def prefixEnd_3158961 : Nat := 4983230072969 + 3 ^ 40 * 3158961 * 2
def baseEnd_3158961 : Nat := 540688453935906761419903

theorem tailTrace_3158961 : CollatzResearch.WordTrace tailWord_3158961 prefixEnd_3158961 540688453935906761419903 := by
  unfold tailWord_3158961
  simp only [CollatzResearch.WordTrace]
  refine ⟨115216773108631279431516737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76811182072420852954344491 115216773108631279431516737)
  ·
    refine ⟨86412579831473459573637553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115216773108631279431516737 86412579831473459573637553)
    ·
      refine ⟨64809434873605094680228165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86412579831473459573637553 64809434873605094680228165)
      ·
        refine ⟨12151769038800955252542781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64809434873605094680228165 12151769038800955252542781)
        ·
          refine ⟨4556913389550358219703543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12151769038800955252542781 4556913389550358219703543)
          ·
            refine ⟨6835370084325537329555315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4556913389550358219703543 6835370084325537329555315)
            ·
              refine ⟨10253055126488305994332973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6835370084325537329555315 10253055126488305994332973)
              ·
                refine ⟨3844895672433114747874865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10253055126488305994332973 3844895672433114747874865)
                ·
                  refine ⟨2883671754324836060906149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844895672433114747874865 2883671754324836060906149)
                  ·
                    refine ⟨540688453935906761419903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2883671754324836060906149 540688453935906761419903)
                    ·
                      rfl

theorem cell23_3158961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 2, 4].length) (baseStart_3158961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3158961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3158961 prefixEnd_3158961 := by exact prefixLift 3158961
  have htrace : WordTrace (prefixWord ++ tailWord_3158961) baseStart_3158961 baseEnd_3158961 := by
    simpa [prefixWord, tailWord_3158961, baseEnd_3158961] using wordTrace_append hprefix tailTrace_3158961
  have hstable : (prefixWord ++ tailWord_3158961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3158961).length < 2 ^ (prefixWord ++ tailWord_3158961).sum := by decide
  have hdescent : baseEnd_3158961 < baseStart_3158961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3158961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159001 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 3]
def baseStart_3159001 : Nat := 118140960795 + 3159001 * 2 ^ 59
def prefixEnd_3159001 : Nat := 4983230072969 + 3 ^ 40 * 3159001 * 2
def baseEnd_3159001 : Nat := 1622085901033900127759525

theorem tailTrace_3159001 : CollatzResearch.WordTrace tailWord_3159001 prefixEnd_3159001 1622085901033900127759525 := by
  unfold tailWord_3159001
  simp only [CollatzResearch.WordTrace]
  refine ⟨115218232028486366262972857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76812154685657577508648571 115218232028486366262972857)
  ·
    refine ⟨86413674021364774697229643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115218232028486366262972857 86413674021364774697229643)
    ·
      refine ⟨129620511032047162045844465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86413674021364774697229643 129620511032047162045844465)
      ·
        refine ⟨97215383274035371534383349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129620511032047162045844465 97215383274035371534383349)
        ·
          refine ⟨9113942181940816081348439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97215383274035371534383349 9113942181940816081348439)
          ·
            refine ⟨13670913272911224122022659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9113942181940816081348439 13670913272911224122022659)
            ·
              refine ⟨20506369909366836183033989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13670913272911224122022659 20506369909366836183033989)
              ·
                refine ⟨3844944358006281784318873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20506369909366836183033989 3844944358006281784318873)
                ·
                  refine ⟨2883708268504711338239155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3844944358006281784318873 2883708268504711338239155)
                  ·
                    refine ⟨4325562402757067007358733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2883708268504711338239155 4325562402757067007358733)
                    ·
                      refine ⟨1622085901033900127759525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4325562402757067007358733 1622085901033900127759525)
                      ·
                        rfl

theorem cell23_3159001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 2, 1, 3].length) (baseStart_3159001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159001 prefixEnd_3159001 := by exact prefixLift 3159001
  have htrace : WordTrace (prefixWord ++ tailWord_3159001) baseStart_3159001 baseEnd_3159001 := by
    simpa [prefixWord, tailWord_3159001, baseEnd_3159001] using wordTrace_append hprefix tailTrace_3159001
  have hstable : (prefixWord ++ tailWord_3159001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159001).length < 2 ^ (prefixWord ++ tailWord_3159001).sum := by decide
  have hdescent : baseEnd_3159001 < baseStart_3159001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159002 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2]
def baseStart_3159002 : Nat := 118140960795 + 3159002 * 2 ^ 59
def prefixEnd_3159002 : Nat := 4983230072969 + 3 ^ 40 * 3159002 * 2
def baseEnd_3159002 : Nat := 1622086414514554623847021

theorem tailTrace_3159002 : CollatzResearch.WordTrace tailWord_3159002 prefixEnd_3159002 1622086414514554623847021 := by
  unfold tailWord_3159002
  simp only [CollatzResearch.WordTrace]
  refine ⟨28804567125370685858439815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76812179000988495622506173 28804567125370685858439815)
  ·
    refine ⟨43206850688056028787659723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28804567125370685858439815 43206850688056028787659723)
    ·
      refine ⟨64810276032084043181489585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43206850688056028787659723 64810276032084043181489585)
      ·
        refine ⟨48607707024063032386117189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64810276032084043181489585 48607707024063032386117189)
        ·
          refine ⟨9113945067011818572396973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48607707024063032386117189 9113945067011818572396973)
          ·
            refine ⟨3417729400129431964648865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9113945067011818572396973 3417729400129431964648865)
            ·
              refine ⟨2563297050097073973486649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417729400129431964648865 2563297050097073973486649)
              ·
                refine ⟨1922472787572805480114987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563297050097073973486649 1922472787572805480114987)
                ·
                  refine ⟨2883709181359208220172481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1922472787572805480114987 2883709181359208220172481)
                  ·
                    refine ⟨2162781886019406165129361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883709181359208220172481 2162781886019406165129361)
                    ·
                      refine ⟨1622086414514554623847021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162781886019406165129361 1622086414514554623847021)
                      ·
                        rfl

theorem cell23_3159002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_3159002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159002 prefixEnd_3159002 := by exact prefixLift 3159002
  have htrace : WordTrace (prefixWord ++ tailWord_3159002) baseStart_3159002 baseEnd_3159002 := by
    simpa [prefixWord, tailWord_3159002, baseEnd_3159002] using wordTrace_append hprefix tailTrace_3159002
  have hstable : (prefixWord ++ tailWord_3159002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159002).length < 2 ^ (prefixWord ++ tailWord_3159002).sum := by decide
  have hdescent : baseEnd_3159002 < baseStart_3159002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159037 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_3159037 : Nat := 118140960795 + 3159037 * 2 ^ 59
def prefixEnd_3159037 : Nat := 4983230072969 + 3 ^ 40 * 3159037 * 2
def baseEnd_3159037 : Nat := 1622104386337461986909359

theorem tailTrace_3159037 : CollatzResearch.WordTrace tailWord_3159037 prefixEnd_3159037 1622104386337461986909359 := by
  unfold tailWord_3159037
  simp only [CollatzResearch.WordTrace]
  refine ⟨115219545056355944411283365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76813030037570629607522243 115219545056355944411283365)
  ·
    refine ⟨21603664698066739577115631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115219545056355944411283365 21603664698066739577115631)
    ·
      refine ⟨32405497047100109365673447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21603664698066739577115631 32405497047100109365673447)
      ·
        refine ⟨48608245570650164048510171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32405497047100109365673447 48608245570650164048510171)
        ·
          refine ⟨72912368355975246072765257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48608245570650164048510171 72912368355975246072765257)
          ·
            refine ⟨54684276266981434554573943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72912368355975246072765257 54684276266981434554573943)
            ·
              refine ⟨82026414400472151831860915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54684276266981434554573943 82026414400472151831860915)
              ·
                refine ⟨123039621600708227747791373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82026414400472151831860915 123039621600708227747791373)
                ·
                  refine ⟨46139858100265585405421765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123039621600708227747791373 46139858100265585405421765)
                  ·
                    refine ⟨8651223393799797263516581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46139858100265585405421765 8651223393799797263516581)
                    ·
                      refine ⟨1622104386337461986909359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8651223393799797263516581 1622104386337461986909359)
                      ·
                        rfl

theorem cell23_3159037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_3159037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159037 prefixEnd_3159037 := by exact prefixLift 3159037
  have htrace : WordTrace (prefixWord ++ tailWord_3159037) baseStart_3159037 baseEnd_3159037 := by
    simpa [prefixWord, tailWord_3159037, baseEnd_3159037] using wordTrace_append hprefix tailTrace_3159037
  have hstable : (prefixWord ++ tailWord_3159037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159037).length < 2 ^ (prefixWord ++ tailWord_3159037).sum := by decide
  have hdescent : baseEnd_3159037 < baseStart_3159037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159041 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_3159041 : Nat := 118140960795 + 3159041 * 2 ^ 59
def prefixEnd_3159041 : Nat := 4983230072969 + 3 ^ 40 * 3159041 * 2
def baseEnd_3159041 : Nat := 1622106440260079971259341

theorem tailTrace_3159041 : CollatzResearch.WordTrace tailWord_3159041 prefixEnd_3159041 1622106440260079971259341 := by
  unfold tailWord_3159041
  simp only [CollatzResearch.WordTrace]
  refine ⟨115219690948341453094428977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76813127298894302062952651 115219690948341453094428977)
  ·
    refine ⟨86414768211256089820821733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115219690948341453094428977 86414768211256089820821733)
    ·
      refine ⟨16202769039610516841404075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86414768211256089820821733 16202769039610516841404075)
      ·
        refine ⟨24304153559415775262106113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16202769039610516841404075 24304153559415775262106113)
        ·
          refine ⟨18228115169561831446579585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24304153559415775262106113 18228115169561831446579585)
          ·
            refine ⟨13671086377171373584934689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18228115169561831446579585 13671086377171373584934689)
            ·
              refine ⟨10253314782878530188701017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13671086377171373584934689 10253314782878530188701017)
              ·
                refine ⟨7689986087158897641525763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10253314782878530188701017 7689986087158897641525763)
                ·
                  refine ⟨11534979130738346462288645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7689986087158897641525763 11534979130738346462288645)
                  ·
                    refine ⟨2162808587013439961679121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11534979130738346462288645 2162808587013439961679121)
                    ·
                      refine ⟨1622106440260079971259341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162808587013439961679121 1622106440260079971259341)
                      ·
                        rfl

theorem cell23_3159041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_3159041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159041 prefixEnd_3159041 := by exact prefixLift 3159041
  have htrace : WordTrace (prefixWord ++ tailWord_3159041) baseStart_3159041 baseEnd_3159041 := by
    simpa [prefixWord, tailWord_3159041, baseEnd_3159041] using wordTrace_append hprefix tailTrace_3159041
  have hstable : (prefixWord ++ tailWord_3159041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159041).length < 2 ^ (prefixWord ++ tailWord_3159041).sum := by decide
  have hdescent : baseEnd_3159041 < baseStart_3159041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159047 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 9]
def baseStart_3159047 : Nat := 118140960795 + 3159047 * 2 ^ 59
def prefixEnd_3159047 : Nat := 4983230072969 + 3 ^ 40 * 3159047 * 2
def baseEnd_3159047 : Nat := 180234391238222994198257

theorem tailTrace_3159047 : CollatzResearch.WordTrace tailWord_3159047 prefixEnd_3159047 180234391238222994198257 := by
  unfold tailWord_3159047
  simp only [CollatzResearch.WordTrace]
  refine ⟨115219909786319716119147395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76813273190879810746098263 115219909786319716119147395)
  ·
    refine ⟨172829864679479574178721093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115219909786319716119147395 172829864679479574178721093)
    ·
      refine ⟨32405599627402420158510205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172829864679479574178721093 32405599627402420158510205)
      ·
        refine ⟨12152099860275907559441327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32405599627402420158510205 12152099860275907559441327)
        ·
          refine ⟨18228149790413861339161991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12152099860275907559441327 18228149790413861339161991)
          ·
            refine ⟨27342224685620792008742987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18228149790413861339161991 27342224685620792008742987)
            ·
              refine ⟨41013337028431188013114481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27342224685620792008742987 41013337028431188013114481)
              ·
                refine ⟨30760002771323391009835861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41013337028431188013114481 30760002771323391009835861)
                ·
                  refine ⟨180234391238222994198257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30760002771323391009835861 180234391238222994198257)
                  ·
                    rfl

theorem cell23_3159047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 9].length) (baseStart_3159047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159047 prefixEnd_3159047 := by exact prefixLift 3159047
  have htrace : WordTrace (prefixWord ++ tailWord_3159047) baseStart_3159047 baseEnd_3159047 := by
    simpa [prefixWord, tailWord_3159047, baseEnd_3159047] using wordTrace_append hprefix tailTrace_3159047
  have hstable : (prefixWord ++ tailWord_3159047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159047).length < 2 ^ (prefixWord ++ tailWord_3159047).sum := by decide
  have hdescent : baseEnd_3159047 < baseStart_3159047 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159054 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_3159054 : Nat := 118140960795 + 3159054 * 2 ^ 59
def prefixEnd_3159054 : Nat := 4983230072969 + 3 ^ 40 * 3159054 * 2
def baseEnd_3159054 : Nat := 1622113115508588420396781

theorem tailTrace_3159054 : CollatzResearch.WordTrace tailWord_3159054 prefixEnd_3159054 1622113115508588420396781 := by
  unfold tailWord_3159054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402520637161794539331527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76813443398196237543101477 14402520637161794539331527)
  ·
    refine ⟨21603780955742691808997291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14402520637161794539331527 21603780955742691808997291)
    ·
      refine ⟨32405671433614037713495937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21603780955742691808997291 32405671433614037713495937)
      ·
        refine ⟨24304253575210528285121953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32405671433614037713495937 24304253575210528285121953)
        ·
          refine ⟨18228190181407896213841465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24304253575210528285121953 18228190181407896213841465)
          ·
            refine ⟨13671142636055922160381099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18228190181407896213841465 13671142636055922160381099)
            ·
              refine ⟨20506713954083883240571649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13671142636055922160381099 20506713954083883240571649)
              ·
                refine ⟨15380035465562912430428737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20506713954083883240571649 15380035465562912430428737)
                ·
                  refine ⟨11535026599172184322821553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15380035465562912430428737 11535026599172184322821553)
                  ·
                    refine ⟨8651269949379138242116165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11535026599172184322821553 8651269949379138242116165)
                    ·
                      refine ⟨1622113115508588420396781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8651269949379138242116165 1622113115508588420396781)
                      ·
                        rfl

theorem cell23_3159054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_3159054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159054 prefixEnd_3159054 := by exact prefixLift 3159054
  have htrace : WordTrace (prefixWord ++ tailWord_3159054) baseStart_3159054 baseEnd_3159054 := by
    simpa [prefixWord, tailWord_3159054, baseEnd_3159054] using wordTrace_append hprefix tailTrace_3159054
  have hstable : (prefixWord ++ tailWord_3159054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159054).length < 2 ^ (prefixWord ++ tailWord_3159054).sum := by decide
  have hdescent : baseEnd_3159054 < baseStart_3159054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159064 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 7]
def baseStart_3159064 : Nat := 118140960795 + 3159064 * 2 ^ 59
def prefixEnd_3159064 : Nat := 4983230072969 + 3 ^ 40 * 3159064 * 2
def baseEnd_3159064 : Nat := 180235361146125931252415

theorem tailTrace_3159064 : CollatzResearch.WordTrace tailWord_3159064 prefixEnd_3159064 180235361146125931252415 := by
  unfold tailWord_3159064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57610264913629064011258123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76813686551505418681677497 57610264913629064011258123)
  ·
    refine ⟨86415397370443596016887185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57610264913629064011258123 86415397370443596016887185)
    ·
      refine ⟨64811548027832697012665389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86415397370443596016887185 64811548027832697012665389)
      ·
        refine ⟨24304330510437261379749521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64811548027832697012665389 24304330510437261379749521)
        ·
          refine ⟨18228247882827946034812141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24304330510437261379749521 18228247882827946034812141)
          ·
            refine ⟨6835592956060479763054553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18228247882827946034812141 6835592956060479763054553)
            ·
              refine ⟨5126694717045359822290915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6835592956060479763054553 5126694717045359822290915)
              ·
                refine ⟨7690042075568039733436373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126694717045359822290915 7690042075568039733436373)
                ·
                  refine ⟨180235361146125931252415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7690042075568039733436373 180235361146125931252415)
                  ·
                    rfl

theorem cell23_3159064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 7].length) (baseStart_3159064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159064 prefixEnd_3159064 := by exact prefixLift 3159064
  have htrace : WordTrace (prefixWord ++ tailWord_3159064) baseStart_3159064 baseEnd_3159064 := by
    simpa [prefixWord, tailWord_3159064, baseEnd_3159064] using wordTrace_append hprefix tailTrace_3159064
  have hstable : (prefixWord ++ tailWord_3159064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159064).length < 2 ^ (prefixWord ++ tailWord_3159064).sum := by decide
  have hdescent : baseEnd_3159064 < baseStart_3159064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159075 : List Nat := [1, 1, 1, 4, 3, 3, 3, 1, 2, 2, 2]
def baseStart_3159075 : Nat := 118140960795 + 3159075 * 2 ^ 59
def prefixEnd_3159075 : Nat := 4983230072969 + 3 ^ 40 * 3159075 * 2
def baseEnd_3159075 : Nat := 1622123898602332838234185

theorem tailTrace_3159075 : CollatzResearch.WordTrace tailWord_3159075 prefixEnd_3159075 1622123898602332838234185 := by
  unfold tailWord_3159075
  simp only [CollatzResearch.WordTrace]
  refine ⟨115220931030218276901166679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76813954020145517934111119 115220931030218276901166679)
  ·
    refine ⟨172831396545327415351750019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115220931030218276901166679 172831396545327415351750019)
    ·
      refine ⟨259247094817991123027625029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172831396545327415351750019 259247094817991123027625029)
      ·
        refine ⟨48608830278373335567679693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259247094817991123027625029 48608830278373335567679693)
        ·
          refine ⟨18228311354390000837879885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48608830278373335567679693 18228311354390000837879885)
          ·
            refine ⟨6835616757896250314204957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18228311354390000837879885 6835616757896250314204957)
            ·
              refine ⟨2563356284211093867826859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6835616757896250314204957 2563356284211093867826859)
              ·
                refine ⟨3845034426316640801740289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563356284211093867826859 3845034426316640801740289)
                ·
                  refine ⟨2883775819737480601305217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845034426316640801740289 2883775819737480601305217)
                  ·
                    refine ⟨2162831864803110450978913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883775819737480601305217 2162831864803110450978913)
                    ·
                      refine ⟨1622123898602332838234185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162831864803110450978913 1622123898602332838234185)
                      ·
                        rfl

theorem cell23_3159075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_3159075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159075 prefixEnd_3159075 := by exact prefixLift 3159075
  have htrace : WordTrace (prefixWord ++ tailWord_3159075) baseStart_3159075 baseEnd_3159075 := by
    simpa [prefixWord, tailWord_3159075, baseEnd_3159075] using wordTrace_append hprefix tailTrace_3159075
  have hstable : (prefixWord ++ tailWord_3159075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159075).length < 2 ^ (prefixWord ++ tailWord_3159075).sum := by decide
  have hdescent : baseEnd_3159075 < baseStart_3159075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159077 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 3, 7]
def baseStart_3159077 : Nat := 118140960795 + 3159077 * 2 ^ 59
def prefixEnd_3159077 : Nat := 4983230072969 + 3 ^ 40 * 3159077 * 2
def baseEnd_3159077 : Nat := 540708308521213943469725

theorem tailTrace_3159077 : CollatzResearch.WordTrace tailWord_3159077 prefixEnd_3159077 540708308521213943469725 := by
  unfold tailWord_3159077
  simp only [CollatzResearch.WordTrace]
  refine ⟨115221003976211031242739485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76814002650807354161826323 115221003976211031242739485)
  ·
    refine ⟨43207876491079136716027307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115221003976211031242739485 43207876491079136716027307)
    ·
      refine ⟨64811814736618705074040961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43207876491079136716027307 64811814736618705074040961)
      ·
        refine ⟨48608861052464028805530721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64811814736618705074040961 48608861052464028805530721)
        ·
          refine ⟨36456645789348021604148041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48608861052464028805530721 36456645789348021604148041)
          ·
            refine ⟨27342484342011016203111031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36456645789348021604148041 27342484342011016203111031)
            ·
              refine ⟨41013726513016524304666547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27342484342011016203111031 41013726513016524304666547)
              ·
                refine ⟨61520589769524786456999821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41013726513016524304666547 61520589769524786456999821)
                ·
                  refine ⟨23070221163571794921374933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61520589769524786456999821 23070221163571794921374933)
                  ·
                    refine ⟨540708308521213943469725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23070221163571794921374933 540708308521213943469725)
                    ·
                      rfl

theorem cell23_3159077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_3159077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159077 prefixEnd_3159077 := by exact prefixLift 3159077
  have htrace : WordTrace (prefixWord ++ tailWord_3159077) baseStart_3159077 baseEnd_3159077 := by
    simpa [prefixWord, tailWord_3159077, baseEnd_3159077] using wordTrace_append hprefix tailTrace_3159077
  have hstable : (prefixWord ++ tailWord_3159077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159077).length < 2 ^ (prefixWord ++ tailWord_3159077).sum := by decide
  have hdescent : baseEnd_3159077 < baseStart_3159077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159114 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4]
def baseStart_3159114 : Nat := 118140960795 + 3159114 * 2 ^ 59
def prefixEnd_3159114 : Nat := 4983230072969 + 3 ^ 40 * 3159114 * 2
def baseEnd_3159114 : Nat := 1622143924347858185646505

theorem tailTrace_3159114 : CollatzResearch.WordTrace tailWord_3159114 prefixEnd_3159114 1622143924347858185646505 := by
  unfold tailWord_3159114
  simp only [CollatzResearch.WordTrace]
  refine ⟨28805588369269246640459099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76814902318051324374557597 28805588369269246640459099)
  ·
    refine ⟨43208382553903869960688649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28805588369269246640459099 43208382553903869960688649)
    ·
      refine ⟨32406286915427902470516487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43208382553903869960688649 32406286915427902470516487)
      ·
        refine ⟨48609430373141853705774731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32406286915427902470516487 48609430373141853705774731)
        ·
          refine ⟨72914145559712780558662097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48609430373141853705774731 72914145559712780558662097)
          ·
            refine ⟨54685609169784585418996573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72914145559712780558662097 54685609169784585418996573)
            ·
              refine ⟨20507103438669219532123715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54685609169784585418996573 20507103438669219532123715)
              ·
                refine ⟨30760655158003829298185573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20507103438669219532123715 30760655158003829298185573)
                ·
                  refine ⟨5767622842125717993409795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30760655158003829298185573 5767622842125717993409795)
                  ·
                    refine ⟨8651434263188576990114693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5767622842125717993409795 8651434263188576990114693)
                    ·
                      refine ⟨1622143924347858185646505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8651434263188576990114693 1622143924347858185646505)
                      ·
                        rfl

theorem cell23_3159114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 4, 1, 4].length) (baseStart_3159114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159114 prefixEnd_3159114 := by exact prefixLift 3159114
  have htrace : WordTrace (prefixWord ++ tailWord_3159114) baseStart_3159114 baseEnd_3159114 := by
    simpa [prefixWord, tailWord_3159114, baseEnd_3159114] using wordTrace_append hprefix tailTrace_3159114
  have hstable : (prefixWord ++ tailWord_3159114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159114).length < 2 ^ (prefixWord ++ tailWord_3159114).sum := by decide
  have hdescent : baseEnd_3159114 < baseStart_3159114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159126 : List Nat := [5, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_3159126 : Nat := 118140960795 + 3159126 * 2 ^ 59
def prefixEnd_3159126 : Nat := 4983230072969 + 3 ^ 40 * 3159126 * 2
def baseEnd_3159126 : Nat := 1622150086115712138696451

theorem tailTrace_3159126 : CollatzResearch.WordTrace tailWord_3159126 prefixEnd_3159126 1622150086115712138696451 := by
  unfold tailWord_3159126
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201424447064594538204577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76815194102022341740848821 7201424447064594538204577)
  ·
    refine ⟨5401068335298445903653433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7201424447064594538204577 5401068335298445903653433)
    ·
      refine ⟨4050801251473834427740075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5401068335298445903653433 4050801251473834427740075)
      ·
        refine ⟨6076201877210751641610113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4050801251473834427740075 6076201877210751641610113)
        ·
          refine ⟨4557151407908063731207585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6076201877210751641610113 4557151407908063731207585)
          ·
            refine ⟨3417863555931047798405689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4557151407908063731207585 3417863555931047798405689)
            ·
              refine ⟨2563397666948285848804267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417863555931047798405689 2563397666948285848804267)
              ·
                refine ⟨3845096500422428773206401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563397666948285848804267 3845096500422428773206401)
                ·
                  refine ⟨2883822375316821579904801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845096500422428773206401 2883822375316821579904801)
                  ·
                    refine ⟨2162866781487616184928601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2883822375316821579904801 2162866781487616184928601)
                    ·
                      refine ⟨1622150086115712138696451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2162866781487616184928601 1622150086115712138696451)
                      ·
                        rfl

theorem cell23_3159126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_3159126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159126 prefixEnd_3159126 := by exact prefixLift 3159126
  have htrace : WordTrace (prefixWord ++ tailWord_3159126) baseStart_3159126 baseEnd_3159126 := by
    simpa [prefixWord, tailWord_3159126, baseEnd_3159126] using wordTrace_append hprefix tailTrace_3159126
  have hstable : (prefixWord ++ tailWord_3159126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159126).length < 2 ^ (prefixWord ++ tailWord_3159126).sum := by decide
  have hdescent : baseEnd_3159126 < baseStart_3159126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159151 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 3]
def baseStart_3159151 : Nat := 118140960795 + 3159151 * 2 ^ 59
def prefixEnd_3159151 : Nat := 4983230072969 + 3 ^ 40 * 3159151 * 2
def baseEnd_3159151 : Nat := 1622162923132074540883835

theorem tailTrace_3159151 : CollatzResearch.WordTrace tailWord_3159151 prefixEnd_3159151 1622162923132074540883835 := by
  unfold tailWord_3159151
  simp only [CollatzResearch.WordTrace]
  refine ⟨115223702977942941880933307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76815801985295294587288871 115223702977942941880933307)
  ·
    refine ⟨172835554466914412821399961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115223702977942941880933307 172835554466914412821399961)
    ·
      refine ⟨129626665850185809616049971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172835554466914412821399961 129626665850185809616049971)
      ·
        refine ⟨194439998775278714424074957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129626665850185809616049971 194439998775278714424074957)
        ·
          refine ⟨72914999540729517909028109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194439998775278714424074957 72914999540729517909028109)
          ·
            refine ⟨27343124827773569215885541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72914999540729517909028109 27343124827773569215885541)
            ·
              refine ⟨5126835905207544227978539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27343124827773569215885541 5126835905207544227978539)
              ·
                refine ⟨7690253857811316341967809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126835905207544227978539 7690253857811316341967809)
                ·
                  refine ⟨5767690393358487256475857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690253857811316341967809 5767690393358487256475857)
                  ·
                    refine ⟨4325767795018865442356893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767690393358487256475857 4325767795018865442356893)
                    ·
                      refine ⟨1622162923132074540883835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4325767795018865442356893 1622162923132074540883835)
                      ·
                        rfl

theorem cell23_3159151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_3159151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159151 prefixEnd_3159151 := by exact prefixLift 3159151
  have htrace : WordTrace (prefixWord ++ tailWord_3159151) baseStart_3159151 baseEnd_3159151 := by
    simpa [prefixWord, tailWord_3159151, baseEnd_3159151] using wordTrace_append hprefix tailTrace_3159151
  have hstable : (prefixWord ++ tailWord_3159151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159151).length < 2 ^ (prefixWord ++ tailWord_3159151).sum := by decide
  have hdescent : baseEnd_3159151 < baseStart_3159151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159166 : List Nat := [4, 2, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3159166 : Nat := 118140960795 + 3159166 * 2 ^ 59
def prefixEnd_3159166 : Nat := 4983230072969 + 3 ^ 40 * 3159166 * 2
def baseEnd_3159166 : Nat := 180241180593543553577363

theorem tailTrace_3159166 : CollatzResearch.WordTrace tailWord_3159166 prefixEnd_3159166 180241180593543553577363 := by
  unfold tailWord_3159166
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403031259111074930341169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76816166715259066295152901 14403031259111074930341169)
  ·
    refine ⟨10802273444333306197755877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14403031259111074930341169 10802273444333306197755877)
    ·
      refine ⟨2025426270812494912079227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10802273444333306197755877 2025426270812494912079227)
      ·
        refine ⟨3038139406218742368118841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025426270812494912079227 3038139406218742368118841)
        ·
          refine ⟨2278604554664056776089131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3038139406218742368118841 2278604554664056776089131)
          ·
            refine ⟨3417906831996085164133697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278604554664056776089131 3417906831996085164133697)
            ·
              refine ⟨2563430123997063873100273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3417906831996085164133697 2563430123997063873100273)
              ·
                refine ⟨1922572592997797904825205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2563430123997063873100273 1922572592997797904825205)
                ·
                  refine ⟨180241180593543553577363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1922572592997797904825205 180241180593543553577363)
                  ·
                    rfl

theorem cell23_3159166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3159166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159166 prefixEnd_3159166 := by exact prefixLift 3159166
  have htrace : WordTrace (prefixWord ++ tailWord_3159166) baseStart_3159166 baseEnd_3159166 := by
    simpa [prefixWord, tailWord_3159166, baseEnd_3159166] using wordTrace_append hprefix tailTrace_3159166
  have hstable : (prefixWord ++ tailWord_3159166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159166).length < 2 ^ (prefixWord ++ tailWord_3159166).sum := by decide
  have hdescent : baseEnd_3159166 < baseStart_3159166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159201 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 1, 5]
def baseStart_3159201 : Nat := 118140960795 + 3159201 * 2 ^ 59
def prefixEnd_3159201 : Nat := 4983230072969 + 3 ^ 40 * 3159201 * 2
def baseEnd_3159201 : Nat := 540729532388266448419535

theorem tailTrace_3159201 : CollatzResearch.WordTrace tailWord_3159201 prefixEnd_3159201 540729532388266448419535 := by
  unfold tailWord_3159201
  simp only [CollatzResearch.WordTrace]
  refine ⟨115225526627761800420253457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76817017751841200280168971 115225526627761800420253457)
  ·
    refine ⟨86419144970821350315190093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115225526627761800420253457 86419144970821350315190093)
    ·
      refine ⟨32407179364058006368196285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86419144970821350315190093 32407179364058006368196285)
      ·
        refine ⟨12152692261521752388073607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32407179364058006368196285 12152692261521752388073607)
        ·
          refine ⟨18229038392282628582110411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12152692261521752388073607 18229038392282628582110411)
          ·
            refine ⟨27343557588423942873165617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18229038392282628582110411 27343557588423942873165617)
            ·
              refine ⟨20507668191317957154874213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27343557588423942873165617 20507668191317957154874213)
              ·
                refine ⟨3845187785872116966538915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20507668191317957154874213 3845187785872116966538915)
                ·
                  refine ⟨5767781678808175449808373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845187785872116966538915 5767781678808175449808373)
                  ·
                    refine ⟨540729532388266448419535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5767781678808175449808373 540729532388266448419535)
                    ·
                      rfl

theorem cell23_3159201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_3159201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159201 prefixEnd_3159201 := by exact prefixLift 3159201
  have htrace : WordTrace (prefixWord ++ tailWord_3159201) baseStart_3159201 baseEnd_3159201 := by
    simpa [prefixWord, tailWord_3159201, baseEnd_3159201] using wordTrace_append hprefix tailTrace_3159201
  have hstable : (prefixWord ++ tailWord_3159201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159201).length < 2 ^ (prefixWord ++ tailWord_3159201).sum := by decide
  have hdescent : baseEnd_3159201 < baseStart_3159201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159202 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_3159202 : Nat := 118140960795 + 3159202 * 2 ^ 59
def prefixEnd_3159202 : Nat := 4983230072969 + 3 ^ 40 * 3159202 * 2
def baseEnd_3159202 : Nat := 1622189110645453841346101

theorem tailTrace_3159202 : CollatzResearch.WordTrace tailWord_3159202 prefixEnd_3159202 1622189110645453841346101 := by
  unfold tailWord_3159202
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806390775189544397759965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76817042067172118394026573 28806390775189544397759965)
  ·
    refine ⟨10802396540696079149159987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28806390775189544397759965 10802396540696079149159987)
    ·
      refine ⟨16203594811044118723739981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802396540696079149159987 16203594811044118723739981)
      ·
        refine ⟨6076348054141544521402493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16203594811044118723739981 6076348054141544521402493)
        ·
          refine ⟨2278630520303079195525935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6076348054141544521402493 2278630520303079195525935)
          ·
            refine ⟨3417945780454618793288903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278630520303079195525935 3417945780454618793288903)
            ·
              refine ⟨5126918670681928189933355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417945780454618793288903 5126918670681928189933355)
              ·
                refine ⟨7690378006022892284900033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5126918670681928189933355 7690378006022892284900033)
                ·
                  refine ⟨5767783504517169213675025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690378006022892284900033 5767783504517169213675025)
                  ·
                    refine ⟨4325837628387876910256269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5767783504517169213675025 4325837628387876910256269)
                    ·
                      refine ⟨1622189110645453841346101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4325837628387876910256269 1622189110645453841346101)
                      ·
                        rfl

theorem cell23_3159202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_3159202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159202 prefixEnd_3159202 := by exact prefixLift 3159202
  have htrace : WordTrace (prefixWord ++ tailWord_3159202) baseStart_3159202 baseEnd_3159202 := by
    simpa [prefixWord, tailWord_3159202, baseEnd_3159202] using wordTrace_append hprefix tailTrace_3159202
  have hstable : (prefixWord ++ tailWord_3159202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159202).length < 2 ^ (prefixWord ++ tailWord_3159202).sum := by decide
  have hdescent : baseEnd_3159202 < baseStart_3159202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159218 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_3159218 : Nat := 118140960795 + 3159218 * 2 ^ 59
def prefixEnd_3159218 : Nat := 4983230072969 + 3 ^ 40 * 3159218 * 2
def baseEnd_3159218 : Nat := 540732442111975259582009

theorem tailTrace_3159218 : CollatzResearch.WordTrace tailWord_3159218 prefixEnd_3159218 540732442111975259582009 := by
  unfold tailWord_3159218
  simp only [CollatzResearch.WordTrace]
  refine ⟨28806536667175053080905577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76817431112466808215748205 28806536667175053080905577)
  ·
    refine ⟨21604902500381289810679183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28806536667175053080905577 21604902500381289810679183)
    ·
      refine ⟨32407353750571934716018775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21604902500381289810679183 32407353750571934716018775)
      ·
        refine ⟨48611030625857902074028163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32407353750571934716018775 48611030625857902074028163)
        ·
          refine ⟨72916545938786853111042245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48611030625857902074028163 72916545938786853111042245)
          ·
            refine ⟨13671852363522534958320421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72916545938786853111042245 13671852363522534958320421)
            ·
              refine ⟨2563472318160475304685079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13671852363522534958320421 2563472318160475304685079)
              ·
                refine ⟨3845208477240712957027619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563472318160475304685079 3845208477240712957027619)
                ·
                  refine ⟨5767812715861069435541429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845208477240712957027619 5767812715861069435541429)
                  ·
                    refine ⟨540732442111975259582009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5767812715861069435541429 540732442111975259582009)
                    ·
                      rfl

theorem cell23_3159218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_3159218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159218 prefixEnd_3159218 := by exact prefixLift 3159218
  have htrace : WordTrace (prefixWord ++ tailWord_3159218) baseStart_3159218 baseEnd_3159218 := by
    simpa [prefixWord, tailWord_3159218, baseEnd_3159218] using wordTrace_append hprefix tailTrace_3159218
  have hstable : (prefixWord ++ tailWord_3159218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159218).length < 2 ^ (prefixWord ++ tailWord_3159218).sum := by decide
  have hdescent : baseEnd_3159218 < baseStart_3159218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159222 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 6]
def baseStart_3159222 : Nat := 118140960795 + 3159222 * 2 ^ 59
def prefixEnd_3159222 : Nat := 4983230072969 + 3 ^ 40 * 3159222 * 2
def baseEnd_3159222 : Nat := 180244375584282640344001

theorem tailTrace_3159222 : CollatzResearch.WordTrace tailWord_3159222 prefixEnd_3159222 180244375584282640344001 := by
  unfold tailWord_3159222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201643285042857562922995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76817528373790480671178613 7201643285042857562922995)
  ·
    refine ⟨10802464927564286344384493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7201643285042857562922995 10802464927564286344384493)
    ·
      refine ⟨4050924347836607379144185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10802464927564286344384493 4050924347836607379144185)
      ·
        refine ⟨3038193260877455534358139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4050924347836607379144185 3038193260877455534358139)
        ·
          refine ⟨4557289891316183301537209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038193260877455534358139 4557289891316183301537209)
          ·
            refine ⟨3417967418487137476152907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4557289891316183301537209 3417967418487137476152907)
            ·
              refine ⟨5126951127730706214229361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3417967418487137476152907 5126951127730706214229361)
              ·
                refine ⟨3845213345798029660672021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5126951127730706214229361 3845213345798029660672021)
                ·
                  refine ⟨180244375584282640344001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3845213345798029660672021 180244375584282640344001)
                  ·
                    rfl

theorem cell23_3159222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_3159222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159222 prefixEnd_3159222 := by exact prefixLift 3159222
  have htrace : WordTrace (prefixWord ++ tailWord_3159222) baseStart_3159222 baseEnd_3159222 := by
    simpa [prefixWord, tailWord_3159222, baseEnd_3159222] using wordTrace_append hprefix tailTrace_3159222
  have hstable : (prefixWord ++ tailWord_3159222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159222).length < 2 ^ (prefixWord ++ tailWord_3159222).sum := by decide
  have hdescent : baseEnd_3159222 < baseStart_3159222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159331 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5]
def baseStart_3159331 : Nat := 118140960795 + 3159331 * 2 ^ 59
def prefixEnd_3159331 : Nat := 4983230072969 + 3 ^ 40 * 3159331 * 2
def baseEnd_3159331 : Nat := 1622255349649883836633007

theorem tailTrace_3159331 : CollatzResearch.WordTrace tailWord_3159331 prefixEnd_3159331 1622255349649883836633007 := by
  unfold tailWord_3159331
  simp only [CollatzResearch.WordTrace]
  refine ⟨115230268117290832622485847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76820178744860555081657231 115230268117290832622485847)
  ·
    refine ⟨172845402175936248933728771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115230268117290832622485847 172845402175936248933728771)
    ·
      refine ⟨259268103263904373400593157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172845402175936248933728771 259268103263904373400593157)
      ·
        refine ⟨48612769361982070012611217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 259268103263904373400593157 48612769361982070012611217)
        ·
          refine ⟨36459577021486552509458413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48612769361982070012611217 36459577021486552509458413)
          ·
            refine ⟨13672341383057457191046905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36459577021486552509458413 13672341383057457191046905)
            ·
              refine ⟨10254256037293092893285179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13672341383057457191046905 10254256037293092893285179)
              ·
                refine ⟨15381384055939639339927769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254256037293092893285179 15381384055939639339927769)
                ·
                  refine ⟨11536038041954729504945827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15381384055939639339927769 11536038041954729504945827)
                  ·
                    refine ⟨17304057062932094257418741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11536038041954729504945827 17304057062932094257418741)
                    ·
                      refine ⟨1622255349649883836633007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17304057062932094257418741 1622255349649883836633007)
                      ·
                        rfl

theorem cell23_3159331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_3159331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159331 prefixEnd_3159331 := by exact prefixLift 3159331
  have htrace : WordTrace (prefixWord ++ tailWord_3159331) baseStart_3159331 baseEnd_3159331 := by
    simpa [prefixWord, tailWord_3159331, baseEnd_3159331] using wordTrace_append hprefix tailTrace_3159331
  have hstable : (prefixWord ++ tailWord_3159331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159331).length < 2 ^ (prefixWord ++ tailWord_3159331).sum := by decide
  have hdescent : baseEnd_3159331 < baseStart_3159331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159332 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_3159332 : Nat := 118140960795 + 3159332 * 2 ^ 59
def prefixEnd_3159332 : Nat := 4983230072969 + 3 ^ 40 * 3159332 * 2
def baseEnd_3159332 : Nat := 1622255863130538332720503

theorem tailTrace_3159332 : CollatzResearch.WordTrace tailWord_3159332 prefixEnd_3159332 1622255863130538332720503 := by
  unfold tailWord_3159332
  simp only [CollatzResearch.WordTrace]
  refine ⟨57615152295143604896636125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76820203060191473195514833 57615152295143604896636125)
  ·
    refine ⟨21605682110678851836238547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57615152295143604896636125 21605682110678851836238547)
    ·
      refine ⟨32408523166018277754357821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21605682110678851836238547 32408523166018277754357821)
      ·
        refine ⟨12153196187256854157884183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32408523166018277754357821 12153196187256854157884183)
        ·
          refine ⟨18229794280885281236826275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12153196187256854157884183 18229794280885281236826275)
          ·
            refine ⟨27344691421327921855239413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18229794280885281236826275 27344691421327921855239413)
            ·
              refine ⟨2563564820749492673928695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27344691421327921855239413 2563564820749492673928695)
              ·
                refine ⟨3845347231124239010893043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563564820749492673928695 3845347231124239010893043)
                ·
                  refine ⟨5768020846686358516339565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845347231124239010893043 5768020846686358516339565)
                  ·
                    refine ⟨2163007817507384443627337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5768020846686358516339565 2163007817507384443627337)
                    ·
                      refine ⟨1622255863130538332720503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163007817507384443627337 1622255863130538332720503)
                      ·
                        rfl

theorem cell23_3159332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_3159332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159332 prefixEnd_3159332 := by exact prefixLift 3159332
  have htrace : WordTrace (prefixWord ++ tailWord_3159332) baseStart_3159332 baseEnd_3159332 := by
    simpa [prefixWord, tailWord_3159332, baseEnd_3159332] using wordTrace_append hprefix tailTrace_3159332
  have hstable : (prefixWord ++ tailWord_3159332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159332).length < 2 ^ (prefixWord ++ tailWord_3159332).sum := by decide
  have hdescent : baseEnd_3159332 < baseStart_3159332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159348 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_3159348 : Nat := 118140960795 + 3159348 * 2 ^ 59
def prefixEnd_3159348 : Nat := 4983230072969 + 3 ^ 40 * 3159348 * 2
def baseEnd_3159348 : Nat := 1622264078821010270120429

theorem tailTrace_3159348 : CollatzResearch.WordTrace tailWord_3159348 prefixEnd_3159348 1622264078821010270120429 := by
  unfold tailWord_3159348
  simp only [CollatzResearch.WordTrace]
  refine ⟨57615444079114622262927349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76820592105486163017236465 57615444079114622262927349)
  ·
    refine ⟨5401447882416995837149439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57615444079114622262927349 5401447882416995837149439)
    ·
      refine ⟨8102171823625493755724159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5401447882416995837149439 8102171823625493755724159)
      ·
        refine ⟨12153257735438240633586239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102171823625493755724159 12153257735438240633586239)
        ·
          refine ⟨18229886603157360950379359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12153257735438240633586239 18229886603157360950379359)
          ·
            refine ⟨27344829904736041425569039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18229886603157360950379359 27344829904736041425569039)
            ·
              refine ⟨41017244857104062138353559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27344829904736041425569039 41017244857104062138353559)
              ·
                refine ⟨61525867285656093207530339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41017244857104062138353559 61525867285656093207530339)
                ·
                  refine ⟨92288800928484139811295509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61525867285656093207530339 92288800928484139811295509)
                  ·
                    refine ⟨4326037543522694053654477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92288800928484139811295509 4326037543522694053654477)
                    ·
                      refine ⟨1622264078821010270120429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4326037543522694053654477 1622264078821010270120429)
                      ·
                        rfl

theorem cell23_3159348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_3159348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159348 prefixEnd_3159348 := by exact prefixLift 3159348
  have htrace : WordTrace (prefixWord ++ tailWord_3159348) baseStart_3159348 baseEnd_3159348 := by
    simpa [prefixWord, tailWord_3159348, baseEnd_3159348] using wordTrace_append hprefix tailTrace_3159348
  have hstable : (prefixWord ++ tailWord_3159348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159348).length < 2 ^ (prefixWord ++ tailWord_3159348).sum := by decide
  have hdescent : baseEnd_3159348 < baseStart_3159348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159358 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_3159358 : Nat := 118140960795 + 3159358 * 2 ^ 59
def prefixEnd_3159358 : Nat := 4983230072969 + 3 ^ 40 * 3159358 * 2
def baseEnd_3159358 : Nat := 1622269213627555230995383

theorem tailTrace_3159358 : CollatzResearch.WordTrace tailWord_3159358 prefixEnd_3159358 1622269213627555230995383 := by
  unfold tailWord_3159358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403906611024127029214841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76820835258795344155812485 14403906611024127029214841)
  ·
    refine ⟨10802929958268095271911131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14403906611024127029214841 10802929958268095271911131)
    ·
      refine ⟨16204394937402142907866697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10802929958268095271911131 16204394937402142907866697)
      ·
        refine ⟨12153296203051607180900023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16204394937402142907866697 12153296203051607180900023)
        ·
          refine ⟨18229944304577410771350035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12153296203051607180900023 18229944304577410771350035)
          ·
            refine ⟨27344916456866116157025053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18229944304577410771350035 27344916456866116157025053)
            ·
              refine ⟨10254343671324793558884395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27344916456866116157025053 10254343671324793558884395)
              ·
                refine ⟨15381515506987190338326593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254343671324793558884395 15381515506987190338326593)
                ·
                  refine ⟨11536136630240392753744945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15381515506987190338326593 11536136630240392753744945)
                  ·
                    refine ⟨8652102472680294565308709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11536136630240392753744945 8652102472680294565308709)
                    ·
                      refine ⟨1622269213627555230995383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8652102472680294565308709 1622269213627555230995383)
                      ·
                        rfl

theorem cell23_3159358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_3159358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159358 prefixEnd_3159358 := by exact prefixLift 3159358
  have htrace : WordTrace (prefixWord ++ tailWord_3159358) baseStart_3159358 baseEnd_3159358 := by
    simpa [prefixWord, tailWord_3159358, baseEnd_3159358] using wordTrace_append hprefix tailTrace_3159358
  have hstable : (prefixWord ++ tailWord_3159358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159358).length < 2 ^ (prefixWord ++ tailWord_3159358).sum := by decide
  have hdescent : baseEnd_3159358 < baseStart_3159358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159452 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3159452 : Nat := 118140960795 + 3159452 * 2 ^ 59
def prefixEnd_3159452 : Nat := 4983230072969 + 3 ^ 40 * 3159452 * 2
def baseEnd_3159452 : Nat := 1622317480809077863219951

theorem tailTrace_3159452 : CollatzResearch.WordTrace tailWord_3159452 prefixEnd_3159452 1622317480809077863219951 := by
  unfold tailWord_3159452
  simp only [CollatzResearch.WordTrace]
  refine ⟨57617340674926235143820305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76823120899901646858427073 57617340674926235143820305)
  ·
    refine ⟨43213005506194676357865229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57617340674926235143820305 43213005506194676357865229)
    ·
      refine ⟨16204877064823003634199461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43213005506194676357865229 16204877064823003634199461)
      ·
        refine ⟨3038414449654313181412399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16204877064823003634199461 3038414449654313181412399)
        ·
          refine ⟨4557621674481469772118599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038414449654313181412399 4557621674481469772118599)
          ·
            refine ⟨6836432511722204658177899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4557621674481469772118599 6836432511722204658177899)
            ·
              refine ⟨10254648767583306987266849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836432511722204658177899 10254648767583306987266849)
              ·
                refine ⟨7690986575687480240450137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10254648767583306987266849 7690986575687480240450137)
                ·
                  refine ⟨5768239931765610180337603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690986575687480240450137 5768239931765610180337603)
                  ·
                    refine ⟨8652359897648415270506405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768239931765610180337603 8652359897648415270506405)
                    ·
                      refine ⟨1622317480809077863219951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8652359897648415270506405 1622317480809077863219951)
                      ·
                        rfl

theorem cell23_3159452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3159452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159452 prefixEnd_3159452 := by exact prefixLift 3159452
  have htrace : WordTrace (prefixWord ++ tailWord_3159452) baseStart_3159452 baseEnd_3159452 := by
    simpa [prefixWord, tailWord_3159452, baseEnd_3159452] using wordTrace_append hprefix tailTrace_3159452
  have hstable : (prefixWord ++ tailWord_3159452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159452).length < 2 ^ (prefixWord ++ tailWord_3159452).sum := by decide
  have hdescent : baseEnd_3159452 < baseStart_3159452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159455 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 3]
def baseStart_3159455 : Nat := 118140960795 + 3159455 * 2 ^ 59
def prefixEnd_3159455 : Nat := 4983230072969 + 3 ^ 40 * 3159455 * 2
def baseEnd_3159455 : Nat := 1622319021251041351482437

theorem tailTrace_3159455 : CollatzResearch.WordTrace tailWord_3159455 prefixEnd_3159455 1622319021251041351482437 := by
  unfold tailWord_3159455
  simp only [CollatzResearch.WordTrace]
  refine ⟨115234790768841601799999819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76823193845894401199999879 115234790768841601799999819)
  ·
    refine ⟨172852186153262402699999729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115234790768841601799999819 172852186153262402699999729)
    ·
      refine ⟨129639139614946802024999797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172852186153262402699999729 129639139614946802024999797)
      ·
        refine ⟨12153669338901262689843731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129639139614946802024999797 12153669338901262689843731)
        ·
          refine ⟨18230504008351894034765597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12153669338901262689843731 18230504008351894034765597)
          ·
            refine ⟨6836439003131960263037099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18230504008351894034765597 6836439003131960263037099)
            ·
              refine ⟨10254658504697940394555649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836439003131960263037099 10254658504697940394555649)
              ·
                refine ⟨7690993878523455295916737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10254658504697940394555649 7690993878523455295916737)
                ·
                  refine ⟨5768245408892591471937553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7690993878523455295916737 5768245408892591471937553)
                  ·
                    refine ⟨4326184056669443603953165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768245408892591471937553 4326184056669443603953165)
                    ·
                      refine ⟨1622319021251041351482437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4326184056669443603953165 1622319021251041351482437)
                      ·
                        rfl

theorem cell23_3159455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_3159455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159455 prefixEnd_3159455 := by exact prefixLift 3159455
  have htrace : WordTrace (prefixWord ++ tailWord_3159455) baseStart_3159455 baseEnd_3159455 := by
    simpa [prefixWord, tailWord_3159455, baseEnd_3159455] using wordTrace_append hprefix tailTrace_3159455
  have hstable : (prefixWord ++ tailWord_3159455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159455).length < 2 ^ (prefixWord ++ tailWord_3159455).sum := by decide
  have hdescent : baseEnd_3159455 < baseStart_3159455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159458 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 8]
def baseStart_3159458 : Nat := 118140960795 + 3159458 * 2 ^ 59
def prefixEnd_3159458 : Nat := 4983230072969 + 3 ^ 40 * 3159458 * 2
def baseEnd_3159458 : Nat := 180257840188111648860547

theorem tailTrace_3159458 : CollatzResearch.WordTrace tailWord_3159458 prefixEnd_3159458 180257840188111648860547 := by
  unfold tailWord_3159458
  simp only [CollatzResearch.WordTrace]
  refine ⟨28808725046957683328089757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76823266791887155541572685 28808725046957683328089757)
  ·
    refine ⟨10803271892609131248033659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28808725046957683328089757 10803271892609131248033659)
    ·
      refine ⟨16204907838913696872050489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10803271892609131248033659 16204907838913696872050489)
      ·
        refine ⟨12153680879185272654037867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16204907838913696872050489 12153680879185272654037867)
        ·
          refine ⟨18230521318777908981056801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12153680879185272654037867 18230521318777908981056801)
          ·
            refine ⟨13672890989083431735792601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18230521318777908981056801 13672890989083431735792601)
            ·
              refine ⟨10254668241812573801844451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13672890989083431735792601 10254668241812573801844451)
              ·
                refine ⟨15382002362718860702766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10254668241812573801844451 15382002362718860702766677)
                ·
                  refine ⟨180257840188111648860547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15382002362718860702766677 180257840188111648860547)
                  ·
                    rfl

theorem cell23_3159458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_3159458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159458 prefixEnd_3159458 := by exact prefixLift 3159458
  have htrace : WordTrace (prefixWord ++ tailWord_3159458) baseStart_3159458 baseEnd_3159458 := by
    simpa [prefixWord, tailWord_3159458, baseEnd_3159458] using wordTrace_append hprefix tailTrace_3159458
  have hstable : (prefixWord ++ tailWord_3159458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159458).length < 2 ^ (prefixWord ++ tailWord_3159458).sum := by decide
  have hdescent : baseEnd_3159458 < baseStart_3159458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159461 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 6]
def baseStart_3159461 : Nat := 118140960795 + 3159461 * 2 ^ 59
def prefixEnd_3159461 : Nat := 4983230072969 + 3 ^ 40 * 3159461 * 2
def baseEnd_3159461 : Nat := 1622322102134968328007409

theorem tailTrace_3159461 : CollatzResearch.WordTrace tailWord_3159461 prefixEnd_3159461 1622322102134968328007409 := by
  unfold tailWord_3159461
  simp only [CollatzResearch.WordTrace]
  refine ⟨115235009606819864824718237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76823339737879909883145491 115235009606819864824718237)
  ·
    refine ⟨43213128602557449309269339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115235009606819864824718237 43213128602557449309269339)
    ·
      refine ⟨64819692903836173963904009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43213128602557449309269339 64819692903836173963904009)
      ·
        refine ⟨48614769677877130472928007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64819692903836173963904009 48614769677877130472928007)
        ·
          refine ⟨72922154516815695709392011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48614769677877130472928007 72922154516815695709392011)
          ·
            refine ⟨109383231775223543564088017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72922154516815695709392011 109383231775223543564088017)
            ·
              refine ⟨82037423831417657673066013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109383231775223543564088017 82037423831417657673066013)
              ·
                refine ⟨30764033936781621627399755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82037423831417657673066013 30764033936781621627399755)
                ·
                  refine ⟨46146050905172432441099633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30764033936781621627399755 46146050905172432441099633)
                  ·
                    refine ⟨34609538178879324330824725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46146050905172432441099633 34609538178879324330824725)
                    ·
                      refine ⟨1622322102134968328007409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34609538178879324330824725 1622322102134968328007409)
                      ·
                        rfl

theorem cell23_3159461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_3159461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159461 prefixEnd_3159461 := by exact prefixLift 3159461
  have htrace : WordTrace (prefixWord ++ tailWord_3159461) baseStart_3159461 baseEnd_3159461 := by
    simpa [prefixWord, tailWord_3159461, baseEnd_3159461] using wordTrace_append hprefix tailTrace_3159461
  have hstable : (prefixWord ++ tailWord_3159461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159461).length < 2 ^ (prefixWord ++ tailWord_3159461).sum := by decide
  have hdescent : baseEnd_3159461 < baseStart_3159461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159485 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_3159485 : Nat := 118140960795 + 3159485 * 2 ^ 59
def prefixEnd_3159485 : Nat := 4983230072969 + 3 ^ 40 * 3159485 * 2
def baseEnd_3159485 : Nat := 1622334425670676234107299

theorem tailTrace_3159485 : CollatzResearch.WordTrace tailWord_3159485 prefixEnd_3159485 1622334425670676234107299 := by
  unfold tailWord_3159485
  simp only [CollatzResearch.WordTrace]
  refine ⟨115235884958732916923591909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76823923305821944615727939 115235884958732916923591909)
  ·
    refine ⟨21606728429762421923173483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115235884958732916923591909 21606728429762421923173483)
    ·
      refine ⟨32410092644643632884760225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21606728429762421923173483 32410092644643632884760225)
      ·
        refine ⟨24307569483482724663570169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32410092644643632884760225 24307569483482724663570169)
        ·
          refine ⟨18230677112612043497677627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24307569483482724663570169 18230677112612043497677627)
          ·
            refine ⟨27346015668918065246516441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18230677112612043497677627 27346015668918065246516441)
            ·
              refine ⟨20509511751688548934887331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27346015668918065246516441 20509511751688548934887331)
              ·
                refine ⟨30764267627532823402330997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20509511751688548934887331 30764267627532823402330997)
                ·
                  refine ⟨2884150090081202193968531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30764267627532823402330997 2884150090081202193968531)
                  ·
                    refine ⟨4326225135121803290952797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2884150090081202193968531 4326225135121803290952797)
                    ·
                      refine ⟨1622334425670676234107299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4326225135121803290952797 1622334425670676234107299)
                      ·
                        rfl

theorem cell23_3159485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_3159485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159485 prefixEnd_3159485 := by exact prefixLift 3159485
  have htrace : WordTrace (prefixWord ++ tailWord_3159485) baseStart_3159485 baseEnd_3159485 := by
    simpa [prefixWord, tailWord_3159485, baseEnd_3159485] using wordTrace_append hprefix tailTrace_3159485
  have hstable : (prefixWord ++ tailWord_3159485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159485).length < 2 ^ (prefixWord ++ tailWord_3159485).sum := by decide
  have hdescent : baseEnd_3159485 < baseStart_3159485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159525 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3159525 : Nat := 118140960795 + 3159525 * 2 ^ 59
def prefixEnd_3159525 : Nat := 4983230072969 + 3 ^ 40 * 3159525 * 2
def baseEnd_3159525 : Nat := 1622354964896856077607115

theorem tailTrace_3159525 : CollatzResearch.WordTrace tailWord_3159525 prefixEnd_3159525 1622354964896856077607115 := by
  unfold tailWord_3159525
  simp only [CollatzResearch.WordTrace]
  refine ⟨115237343878588003755048029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76824895919058669170032019 115237343878588003755048029)
  ·
    refine ⟨43214003954470501408143011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115237343878588003755048029 43214003954470501408143011)
    ·
      refine ⟨64821005931705752112214517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43214003954470501408143011 64821005931705752112214517)
      ·
        refine ⟨6076969306097414260520111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64821005931705752112214517 6076969306097414260520111)
        ·
          refine ⟨9115453959146121390780167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076969306097414260520111 9115453959146121390780167)
          ·
            refine ⟨13673180938719182086170251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9115453959146121390780167 13673180938719182086170251)
            ·
              refine ⟨20509771408078773129255377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13673180938719182086170251 20509771408078773129255377)
              ·
                refine ⟨15382328556059079846941533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20509771408078773129255377 15382328556059079846941533)
                ·
                  refine ⟨5768373208522154942603075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15382328556059079846941533 5768373208522154942603075)
                  ·
                    refine ⟨8652559812783232413904613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768373208522154942603075 8652559812783232413904613)
                    ·
                      refine ⟨1622354964896856077607115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8652559812783232413904613 1622354964896856077607115)
                      ·
                        rfl

theorem cell23_3159525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3159525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159525 prefixEnd_3159525 := by exact prefixLift 3159525
  have htrace : WordTrace (prefixWord ++ tailWord_3159525) baseStart_3159525 baseEnd_3159525 := by
    simpa [prefixWord, tailWord_3159525, baseEnd_3159525] using wordTrace_append hprefix tailTrace_3159525
  have hstable : (prefixWord ++ tailWord_3159525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159525).length < 2 ^ (prefixWord ++ tailWord_3159525).sum := by decide
  have hdescent : baseEnd_3159525 < baseStart_3159525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159528 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_3159528 : Nat := 118140960795 + 3159528 * 2 ^ 59
def prefixEnd_3159528 : Nat := 4983230072969 + 3 ^ 40 * 3159528 * 2
def baseEnd_3159528 : Nat := 1622356505338819565869601

theorem tailTrace_3159528 : CollatzResearch.WordTrace tailWord_3159528 prefixEnd_3159528 1622356505338819565869601 := by
  unfold tailWord_3159528
  simp only [CollatzResearch.WordTrace]
  refine ⟨57618726648788567633703619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76824968865051423511604825 57618726648788567633703619)
  ·
    refine ⟨86428089973182851450555429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57618726648788567633703619 86428089973182851450555429)
    ·
      refine ⟨16205266869971784646979143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86428089973182851450555429 16205266869971784646979143)
      ·
        refine ⟨24307900304957676970468715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16205266869971784646979143 24307900304957676970468715)
        ·
          refine ⟨36461850457436515455703073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24307900304957676970468715 36461850457436515455703073)
          ·
            refine ⟨27346387843077386591777305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36461850457436515455703073 27346387843077386591777305)
            ·
              refine ⟨20509790882308039943832979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27346387843077386591777305 20509790882308039943832979)
              ·
                refine ⟨30764686323462059915749469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20509790882308039943832979 30764686323462059915749469)
                ·
                  refine ⟨11536757371298272468406051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30764686323462059915749469 11536757371298272468406051)
                  ·
                    refine ⟨17305136056947408702609077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11536757371298272468406051 17305136056947408702609077)
                    ·
                      refine ⟨1622356505338819565869601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17305136056947408702609077 1622356505338819565869601)
                      ·
                        rfl

theorem cell23_3159528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_3159528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159528 prefixEnd_3159528 := by exact prefixLift 3159528
  have htrace : WordTrace (prefixWord ++ tailWord_3159528) baseStart_3159528 baseEnd_3159528 := by
    simpa [prefixWord, tailWord_3159528, baseEnd_3159528] using wordTrace_append hprefix tailTrace_3159528
  have hstable : (prefixWord ++ tailWord_3159528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159528).length < 2 ^ (prefixWord ++ tailWord_3159528).sum := by decide
  have hdescent : baseEnd_3159528 < baseStart_3159528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159531 : List Nat := [1, 1, 1, 1, 2, 3, 2, 12]
def baseStart_3159531 : Nat := 118140960795 + 3159531 * 2 ^ 59
def prefixEnd_3159531 : Nat := 4983230072969 + 3 ^ 40 * 3159531 * 2
def baseEnd_3159531 : Nat := 60087335028917890893781

theorem tailTrace_3159531 : CollatzResearch.WordTrace tailWord_3159531 prefixEnd_3159531 60087335028917890893781 := by
  unfold tailWord_3159531
  simp only [CollatzResearch.WordTrace]
  refine ⟨115237562716566266779766447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76825041811044177853177631 115237562716566266779766447)
  ·
    refine ⟨172856344074849400169649671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115237562716566266779766447 172856344074849400169649671)
    ·
      refine ⟨259284516112274100254474507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172856344074849400169649671 259284516112274100254474507)
      ·
        refine ⟨388926774168411150381711761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259284516112274100254474507 388926774168411150381711761)
        ·
          refine ⟨291695080626308362786283821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388926774168411150381711761 291695080626308362786283821)
          ·
            refine ⟨109385655234865636044856433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291695080626308362786283821 109385655234865636044856433)
            ·
              refine ⟨82039241426149227033642325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109385655234865636044856433 82039241426149227033642325)
              ·
                refine ⟨60087335028917890893781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 82039241426149227033642325 60087335028917890893781)
                ·
                  rfl

theorem cell23_3159531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 12].length) (baseStart_3159531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159531 prefixEnd_3159531 := by exact prefixLift 3159531
  have htrace : WordTrace (prefixWord ++ tailWord_3159531) baseStart_3159531 baseEnd_3159531 := by
    simpa [prefixWord, tailWord_3159531, baseEnd_3159531] using wordTrace_append hprefix tailTrace_3159531
  have hstable : (prefixWord ++ tailWord_3159531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159531).length < 2 ^ (prefixWord ++ tailWord_3159531).sum := by decide
  have hdescent : baseEnd_3159531 < baseStart_3159531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159535 : List Nat := [1, 1, 2, 1, 4, 1, 4, 3, 2, 4]
def baseStart_3159535 : Nat := 118140960795 + 3159535 * 2 ^ 59
def prefixEnd_3159535 : Nat := 4983230072969 + 3 ^ 40 * 3159535 * 2
def baseEnd_3159535 : Nat := 540786699901133679494023

theorem tailTrace_3159535 : CollatzResearch.WordTrace tailWord_3159535 prefixEnd_3159535 540786699901133679494023 := by
  unfold tailWord_3159535
  simp only [CollatzResearch.WordTrace]
  refine ⟨115237708608551775462912059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76825139072367850308608039 115237708608551775462912059)
  ·
    refine ⟨172856562912827663194368089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115237708608551775462912059 172856562912827663194368089)
    ·
      refine ⟨129642422184620747395776067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172856562912827663194368089 129642422184620747395776067)
      ·
        refine ⟨194463633276931121093664101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129642422184620747395776067 194463633276931121093664101)
        ·
          refine ⟨36461931239424585205062019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194463633276931121093664101 36461931239424585205062019)
          ·
            refine ⟨54692896859136877807593029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36461931239424585205062019 54692896859136877807593029)
            ·
              refine ⟨10254918161088164588923693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54692896859136877807593029 10254918161088164588923693)
              ·
                refine ⟨3845594310408061720846385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10254918161088164588923693 3845594310408061720846385)
                ·
                  refine ⟨2884195732806046290634789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845594310408061720846385 2884195732806046290634789)
                  ·
                    refine ⟨540786699901133679494023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2884195732806046290634789 540786699901133679494023)
                    ·
                      rfl

theorem cell23_3159535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 3, 2, 4].length) (baseStart_3159535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159535 prefixEnd_3159535 := by exact prefixLift 3159535
  have htrace : WordTrace (prefixWord ++ tailWord_3159535) baseStart_3159535 baseEnd_3159535 := by
    simpa [prefixWord, tailWord_3159535, baseEnd_3159535] using wordTrace_append hprefix tailTrace_3159535
  have hstable : (prefixWord ++ tailWord_3159535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159535).length < 2 ^ (prefixWord ++ tailWord_3159535).sum := by decide
  have hdescent : baseEnd_3159535 < baseStart_3159535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159545 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 3]
def baseStart_3159545 : Nat := 118140960795 + 3159545 * 2 ^ 59
def prefixEnd_3159545 : Nat := 4983230072969 + 3 ^ 40 * 3159545 * 2
def baseEnd_3159545 : Nat := 1622365234509945999357023

theorem tailTrace_3159545 : CollatzResearch.WordTrace tailWord_3159545 prefixEnd_3159545 1622365234509945999357023 := by
  unfold tailWord_3159545
  simp only [CollatzResearch.WordTrace]
  refine ⟨115238073338515547170776089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76825382225677031447184059 115238073338515547170776089)
  ·
    refine ⟨86428555003886660378082067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115238073338515547170776089 86428555003886660378082067)
    ·
      refine ⟨129642832505829990567123101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86428555003886660378082067 129642832505829990567123101)
      ·
        refine ⟨48616062189686246462671163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129642832505829990567123101 48616062189686246462671163)
        ·
          refine ⟨72924093284529369694006745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48616062189686246462671163 72924093284529369694006745)
          ·
            refine ⟨54693069963397027270505059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72924093284529369694006745 54693069963397027270505059)
            ·
              refine ⟨82039604945095540905757589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54693069963397027270505059 82039604945095540905757589)
              ·
                refine ⟨3845606481801353479957387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82039604945095540905757589 3845606481801353479957387)
                ·
                  refine ⟨5768409722702030219936081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845606481801353479957387 5768409722702030219936081)
                  ·
                    refine ⟨4326307292026522664952061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768409722702030219936081 4326307292026522664952061)
                    ·
                      refine ⟨1622365234509945999357023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4326307292026522664952061 1622365234509945999357023)
                      ·
                        rfl

theorem cell23_3159545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_3159545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159545 prefixEnd_3159545 := by exact prefixLift 3159545
  have htrace : WordTrace (prefixWord ++ tailWord_3159545) baseStart_3159545 baseEnd_3159545 := by
    simpa [prefixWord, tailWord_3159545, baseEnd_3159545] using wordTrace_append hprefix tailTrace_3159545
  have hstable : (prefixWord ++ tailWord_3159545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159545).length < 2 ^ (prefixWord ++ tailWord_3159545).sum := by decide
  have hdescent : baseEnd_3159545 < baseStart_3159545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159556 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_3159556 : Nat := 118140960795 + 3159556 * 2 ^ 59
def prefixEnd_3159556 : Nat := 4983230072969 + 3 ^ 40 * 3159556 * 2
def baseEnd_3159556 : Nat := 540790294265715152106491

theorem tailTrace_3159556 : CollatzResearch.WordTrace tailWord_3159556 prefixEnd_3159556 540790294265715152106491 := by
  unfold tailWord_3159556
  simp only [CollatzResearch.WordTrace]
  refine ⟨57619237270737848024713261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76825649694317130699617681 57619237270737848024713261)
  ·
    refine ⟨21607213976526693009267473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57619237270737848024713261 21607213976526693009267473)
    ·
      refine ⟨16205410482395019756950605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21607213976526693009267473 16205410482395019756950605)
      ·
        refine ⟨6077028930898132408856477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16205410482395019756950605 6077028930898132408856477)
        ·
          refine ⟨2278885849086799653321179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6077028930898132408856477 2278885849086799653321179)
          ·
            refine ⟨3418328773630199479981769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278885849086799653321179 3418328773630199479981769)
            ·
              refine ⟨2563746580222649609986327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418328773630199479981769 2563746580222649609986327)
              ·
                refine ⟨3845619870333974414979491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563746580222649609986327 3845619870333974414979491)
                ·
                  refine ⟨5768429805500961622469237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845619870333974414979491 5768429805500961622469237)
                  ·
                    refine ⟨540790294265715152106491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5768429805500961622469237 540790294265715152106491)
                    ·
                      rfl

theorem cell23_3159556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_3159556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159556 prefixEnd_3159556 := by exact prefixLift 3159556
  have htrace : WordTrace (prefixWord ++ tailWord_3159556) baseStart_3159556 baseEnd_3159556 := by
    simpa [prefixWord, tailWord_3159556, baseEnd_3159556] using wordTrace_append hprefix tailTrace_3159556
  have hstable : (prefixWord ++ tailWord_3159556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159556).length < 2 ^ (prefixWord ++ tailWord_3159556).sum := by decide
  have hdescent : baseEnd_3159556 < baseStart_3159556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159559 : List Nat := [1, 1, 4, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_3159559 : Nat := 118140960795 + 3159559 * 2 ^ 59
def prefixEnd_3159559 : Nat := 4983230072969 + 3 ^ 40 * 3159559 * 2
def baseEnd_3159559 : Nat := 1622372423239108944581959

theorem tailTrace_3159559 : CollatzResearch.WordTrace tailWord_3159559 prefixEnd_3159559 1622372423239108944581959 := by
  unfold tailWord_3159559
  simp only [CollatzResearch.WordTrace]
  refine ⟨115238583960464827561785731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76825722640309885041190487 115238583960464827561785731)
  ·
    refine ⟨172857875940697241342678597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115238583960464827561785731 172857875940697241342678597)
    ·
      refine ⟨32410851738880732751752237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172857875940697241342678597 32410851738880732751752237)
      ·
        refine ⟨12154069402080274781907089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32410851738880732751752237 12154069402080274781907089)
        ·
          refine ⟨9115552051560206086430317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12154069402080274781907089 9115552051560206086430317)
          ·
            refine ⟨3418332019335077282411369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9115552051560206086430317 3418332019335077282411369)
            ·
              refine ⟨2563749014501307961808527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418332019335077282411369 2563749014501307961808527)
              ·
                refine ⟨3845623521751961942712791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563749014501307961808527 3845623521751961942712791)
                ·
                  refine ⟨5768435282627942914069187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845623521751961942712791 5768435282627942914069187)
                  ·
                    refine ⟨8652652923941914371103781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768435282627942914069187 8652652923941914371103781)
                    ·
                      refine ⟨1622372423239108944581959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8652652923941914371103781 1622372423239108944581959)
                      ·
                        rfl

theorem cell23_3159559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_3159559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159559 prefixEnd_3159559 := by exact prefixLift 3159559
  have htrace : WordTrace (prefixWord ++ tailWord_3159559) baseStart_3159559 baseEnd_3159559 := by
    simpa [prefixWord, tailWord_3159559, baseEnd_3159559] using wordTrace_append hprefix tailTrace_3159559
  have hstable : (prefixWord ++ tailWord_3159559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159559).length < 2 ^ (prefixWord ++ tailWord_3159559).sum := by decide
  have hdescent : baseEnd_3159559 < baseStart_3159559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159562 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3]
def baseStart_3159562 : Nat := 118140960795 + 3159562 * 2 ^ 59
def prefixEnd_3159562 : Nat := 4983230072969 + 3 ^ 40 * 3159562 * 2
def baseEnd_3159562 : Nat := 1622373963681072432844445

theorem tailTrace_3159562 : CollatzResearch.WordTrace tailWord_3159562 prefixEnd_3159562 1622373963681072432844445 := by
  unfold tailWord_3159562
  simp only [CollatzResearch.WordTrace]
  refine ⟨28809673344863489768536235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76825795586302639382763293 28809673344863489768536235)
  ·
    refine ⟨43214510017295234652804353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28809673344863489768536235 43214510017295234652804353)
    ·
      refine ⟨32410882512971425989603265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43214510017295234652804353 32410882512971425989603265)
      ·
        refine ⟨24308161884728569492202449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32410882512971425989603265 24308161884728569492202449)
        ·
          refine ⟨18231121413546427119151837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24308161884728569492202449 18231121413546427119151837)
          ·
            refine ⟨6836670530079910169681939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18231121413546427119151837 6836670530079910169681939)
            ·
              refine ⟨10255005795119865254522909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6836670530079910169681939 10255005795119865254522909)
              ·
                refine ⟨3845627173169949470446091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10255005795119865254522909 3845627173169949470446091)
                ·
                  refine ⟨5768440759754924205669137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845627173169949470446091 5768440759754924205669137)
                  ·
                    refine ⟨4326330569816193154251853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5768440759754924205669137 4326330569816193154251853)
                    ·
                      refine ⟨1622373963681072432844445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4326330569816193154251853 1622373963681072432844445)
                      ·
                        rfl

theorem cell23_3159562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_3159562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159562 prefixEnd_3159562 := by exact prefixLift 3159562
  have htrace : WordTrace (prefixWord ++ tailWord_3159562) baseStart_3159562 baseEnd_3159562 := by
    simpa [prefixWord, tailWord_3159562, baseEnd_3159562] using wordTrace_append hprefix tailTrace_3159562
  have hstable : (prefixWord ++ tailWord_3159562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159562).length < 2 ^ (prefixWord ++ tailWord_3159562).sum := by decide
  have hdescent : baseEnd_3159562 < baseStart_3159562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159632 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 4, 2, 2]
def baseStart_3159632 : Nat := 118140960795 + 3159632 * 2 ^ 59
def prefixEnd_3159632 : Nat := 4983230072969 + 3 ^ 40 * 3159632 * 2
def baseEnd_3159632 : Nat := 1622409907326887158969123

theorem tailTrace_3159632 : CollatzResearch.WordTrace tailWord_3159632 prefixEnd_3159632 1622409907326887158969123 := by
  unfold tailWord_3159632
  simp only [CollatzResearch.WordTrace]
  refine ⟨57620623244600180514596575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76827497659466907352795433 57620623244600180514596575)
  ·
    refine ⟨86430934866900270771894863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57620623244600180514596575 86430934866900270771894863)
    ·
      refine ⟨129646402300350406157842295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86430934866900270771894863 129646402300350406157842295)
      ·
        refine ⟨194469603450525609236763443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129646402300350406157842295 194469603450525609236763443)
        ·
          refine ⟨291704405175788413855145165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194469603450525609236763443 291704405175788413855145165)
          ·
            refine ⟨109389151940920655195679437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291704405175788413855145165 109389151940920655195679437)
            ·
              refine ⟨41020931977845245698379789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109389151940920655195679437 41020931977845245698379789)
              ·
                refine ⟨15382849491691967136892421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41020931977845245698379789 15382849491691967136892421)
                ·
                  refine ⟨2884284279692243838167329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15382849491691967136892421 2884284279692243838167329)
                  ·
                    refine ⟨2163213209769182878625497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2884284279692243838167329 2163213209769182878625497)
                    ·
                      refine ⟨1622409907326887158969123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163213209769182878625497 1622409907326887158969123)
                      ·
                        rfl

theorem cell23_3159632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 4, 2, 2].length) (baseStart_3159632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159632 prefixEnd_3159632 := by exact prefixLift 3159632
  have htrace : WordTrace (prefixWord ++ tailWord_3159632) baseStart_3159632 baseEnd_3159632 := by
    simpa [prefixWord, tailWord_3159632, baseEnd_3159632] using wordTrace_append hprefix tailTrace_3159632
  have hstable : (prefixWord ++ tailWord_3159632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159632).length < 2 ^ (prefixWord ++ tailWord_3159632).sum := by decide
  have hdescent : baseEnd_3159632 < baseStart_3159632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159649 : List Nat := [1, 2, 3, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_3159649 : Nat := 118140960795 + 3159649 * 2 ^ 59
def prefixEnd_3159649 : Nat := 4983230072969 + 3 ^ 40 * 3159649 * 2
def baseEnd_3159649 : Nat := 1622418636498013592456545

theorem tailTrace_3159649 : CollatzResearch.WordTrace tailWord_3159649 prefixEnd_3159649 1622418636498013592456545 := by
  unfold tailWord_3159649
  simp only [CollatzResearch.WordTrace]
  refine ⟨115241866530138772932562001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76827911020092515288374667 115241866530138772932562001)
  ·
    refine ⟨86431399897604079699421501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115241866530138772932562001 86431399897604079699421501)
    ·
      refine ⟨32411774961601529887283063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86431399897604079699421501 32411774961601529887283063)
      ·
        refine ⟨48617662442402294830924595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32411774961601529887283063 48617662442402294830924595)
        ·
          refine ⟨72926493663603442246386893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48617662442402294830924595 72926493663603442246386893)
          ·
            refine ⟨27347435123851290842395085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72926493663603442246386893 27347435123851290842395085)
            ·
              refine ⟨10255288171444234065898157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27347435123851290842395085 10255288171444234065898157)
              ·
                refine ⟨3845733064291587774711809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10255288171444234065898157 3845733064291587774711809)
                ·
                  refine ⟨2884299798218690831033857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3845733064291587774711809 2884299798218690831033857)
                  ·
                    refine ⟨2163224848664018123275393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2884299798218690831033857 2163224848664018123275393)
                    ·
                      refine ⟨1622418636498013592456545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163224848664018123275393 1622418636498013592456545)
                      ·
                        rfl

theorem cell23_3159649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_3159649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159649 prefixEnd_3159649 := by exact prefixLift 3159649
  have htrace : WordTrace (prefixWord ++ tailWord_3159649) baseStart_3159649 baseEnd_3159649 := by
    simpa [prefixWord, tailWord_3159649, baseEnd_3159649] using wordTrace_append hprefix tailTrace_3159649
  have hstable : (prefixWord ++ tailWord_3159649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159649).length < 2 ^ (prefixWord ++ tailWord_3159649).sum := by decide
  have hdescent : baseEnd_3159649 < baseStart_3159649 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159685 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 2, 5]
def baseStart_3159685 : Nat := 118140960795 + 3159685 * 2 ^ 59
def prefixEnd_3159685 : Nat := 4983230072969 + 3 ^ 40 * 3159685 * 2
def baseEnd_3159685 : Nat := 540812373933858483868793

theorem tailTrace_3159685 : CollatzResearch.WordTrace tailWord_3159685 prefixEnd_3159685 540812373933858483868793 := by
  unfold tailWord_3159685
  simp only [CollatzResearch.WordTrace]
  refine ⟨115243179558008351080872509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76828786372005567387248339 115243179558008351080872509)
  ·
    refine ⟨43216192334253131655327191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115243179558008351080872509 43216192334253131655327191)
    ·
      refine ⟨64824288501379697482990787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43216192334253131655327191 64824288501379697482990787)
      ·
        refine ⟨97236432752069546224486181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64824288501379697482990787 97236432752069546224486181)
        ·
          refine ⟨18231831141013039917091159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97236432752069546224486181 18231831141013039917091159)
          ·
            refine ⟨27347746711519559875636739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18231831141013039917091159 27347746711519559875636739)
            ·
              refine ⟨41021620067279339813455109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27347746711519559875636739 41021620067279339813455109)
              ·
                refine ⟨7691553762614876215022833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41021620067279339813455109 7691553762614876215022833)
                ·
                  refine ⟨5768665321961157161267125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7691553762614876215022833 5768665321961157161267125)
                  ·
                    refine ⟨540812373933858483868793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5768665321961157161267125 540812373933858483868793)
                    ·
                      rfl

theorem cell23_3159685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 5].length) (baseStart_3159685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159685 prefixEnd_3159685 := by exact prefixLift 3159685
  have htrace : WordTrace (prefixWord ++ tailWord_3159685) baseStart_3159685 baseEnd_3159685 := by
    simpa [prefixWord, tailWord_3159685, baseEnd_3159685] using wordTrace_append hprefix tailTrace_3159685
  have hstable : (prefixWord ++ tailWord_3159685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159685).length < 2 ^ (prefixWord ++ tailWord_3159685).sum := by decide
  have hdescent : baseEnd_3159685 < baseStart_3159685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159735 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_3159735 : Nat := 118140960795 + 3159735 * 2 ^ 59
def prefixEnd_3159735 : Nat := 4983230072969 + 3 ^ 40 * 3159735 * 2
def baseEnd_3159735 : Nat := 1622462795834300255981149

theorem tailTrace_3159735 : CollatzResearch.WordTrace tailWord_3159735 prefixEnd_3159735 1622462795834300255981149 := by
  unfold tailWord_3159735
  simp only [CollatzResearch.WordTrace]
  refine ⟨115245003207827209620192659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76830002138551473080128439 115245003207827209620192659)
  ·
    refine ⟨172867504811740814430288989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115245003207827209620192659 172867504811740814430288989)
    ·
      refine ⟨64825314304402805411358371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172867504811740814430288989 64825314304402805411358371)
      ·
        refine ⟨97237971456604208117037557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64825314304402805411358371 97237971456604208117037557)
        ·
          refine ⟨9116059824056644510972271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97237971456604208117037557 9116059824056644510972271)
          ·
            refine ⟨13674089736084966766458407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9116059824056644510972271 13674089736084966766458407)
            ·
              refine ⟨20511134604127450149687611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13674089736084966766458407 20511134604127450149687611)
              ·
                refine ⟨30766701906191175224531417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20511134604127450149687611 30766701906191175224531417)
                ·
                  refine ⟨23075026429643381418398563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30766701906191175224531417 23075026429643381418398563)
                  ·
                    refine ⟨34612539644465072127597845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23075026429643381418398563 34612539644465072127597845)
                    ·
                      refine ⟨1622462795834300255981149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34612539644465072127597845 1622462795834300255981149)
                      ·
                        rfl

theorem cell23_3159735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_3159735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159735 prefixEnd_3159735 := by exact prefixLift 3159735
  have htrace : WordTrace (prefixWord ++ tailWord_3159735) baseStart_3159735 baseEnd_3159735 := by
    simpa [prefixWord, tailWord_3159735, baseEnd_3159735] using wordTrace_append hprefix tailTrace_3159735
  have hstable : (prefixWord ++ tailWord_3159735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159735).length < 2 ^ (prefixWord ++ tailWord_3159735).sum := by decide
  have hdescent : baseEnd_3159735 < baseStart_3159735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159805 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_3159805 : Nat := 118140960795 + 3159805 * 2 ^ 59
def prefixEnd_3159805 : Nat := 4983230072969 + 3 ^ 40 * 3159805 * 2
def baseEnd_3159805 : Nat := 540832913160038327368609

theorem tailTrace_3159805 : CollatzResearch.WordTrace tailWord_3159805 prefixEnd_3159805 540832913160038327368609 := by
  unfold tailWord_3159805
  simp only [CollatzResearch.WordTrace]
  refine ⟨115247556317573611575240869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76831704211715741050160579 115247556317573611575240869)
  ·
    refine ⟨21608916809545052170357663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115247556317573611575240869 21608916809545052170357663)
    ·
      refine ⟨32413375214317578255536495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21608916809545052170357663 32413375214317578255536495)
      ·
        refine ⟨48620062821476367383304743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32413375214317578255536495 48620062821476367383304743)
        ·
          refine ⟨72930094232214551074957115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48620062821476367383304743 72930094232214551074957115)
          ·
            refine ⟨109395141348321826612435673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72930094232214551074957115 109395141348321826612435673)
            ·
              refine ⟨82046356011241369959326755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109395141348321826612435673 82046356011241369959326755)
              ·
                refine ⟨123069534016862054938990133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82046356011241369959326755 123069534016862054938990133)
                ·
                  refine ⟨11537768814080817650530325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 123069534016862054938990133 11537768814080817650530325)
                  ·
                    refine ⟨540832913160038327368609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11537768814080817650530325 540832913160038327368609)
                    ·
                      rfl

theorem cell23_3159805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_3159805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159805 prefixEnd_3159805 := by exact prefixLift 3159805
  have htrace : WordTrace (prefixWord ++ tailWord_3159805) baseStart_3159805 baseEnd_3159805 := by
    simpa [prefixWord, tailWord_3159805, baseEnd_3159805] using wordTrace_append hprefix tailTrace_3159805
  have hstable : (prefixWord ++ tailWord_3159805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159805).length < 2 ^ (prefixWord ++ tailWord_3159805).sum := by decide
  have hdescent : baseEnd_3159805 < baseStart_3159805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159826 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_3159826 : Nat := 118140960795 + 3159826 * 2 ^ 59
def prefixEnd_3159826 : Nat := 4983230072969 + 3 ^ 40 * 3159826 * 2
def baseEnd_3159826 : Nat := 540836507524619799981077

theorem tailTrace_3159826 : CollatzResearch.WordTrace tailWord_3159826 prefixEnd_3159826 540836507524619799981077 := by
  unfold tailWord_3159826
  simp only [CollatzResearch.WordTrace]
  refine ⟨28812080562624383040438833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76832214833665021441170221 28812080562624383040438833)
  ·
    refine ⟨21609060421968287280329125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28812080562624383040438833 21609060421968287280329125)
    ·
      refine ⟨4051698829119053865061711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21609060421968287280329125 4051698829119053865061711)
      ·
        refine ⟨6077548243678580797592567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051698829119053865061711 6077548243678580797592567)
        ·
          refine ⟨9116322365517871196388851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6077548243678580797592567 9116322365517871196388851)
          ·
            refine ⟨13674483548276806794583277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9116322365517871196388851 13674483548276806794583277)
            ·
              refine ⟨5127931330603802547968729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13674483548276806794583277 5127931330603802547968729)
              ·
                refine ⟨3845948497952851910976547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5127931330603802547968729 3845948497952851910976547)
                ·
                  refine ⟨5768922746929277866464821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845948497952851910976547 5768922746929277866464821)
                  ·
                    refine ⟨540836507524619799981077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5768922746929277866464821 540836507524619799981077)
                    ·
                      rfl

theorem cell23_3159826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_3159826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159826 prefixEnd_3159826 := by exact prefixLift 3159826
  have htrace : WordTrace (prefixWord ++ tailWord_3159826) baseStart_3159826 baseEnd_3159826 := by
    simpa [prefixWord, tailWord_3159826, baseEnd_3159826] using wordTrace_append hprefix tailTrace_3159826
  have hstable : (prefixWord ++ tailWord_3159826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159826).length < 2 ^ (prefixWord ++ tailWord_3159826).sum := by decide
  have hdescent : baseEnd_3159826 < baseStart_3159826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159829 : List Nat := [1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 4]
def baseStart_3159829 : Nat := 118140960795 + 3159829 * 2 ^ 59
def prefixEnd_3159829 : Nat := 4983230072969 + 3 ^ 40 * 3159829 * 2
def baseEnd_3159829 : Nat := 1622511063015822888205717

theorem tailTrace_3159829 : CollatzResearch.WordTrace tailWord_3159829 prefixEnd_3159829 1622511063015822888205717 := by
  unfold tailWord_3159829
  simp only [CollatzResearch.WordTrace]
  refine ⟨115248431669486663674114541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76832287779657775782743027 115248431669486663674114541)
  ·
    refine ⟨43218161876057498877792953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115248431669486663674114541 43218161876057498877792953)
    ·
      refine ⟨32413621407043124158344715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43218161876057498877792953 32413621407043124158344715)
      ·
        refine ⟨48620432110564686237517073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32413621407043124158344715 48620432110564686237517073)
        ·
          refine ⟨36465324082923514678137805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48620432110564686237517073 36465324082923514678137805)
          ·
            refine ⟨13674496531096318004301677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36465324082923514678137805 13674496531096318004301677)
            ·
              refine ⟨5127936199161119251613129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13674496531096318004301677 5127936199161119251613129)
              ·
                refine ⟨3845952149370839438709847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5127936199161119251613129 3845952149370839438709847)
                ·
                  refine ⟨5768928224056259158064771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3845952149370839438709847 5768928224056259158064771)
                  ·
                    refine ⟨8653392336084388737097157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5768928224056259158064771 8653392336084388737097157)
                    ·
                      refine ⟨1622511063015822888205717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8653392336084388737097157 1622511063015822888205717)
                      ·
                        rfl

theorem cell23_3159829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_3159829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159829 prefixEnd_3159829 := by exact prefixLift 3159829
  have htrace : WordTrace (prefixWord ++ tailWord_3159829) baseStart_3159829 baseEnd_3159829 := by
    simpa [prefixWord, tailWord_3159829, baseEnd_3159829] using wordTrace_append hprefix tailTrace_3159829
  have hstable : (prefixWord ++ tailWord_3159829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159829).length < 2 ^ (prefixWord ++ tailWord_3159829).sum := by decide
  have hdescent : baseEnd_3159829 < baseStart_3159829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159869 : List Nat := [1, 4, 1, 4, 1, 3, 1, 8]
def baseStart_3159869 : Nat := 118140960795 + 3159869 * 2 ^ 59
def prefixEnd_3159869 : Nat := 4983230072969 + 3 ^ 40 * 3159869 * 2
def baseEnd_3159869 : Nat := 60093763046000101174279

theorem tailTrace_3159869 : CollatzResearch.WordTrace tailWord_3159869 prefixEnd_3159869 60093763046000101174279 := by
  unfold tailWord_3159869
  simp only [CollatzResearch.WordTrace]
  refine ⟨115249890589341750505570661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76833260392894500337047107 115249890589341750505570661)
  ·
    refine ⟨21609354485501578219794499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115249890589341750505570661 21609354485501578219794499)
    ·
      refine ⟨32414031728252367329691749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21609354485501578219794499 32414031728252367329691749)
      ·
        refine ⟨6077630949047318874317203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32414031728252367329691749 6077630949047318874317203)
        ·
          refine ⟨9116446423570978311475805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6077630949047318874317203 9116446423570978311475805)
          ·
            refine ⟨3418667408839116866803427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9116446423570978311475805 3418667408839116866803427)
            ·
              refine ⟨5128001113258675300205141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3418667408839116866803427 5128001113258675300205141)
              ·
                refine ⟨60093763046000101174279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5128001113258675300205141 60093763046000101174279)
                ·
                  rfl

theorem cell23_3159869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 8].length) (baseStart_3159869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159869 prefixEnd_3159869 := by exact prefixLift 3159869
  have htrace : WordTrace (prefixWord ++ tailWord_3159869) baseStart_3159869 baseEnd_3159869 := by
    simpa [prefixWord, tailWord_3159869, baseEnd_3159869] using wordTrace_append hprefix tailTrace_3159869
  have hstable : (prefixWord ++ tailWord_3159869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159869).length < 2 ^ (prefixWord ++ tailWord_3159869).sum := by decide
  have hdescent : baseEnd_3159869 < baseStart_3159869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159900 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_3159900 : Nat := 118140960795 + 3159900 * 2 ^ 59
def prefixEnd_3159900 : Nat := 4983230072969 + 3 ^ 40 * 3159900 * 2
def baseEnd_3159900 : Nat := 1622547520142292110417891

theorem tailTrace_3159900 : CollatzResearch.WordTrace tailWord_3159900 prefixEnd_3159900 1622547520142292110417891 := by
  unfold tailWord_3159900
  simp only [CollatzResearch.WordTrace]
  refine ⟨57625510626114721399974577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76834014168152961866632769 57625510626114721399974577)
  ·
    refine ⟨43219132969586041049980933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57625510626114721399974577 43219132969586041049980933)
    ·
      refine ⟨8103587431797382696871425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43219132969586041049980933 8103587431797382696871425)
      ·
        refine ⟨6077690573848037022653569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8103587431797382696871425 6077690573848037022653569)
        ·
          refine ⟨4558267930386027766990177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6077690573848037022653569 4558267930386027766990177)
          ·
            refine ⟨3418700947789520825242633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4558267930386027766990177 3418700947789520825242633)
            ·
              refine ⟨2564025710842140618931975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418700947789520825242633 2564025710842140618931975)
              ·
                refine ⟨3846038566263210928397963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564025710842140618931975 3846038566263210928397963)
                ·
                  refine ⟨5769057849394816392596945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846038566263210928397963 5769057849394816392596945)
                  ·
                    refine ⟨4326793387046112294447709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5769057849394816392596945 4326793387046112294447709)
                    ·
                      refine ⟨1622547520142292110417891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4326793387046112294447709 1622547520142292110417891)
                      ·
                        rfl

theorem cell23_3159900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_3159900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159900 prefixEnd_3159900 := by exact prefixLift 3159900
  have htrace : WordTrace (prefixWord ++ tailWord_3159900) baseStart_3159900 baseEnd_3159900 := by
    simpa [prefixWord, tailWord_3159900, baseEnd_3159900] using wordTrace_append hprefix tailTrace_3159900
  have hstable : (prefixWord ++ tailWord_3159900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159900).length < 2 ^ (prefixWord ++ tailWord_3159900).sum := by decide
  have hdescent : baseEnd_3159900 < baseStart_3159900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159912 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 4, 6]
def baseStart_3159912 : Nat := 118140960795 + 3159912 * 2 ^ 59
def prefixEnd_3159912 : Nat := 4983230072969 + 3 ^ 40 * 3159912 * 2
def baseEnd_3159912 : Nat := 540851227303382021155945

theorem tailTrace_3159912 : CollatzResearch.WordTrace tailWord_3159912 prefixEnd_3159912 540851227303382021155945 := by
  unfold tailWord_3159912
  simp only [CollatzResearch.WordTrace]
  refine ⟨57625729464092984424692995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76834305952123979232923993 57625729464092984424692995)
  ·
    refine ⟨86438594196139476637039493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57625729464092984424692995 86438594196139476637039493)
    ·
      refine ⟨16207236411776151869444905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86438594196139476637039493 16207236411776151869444905)
      ·
        refine ⟨12155427308832113902083679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16207236411776151869444905 12155427308832113902083679)
        ·
          refine ⟨18233140963248170853125519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12155427308832113902083679 18233140963248170853125519)
          ·
            refine ⟨27349711444872256279688279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18233140963248170853125519 27349711444872256279688279)
            ·
              refine ⟨41024567167308384419532419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27349711444872256279688279 41024567167308384419532419)
              ·
                refine ⟨61536850750962576629298629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41024567167308384419532419 61536850750962576629298629)
                ·
                  refine ⟨11538159515805483117993493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61536850750962576629298629 11538159515805483117993493)
                  ·
                    refine ⟨540851227303382021155945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11538159515805483117993493 540851227303382021155945)
                    ·
                      rfl

theorem cell23_3159912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_3159912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159912 prefixEnd_3159912 := by exact prefixLift 3159912
  have htrace : WordTrace (prefixWord ++ tailWord_3159912) baseStart_3159912 baseEnd_3159912 := by
    simpa [prefixWord, tailWord_3159912, baseEnd_3159912] using wordTrace_append hprefix tailTrace_3159912
  have hstable : (prefixWord ++ tailWord_3159912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159912).length < 2 ^ (prefixWord ++ tailWord_3159912).sum := by decide
  have hdescent : baseEnd_3159912 < baseStart_3159912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159922 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3159922 : Nat := 118140960795 + 3159922 * 2 ^ 59
def prefixEnd_3159922 : Nat := 4983230072969 + 3 ^ 40 * 3159922 * 2
def baseEnd_3159922 : Nat := 1622558816716691024342789

theorem tailTrace_3159922 : CollatzResearch.WordTrace tailWord_3159922 prefixEnd_3159922 1622558816716691024342789 := by
  unfold tailWord_3159922
  simp only [CollatzResearch.WordTrace]
  refine ⟨28812955914537435139312505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76834549105433160371500013 28812955914537435139312505)
  ·
    refine ⟨21609716935903076354484379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28812955914537435139312505 21609716935903076354484379)
    ·
      refine ⟨32414575403854614531726569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21609716935903076354484379 32414575403854614531726569)
      ·
        refine ⟨24310931552890960898794927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32414575403854614531726569 24310931552890960898794927)
        ·
          refine ⟨36466397329336441348192391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24310931552890960898794927 36466397329336441348192391)
          ·
            refine ⟨54699595994004662022288587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36466397329336441348192391 54699595994004662022288587)
            ·
              refine ⟨82049393991006993033432881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54699595994004662022288587 82049393991006993033432881)
              ·
                refine ⟨61537045493255244775074661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82049393991006993033432881 61537045493255244775074661)
                ·
                  refine ⟨11538196029985358395326499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61537045493255244775074661 11538196029985358395326499)
                  ·
                    refine ⟨17307294044978037592989749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11538196029985358395326499 17307294044978037592989749)
                    ·
                      refine ⟨1622558816716691024342789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17307294044978037592989749 1622558816716691024342789)
                      ·
                        rfl

theorem cell23_3159922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3159922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159922 prefixEnd_3159922 := by exact prefixLift 3159922
  have htrace : WordTrace (prefixWord ++ tailWord_3159922) baseStart_3159922 baseEnd_3159922 := by
    simpa [prefixWord, tailWord_3159922, baseEnd_3159922] using wordTrace_append hprefix tailTrace_3159922
  have hstable : (prefixWord ++ tailWord_3159922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159922).length < 2 ^ (prefixWord ++ tailWord_3159922).sum := by decide
  have hdescent : baseEnd_3159922 < baseStart_3159922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3159952 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3]
def baseStart_3159952 : Nat := 118140960795 + 3159952 * 2 ^ 59
def prefixEnd_3159952 : Nat := 4983230072969 + 3 ^ 40 * 3159952 * 2
def baseEnd_3159952 : Nat := 1622574221136325906967651

theorem tailTrace_3159952 : CollatzResearch.WordTrace tailWord_3159952 prefixEnd_3159952 1622574221136325906967651 := by
  unfold tailWord_3159952
  simp only [CollatzResearch.WordTrace]
  refine ⟨57626458924020527840421055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76835278565360703787228073 57626458924020527840421055)
  ·
    refine ⟨86439688386030791760631583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57626458924020527840421055 86439688386030791760631583)
    ·
      refine ⟨129659532579046187640947375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86439688386030791760631583 129659532579046187640947375)
      ·
        refine ⟨194489298868569281461421063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129659532579046187640947375 194489298868569281461421063)
        ·
          refine ⟨291733948302853922192131595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194489298868569281461421063 291733948302853922192131595)
          ·
            refine ⟨437600922454280883288197393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291733948302853922192131595 437600922454280883288197393)
            ·
              refine ⟨328200691840710662466148045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437600922454280883288197393 328200691840710662466148045)
              ·
                refine ⟨123075259440266498424805517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328200691840710662466148045 123075259440266498424805517)
                ·
                  refine ⟨46153222290099936909302069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123075259440266498424805517 46153222290099936909302069)
                  ·
                    refine ⟨4326864589696869085247069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46153222290099936909302069 4326864589696869085247069)
                    ·
                      refine ⟨1622574221136325906967651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4326864589696869085247069 1622574221136325906967651)
                      ·
                        rfl

theorem cell23_3159952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 3].length) (baseStart_3159952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3159952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3159952 prefixEnd_3159952 := by exact prefixLift 3159952
  have htrace : WordTrace (prefixWord ++ tailWord_3159952) baseStart_3159952 baseEnd_3159952 := by
    simpa [prefixWord, tailWord_3159952, baseEnd_3159952] using wordTrace_append hprefix tailTrace_3159952
  have hstable : (prefixWord ++ tailWord_3159952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3159952).length < 2 ^ (prefixWord ++ tailWord_3159952).sum := by decide
  have hdescent : baseEnd_3159952 < baseStart_3159952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3159952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160009 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 1, 6, 2]
def baseStart_3160009 : Nat := 118140960795 + 3160009 * 2 ^ 59
def prefixEnd_3160009 : Nat := 4983230072969 + 3 ^ 40 * 3160009 * 2
def baseEnd_3160009 : Nat := 1622603489533632183954889

theorem tailTrace_3160009 : CollatzResearch.WordTrace tailWord_3160009 prefixEnd_3160009 1622603489533632183954889 := by
  unfold tailWord_3160009
  simp only [CollatzResearch.WordTrace]
  refine ⟨115254996808834554415667081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76836664539223036277111387 115254996808834554415667081)
  ·
    refine ⟨86441247606625915811750311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115254996808834554415667081 86441247606625915811750311)
    ·
      refine ⟨129661871409938873717625467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86441247606625915811750311 129661871409938873717625467)
      ·
        refine ⟨194492807114908310576438201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129661871409938873717625467 194492807114908310576438201)
        ·
          refine ⟨145869605336181232932328651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194492807114908310576438201 145869605336181232932328651)
          ·
            refine ⟨218804408004271849398492977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145869605336181232932328651 218804408004271849398492977)
            ·
              refine ⟨164103306003203887048869733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218804408004271849398492977 164103306003203887048869733)
              ·
                refine ⟨30769369875600728821663075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 164103306003203887048869733 30769369875600728821663075)
                ·
                  refine ⟨46154054813401093232494613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30769369875600728821663075 46154054813401093232494613)
                  ·
                    refine ⟨2163471319378176245273185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46154054813401093232494613 2163471319378176245273185)
                    ·
                      refine ⟨1622603489533632183954889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163471319378176245273185 1622603489533632183954889)
                      ·
                        rfl

theorem cell23_3160009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 6, 2].length) (baseStart_3160009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160009 prefixEnd_3160009 := by exact prefixLift 3160009
  have htrace : WordTrace (prefixWord ++ tailWord_3160009) baseStart_3160009 baseEnd_3160009 := by
    simpa [prefixWord, tailWord_3160009, baseEnd_3160009] using wordTrace_append hprefix tailTrace_3160009
  have hstable : (prefixWord ++ tailWord_3160009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160009).length < 2 ^ (prefixWord ++ tailWord_3160009).sum := by decide
  have hdescent : baseEnd_3160009 < baseStart_3160009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160032 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 8]
def baseStart_3160032 : Nat := 118140960795 + 3160032 * 2 ^ 59
def prefixEnd_3160032 : Nat := 4983230072969 + 3 ^ 40 * 3160032 * 2
def baseEnd_3160032 : Nat := 180290588843187288218587

theorem tailTrace_3160032 : CollatzResearch.WordTrace tailWord_3160032 prefixEnd_3160032 180290588843187288218587 := by
  unfold tailWord_3160032
  simp only [CollatzResearch.WordTrace]
  refine ⟨57627917843875614671877175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76837223791834152895836233 57627917843875614671877175)
  ·
    refine ⟨86441876765813422007815763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57627917843875614671877175 86441876765813422007815763)
    ·
      refine ⟨129662815148720133011723645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86441876765813422007815763 129662815148720133011723645)
      ·
        refine ⟨48623555680770049879396367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129662815148720133011723645 48623555680770049879396367)
        ·
          refine ⟨72935333521155074819094551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48623555680770049879396367 72935333521155074819094551)
          ·
            refine ⟨109403000281732612228641827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72935333521155074819094551 109403000281732612228641827)
            ·
              refine ⟨164104500422598918342962741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109403000281732612228641827 164104500422598918342962741)
              ·
                refine ⟨15384796914618648594652757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164104500422598918342962741 15384796914618648594652757)
                ·
                  refine ⟨180290588843187288218587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15384796914618648594652757 180290588843187288218587)
                  ·
                    rfl

theorem cell23_3160032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 8].length) (baseStart_3160032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160032 prefixEnd_3160032 := by exact prefixLift 3160032
  have htrace : WordTrace (prefixWord ++ tailWord_3160032) baseStart_3160032 baseEnd_3160032 := by
    simpa [prefixWord, tailWord_3160032, baseEnd_3160032] using wordTrace_append hprefix tailTrace_3160032
  have hstable : (prefixWord ++ tailWord_3160032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160032).length < 2 ^ (prefixWord ++ tailWord_3160032).sum := by decide
  have hdescent : baseEnd_3160032 < baseStart_3160032 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160076 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_3160076 : Nat := 118140960795 + 3160076 * 2 ^ 59
def prefixEnd_3160076 : Nat := 4983230072969 + 3 ^ 40 * 3160076 * 2
def baseEnd_3160076 : Nat := 1622637892737483421817081

theorem tailTrace_3160076 : CollatzResearch.WordTrace tailWord_3160076 prefixEnd_3160076 1622637892737483421817081 := by
  unfold tailWord_3160076
  simp only [CollatzResearch.WordTrace]
  refine ⟨57628720249795912429178041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76838293666394549905570721 57628720249795912429178041)
  ·
    refine ⟨43221540187346934321883531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57628720249795912429178041 43221540187346934321883531)
    ·
      refine ⟨64832310281020401482825297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43221540187346934321883531 64832310281020401482825297)
      ·
        refine ⟨48624232710765301112118973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64832310281020401482825297 48624232710765301112118973)
        ·
          refine ⟨18234087266536987917044615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48624232710765301112118973 18234087266536987917044615)
          ·
            refine ⟨27351130899805481875566923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234087266536987917044615 27351130899805481875566923)
            ·
              refine ⟨41026696349708222813350385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27351130899805481875566923 41026696349708222813350385)
              ·
                refine ⟨30770022262281167110012789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41026696349708222813350385 30770022262281167110012789)
                ·
                  refine ⟨2884689587088859416563699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30770022262281167110012789 2884689587088859416563699)
                  ·
                    refine ⟨4327034380633289124845549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2884689587088859416563699 4327034380633289124845549)
                    ·
                      refine ⟨1622637892737483421817081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327034380633289124845549 1622637892737483421817081)
                      ·
                        rfl

theorem cell23_3160076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_3160076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160076 prefixEnd_3160076 := by exact prefixLift 3160076
  have htrace : WordTrace (prefixWord ++ tailWord_3160076) baseStart_3160076 baseEnd_3160076 := by
    simpa [prefixWord, tailWord_3160076, baseEnd_3160076] using wordTrace_append hprefix tailTrace_3160076
  have hstable : (prefixWord ++ tailWord_3160076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160076).length < 2 ^ (prefixWord ++ tailWord_3160076).sum := by decide
  have hdescent : baseEnd_3160076 < baseStart_3160076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160093 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_3160093 : Nat := 118140960795 + 3160093 * 2 ^ 59
def prefixEnd_3160093 : Nat := 4983230072969 + 3 ^ 40 * 3160093 * 2
def baseEnd_3160093 : Nat := 1622646621908609855304503

theorem tailTrace_3160093 : CollatzResearch.WordTrace tailWord_3160093 prefixEnd_3160093 1622646621908609855304503 := by
  unfold tailWord_3160093
  simp only [CollatzResearch.WordTrace]
  refine ⟨115258060540530236761724933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76838707027020157841149955 115258060540530236761724933)
  ·
    refine ⟨21610886351349419392823425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115258060540530236761724933 21610886351349419392823425)
    ·
      refine ⟨16208164763512064544617569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21610886351349419392823425 16208164763512064544617569)
      ·
        refine ⟨12156123572634048408463177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16208164763512064544617569 12156123572634048408463177)
        ·
          refine ⟨9117092679475536306347383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12156123572634048408463177 9117092679475536306347383)
          ·
            refine ⟨13675639019213304459521075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117092679475536306347383 13675639019213304459521075)
            ·
              refine ⟨20513458528819956689281613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13675639019213304459521075 20513458528819956689281613)
              ·
                refine ⟨7692546948307483758480605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20513458528819956689281613 7692546948307483758480605)
                ·
                  refine ⟨2884705105615306409430227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7692546948307483758480605 2884705105615306409430227)
                  ·
                    refine ⟨4327057658422959614145341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2884705105615306409430227 4327057658422959614145341)
                    ·
                      refine ⟨1622646621908609855304503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327057658422959614145341 1622646621908609855304503)
                      ·
                        rfl

theorem cell23_3160093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_3160093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160093 prefixEnd_3160093 := by exact prefixLift 3160093
  have htrace : WordTrace (prefixWord ++ tailWord_3160093) baseStart_3160093 baseEnd_3160093 := by
    simpa [prefixWord, tailWord_3160093, baseEnd_3160093] using wordTrace_append hprefix tailTrace_3160093
  have hstable : (prefixWord ++ tailWord_3160093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160093).length < 2 ^ (prefixWord ++ tailWord_3160093).sum := by decide
  have hdescent : baseEnd_3160093 < baseStart_3160093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160156 : List Nat := [2, 2, 4, 1, 1, 3, 2, 8]
def baseStart_3160156 : Nat := 118140960795 + 3160156 * 2 ^ 59
def prefixEnd_3160156 : Nat := 4983230072969 + 3 ^ 40 * 3160156 * 2
def baseEnd_3160156 : Nat := 60099221155179374400619

theorem tailTrace_3160156 : CollatzResearch.WordTrace tailWord_3160156 prefixEnd_3160156 60099221155179374400619 := by
  unfold tailWord_3160156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57630179169650999260634161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76840238892867999014178881 57630179169650999260634161)
  ·
    refine ⟨43222634377238249445475621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57630179169650999260634161 43222634377238249445475621)
    ·
      refine ⟨8104243945732171771026679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43222634377238249445475621 8104243945732171771026679)
      ·
        refine ⟨12156365918598257656540019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8104243945732171771026679 12156365918598257656540019)
        ·
          refine ⟨18234548877897386484810029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156365918598257656540019 18234548877897386484810029)
          ·
            refine ⟨6837955829211519931803761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18234548877897386484810029 6837955829211519931803761)
            ·
              refine ⟨5128466871908639948852821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6837955829211519931803761 5128466871908639948852821)
              ·
                refine ⟨60099221155179374400619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5128466871908639948852821 60099221155179374400619)
                ·
                  rfl

theorem cell23_3160156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 8].length) (baseStart_3160156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160156 prefixEnd_3160156 := by exact prefixLift 3160156
  have htrace : WordTrace (prefixWord ++ tailWord_3160156) baseStart_3160156 baseEnd_3160156 := by
    simpa [prefixWord, tailWord_3160156, baseEnd_3160156] using wordTrace_append hprefix tailTrace_3160156
  have hstable : (prefixWord ++ tailWord_3160156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160156).length < 2 ^ (prefixWord ++ tailWord_3160156).sum := by decide
  have hdescent : baseEnd_3160156 < baseStart_3160156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160160 : List Nat := [2, 1, 1, 3, 2, 5, 2, 1, 2, 4]
def baseStart_3160160 : Nat := 118140960795 + 3160160 * 2 ^ 59
def prefixEnd_3160160 : Nat := 4983230072969 + 3 ^ 40 * 3160160 * 2
def baseEnd_3160160 : Nat := 540893675037487031055565

theorem tailTrace_3160160 : CollatzResearch.WordTrace tailWord_3160160 prefixEnd_3160160 540893675037487031055565 := by
  unfold tailWord_3160160
  simp only [CollatzResearch.WordTrace]
  refine ⟨57630252115643753602206967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76840336154191671469609289 57630252115643753602206967)
  ·
    refine ⟨86445378173465630403310451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57630252115643753602206967 86445378173465630403310451)
    ·
      refine ⟨129668067260198445604965677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86445378173465630403310451 129668067260198445604965677)
      ·
        refine ⟨48625525222574417101862129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129668067260198445604965677 48625525222574417101862129)
        ·
          refine ⟨36469143916930812826396597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48625525222574417101862129 36469143916930812826396597)
          ·
            refine ⟨3418982242212263702474681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36469143916930812826396597 3418982242212263702474681)
            ·
              refine ⟨2564236681659197776856011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3418982242212263702474681 2564236681659197776856011)
              ·
                refine ⟨3846355022488796665284017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564236681659197776856011 3846355022488796665284017)
                ·
                  refine ⟨2884766266866597498963013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3846355022488796665284017 2884766266866597498963013)
                  ·
                    refine ⟨540893675037487031055565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2884766266866597498963013 540893675037487031055565)
                    ·
                      rfl

theorem cell23_3160160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 1, 2, 4].length) (baseStart_3160160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160160 prefixEnd_3160160 := by exact prefixLift 3160160
  have htrace : WordTrace (prefixWord ++ tailWord_3160160) baseStart_3160160 baseEnd_3160160 := by
    simpa [prefixWord, tailWord_3160160, baseEnd_3160160] using wordTrace_append hprefix tailTrace_3160160
  have hstable : (prefixWord ++ tailWord_3160160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160160).length < 2 ^ (prefixWord ++ tailWord_3160160).sum := by decide
  have hdescent : baseEnd_3160160 < baseStart_3160160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160200 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3160200 : Nat := 118140960795 + 3160200 * 2 ^ 59
def prefixEnd_3160200 : Nat := 4983230072969 + 3 ^ 40 * 3160200 * 2
def baseEnd_3160200 : Nat := 1622701564338640936666511

theorem tailTrace_3160200 : CollatzResearch.WordTrace tailWord_3160200 prefixEnd_3160200 1622701564338640936666511 := by
  unfold tailWord_3160200
  simp only [CollatzResearch.WordTrace]
  refine ⟨57630981575571297017935027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76841308767428396023913369 57630981575571297017935027)
  ·
    refine ⟨86446472363356945526902541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57630981575571297017935027 86446472363356945526902541)
    ·
      refine ⟨32417427136258854572588453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86446472363356945526902541 32417427136258854572588453)
      ·
        refine ⟨6078267588048535232360335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32417427136258854572588453 6078267588048535232360335)
        ·
          refine ⟨9117401382072802848540503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078267588048535232360335 9117401382072802848540503)
          ·
            refine ⟨13676102073109204272810755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9117401382072802848540503 13676102073109204272810755)
            ·
              refine ⟨20514153109663806409216133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13676102073109204272810755 20514153109663806409216133)
              ·
                refine ⟨3846403708061963701728025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20514153109663806409216133 3846403708061963701728025)
                ·
                  refine ⟨2884802781046472776296019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3846403708061963701728025 2884802781046472776296019)
                  ·
                    refine ⟨4327204171569709164444029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2884802781046472776296019 4327204171569709164444029)
                    ·
                      refine ⟨1622701564338640936666511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327204171569709164444029 1622701564338640936666511)
                      ·
                        rfl

theorem cell23_3160200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3160200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160200 prefixEnd_3160200 := by exact prefixLift 3160200
  have htrace : WordTrace (prefixWord ++ tailWord_3160200) baseStart_3160200 baseEnd_3160200 := by
    simpa [prefixWord, tailWord_3160200, baseEnd_3160200] using wordTrace_append hprefix tailTrace_3160200
  have hstable : (prefixWord ++ tailWord_3160200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160200).length < 2 ^ (prefixWord ++ tailWord_3160200).sum := by decide
  have hdescent : baseEnd_3160200 < baseStart_3160200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160239 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_3160239 : Nat := 118140960795 + 3160239 * 2 ^ 59
def prefixEnd_3160239 : Nat := 4983230072969 + 3 ^ 40 * 3160239 * 2
def baseEnd_3160239 : Nat := 1622721590084166284078831

theorem tailTrace_3160239 : CollatzResearch.WordTrace tailWord_3160239 prefixEnd_3160239 1622721590084166284078831 := by
  unfold tailWord_3160239
  simp only [CollatzResearch.WordTrace]
  refine ⟨115263385598001303696539771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76842257065334202464359847 115263385598001303696539771)
  ·
    refine ⟨172895078397001955544809657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115263385598001303696539771 172895078397001955544809657)
    ·
      refine ⟨129671308797751466658607243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172895078397001955544809657 129671308797751466658607243)
      ·
        refine ⟨194506963196627199987910865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129671308797751466658607243 194506963196627199987910865)
        ·
          refine ⟨145880222397470399990933149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194506963196627199987910865 145880222397470399990933149)
          ·
            refine ⟨54705083399051399996599931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145880222397470399990933149 54705083399051399996599931)
            ·
              refine ⟨82057625098577099994899897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54705083399051399996599931 82057625098577099994899897)
              ·
                refine ⟨61543218823932824996174923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82057625098577099994899897 61543218823932824996174923)
                ·
                  refine ⟨92314828235899237494262385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61543218823932824996174923 92314828235899237494262385)
                  ·
                    refine ⟨69236121176924428120696789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92314828235899237494262385 69236121176924428120696789)
                    ·
                      refine ⟨1622721590084166284078831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69236121176924428120696789 1622721590084166284078831)
                      ·
                        rfl

theorem cell23_3160239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_3160239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160239 prefixEnd_3160239 := by exact prefixLift 3160239
  have htrace : WordTrace (prefixWord ++ tailWord_3160239) baseStart_3160239 baseEnd_3160239 := by
    simpa [prefixWord, tailWord_3160239, baseEnd_3160239] using wordTrace_append hprefix tailTrace_3160239
  have hstable : (prefixWord ++ tailWord_3160239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160239).length < 2 ^ (prefixWord ++ tailWord_3160239).sum := by decide
  have hdescent : baseEnd_3160239 < baseStart_3160239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160274 : List Nat := [3, 2, 2, 2, 1, 3, 3, 1, 2, 2, 2]
def baseStart_3160274 : Nat := 118140960795 + 3160274 * 2 ^ 59
def prefixEnd_3160274 : Nat := 4983230072969 + 3 ^ 40 * 3160274 * 2
def baseEnd_3160274 : Nat := 1622739561907073647141171

theorem tailTrace_3160274 : CollatzResearch.WordTrace tailWord_3160274 prefixEnd_3160274 1622739561907073647141171 := by
  unfold tailWord_3160274
  simp only [CollatzResearch.WordTrace]
  refine ⟨28816165538218626168515969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76843108101916336449375917 28816165538218626168515969)
  ·
    refine ⟨21612124153663969626386977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28816165538218626168515969 21612124153663969626386977)
    ·
      refine ⟨16209093115247977219790233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21612124153663969626386977 16209093115247977219790233)
      ·
        refine ⟨12156819836435982914842675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16209093115247977219790233 12156819836435982914842675)
        ·
          refine ⟨18235229754653974372264013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156819836435982914842675 18235229754653974372264013)
          ·
            refine ⟨6838211157995240389599005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18235229754653974372264013 6838211157995240389599005)
            ·
              refine ⟨2564329184248215146099627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6838211157995240389599005 2564329184248215146099627)
              ·
                refine ⟨3846493776372322719149441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564329184248215146099627 3846493776372322719149441)
                ·
                  refine ⟨2884870332279242039362081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3846493776372322719149441 2884870332279242039362081)
                  ·
                    refine ⟨2163652749209431529521561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2884870332279242039362081 2163652749209431529521561)
                    ·
                      refine ⟨1622739561907073647141171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163652749209431529521561 1622739561907073647141171)
                      ·
                        rfl

theorem cell23_3160274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_3160274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160274 prefixEnd_3160274 := by exact prefixLift 3160274
  have htrace : WordTrace (prefixWord ++ tailWord_3160274) baseStart_3160274 baseEnd_3160274 := by
    simpa [prefixWord, tailWord_3160274, baseEnd_3160274] using wordTrace_append hprefix tailTrace_3160274
  have hstable : (prefixWord ++ tailWord_3160274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160274).length < 2 ^ (prefixWord ++ tailWord_3160274).sum := by decide
  have hdescent : baseEnd_3160274 < baseStart_3160274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160313 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 2, 4, 2]
def baseStart_3160313 : Nat := 118140960795 + 3160313 * 2 ^ 59
def prefixEnd_3160313 : Nat := 4983230072969 + 3 ^ 40 * 3160313 * 2
def baseEnd_3160313 : Nat := 1622759587652598994553491

theorem tailTrace_3160313 : CollatzResearch.WordTrace tailWord_3160313 prefixEnd_3160313 1622759587652598994553491 := by
  unfold tailWord_3160313
  simp only [CollatzResearch.WordTrace]
  refine ⟨115266084599733214334733593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76844056399822142889822395 115266084599733214334733593)
  ·
    refine ⟨86449563449799910751050195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115266084599733214334733593 86449563449799910751050195)
    ·
      refine ⟨129674345174699866126575293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86449563449799910751050195 129674345174699866126575293)
      ·
        refine ⟨48627879440512449797465735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129674345174699866126575293 48627879440512449797465735)
        ·
          refine ⟨72941819160768674696198603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48627879440512449797465735 72941819160768674696198603)
          ·
            refine ⟨109412728741153012044297905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72941819160768674696198603 109412728741153012044297905)
            ·
              refine ⟨82059546555864759033223429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109412728741153012044297905 82059546555864759033223429)
              ·
                refine ⟨15386164979224642318729393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82059546555864759033223429 15386164979224642318729393)
                ·
                  refine ⟨11539623734418481739047045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15386164979224642318729393 11539623734418481739047045)
                  ·
                    refine ⟨2163679450203465326071321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11539623734418481739047045 2163679450203465326071321)
                    ·
                      refine ⟨1622759587652598994553491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163679450203465326071321 1622759587652598994553491)
                      ·
                        rfl

theorem cell23_3160313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_3160313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160313 prefixEnd_3160313 := by exact prefixLift 3160313
  have htrace : WordTrace (prefixWord ++ tailWord_3160313) baseStart_3160313 baseEnd_3160313 := by
    simpa [prefixWord, tailWord_3160313, baseEnd_3160313] using wordTrace_append hprefix tailTrace_3160313
  have hstable : (prefixWord ++ tailWord_3160313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160313).length < 2 ^ (prefixWord ++ tailWord_3160313).sum := by decide
  have hdescent : baseEnd_3160313 < baseStart_3160313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160370 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 6]
def baseStart_3160370 : Nat := 118140960795 + 3160370 * 2 ^ 59
def prefixEnd_3160370 : Nat := 4983230072969 + 3 ^ 40 * 3160370 * 2
def baseEnd_3160370 : Nat := 180309872894433919060081

theorem tailTrace_3160370 : CollatzResearch.WordTrace tailWord_3160370 prefixEnd_3160370 180309872894433919060081 := by
  unfold tailWord_3160370
  simp only [CollatzResearch.WordTrace]
  refine ⟨28817040890131678267389641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76845442373684475379705709 28817040890131678267389641)
  ·
    refine ⟨21612780667598758700542231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28817040890131678267389641 21612780667598758700542231)
    ·
      refine ⟨32419171001398138050813347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21612780667598758700542231 32419171001398138050813347)
      ·
        refine ⟨48628756502097207076220021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32419171001398138050813347 48628756502097207076220021)
        ·
          refine ⟨4558945922071613163395627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48628756502097207076220021 4558945922071613163395627)
          ·
            refine ⟨6838418883107419745093441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558945922071613163395627 6838418883107419745093441)
            ·
              refine ⟨5128814162330564808820081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6838418883107419745093441 5128814162330564808820081)
              ·
                refine ⟨3846610621747923606615061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5128814162330564808820081 3846610621747923606615061)
                ·
                  refine ⟨180309872894433919060081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3846610621747923606615061 180309872894433919060081)
                  ·
                    rfl

theorem cell23_3160370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_3160370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160370 prefixEnd_3160370 := by exact prefixLift 3160370
  have htrace : WordTrace (prefixWord ++ tailWord_3160370) baseStart_3160370 baseEnd_3160370 := by
    simpa [prefixWord, tailWord_3160370, baseEnd_3160370] using wordTrace_append hprefix tailTrace_3160370
  have hstable : (prefixWord ++ tailWord_3160370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160370).length < 2 ^ (prefixWord ++ tailWord_3160370).sum := by decide
  have hdescent : baseEnd_3160370 < baseStart_3160370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160380 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_3160380 : Nat := 118140960795 + 3160380 * 2 ^ 59
def prefixEnd_3160380 : Nat := 4983230072969 + 3 ^ 40 * 3160380 * 2
def baseEnd_3160380 : Nat := 1622793990856450232415683

theorem tailTrace_3160380 : CollatzResearch.WordTrace tailWord_3160380 prefixEnd_3160380 1622793990856450232415683 := by
  unfold tailWord_3160380
  simp only [CollatzResearch.WordTrace]
  refine ⟨57634264145245242388711297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76845685526993656518281729 57634264145245242388711297)
  ·
    refine ⟨43225698108933931791533473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57634264145245242388711297 43225698108933931791533473)
    ·
      refine ⟨32419273581700448843650105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43225698108933931791533473 32419273581700448843650105)
      ·
        refine ⟨24314455186275336632737579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32419273581700448843650105 24314455186275336632737579)
        ·
          refine ⟨36471682779413004949106369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24314455186275336632737579 36471682779413004949106369)
          ·
            refine ⟨27353762084559753711829777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36471682779413004949106369 27353762084559753711829777)
            ·
              refine ⟨20515321563419815283872333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27353762084559753711829777 20515321563419815283872333)
              ·
                refine ⟨7693245586282430731452125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20515321563419815283872333 7693245586282430731452125)
                ·
                  refine ⟨2884967094855911524294547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7693245586282430731452125 2884967094855911524294547)
                  ·
                    refine ⟨4327450642283867286441821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2884967094855911524294547 4327450642283867286441821)
                    ·
                      refine ⟨1622793990856450232415683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327450642283867286441821 1622793990856450232415683)
                      ·
                        rfl

theorem cell23_3160380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_3160380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160380 prefixEnd_3160380 := by exact prefixLift 3160380
  have htrace : WordTrace (prefixWord ++ tailWord_3160380) baseStart_3160380 baseEnd_3160380 := by
    simpa [prefixWord, tailWord_3160380, baseEnd_3160380] using wordTrace_append hprefix tailTrace_3160380
  have hstable : (prefixWord ++ tailWord_3160380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160380).length < 2 ^ (prefixWord ++ tailWord_3160380).sum := by decide
  have hdescent : baseEnd_3160380 < baseStart_3160380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160403 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 1, 8, 2]
def baseStart_3160403 : Nat := 118140960795 + 3160403 * 2 ^ 59
def prefixEnd_3160403 : Nat := 4983230072969 + 3 ^ 40 * 3160403 * 2
def baseEnd_3160403 : Nat := 1622805800911503642428077

theorem tailTrace_3160403 : CollatzResearch.WordTrace tailWord_3160403 prefixEnd_3160403 1622805800911503642428077 := by
  unfold tailWord_3160403
  simp only [CollatzResearch.WordTrace]
  refine ⟨115269367169407159705509863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76846244779604773137006575 115269367169407159705509863)
  ·
    refine ⟨172904050754110739558264795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115269367169407159705509863 172904050754110739558264795)
    ·
      refine ⟨259356076131166109337397193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172904050754110739558264795 259356076131166109337397193)
      ·
        refine ⟨194517057098374582003047895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259356076131166109337397193 194517057098374582003047895)
        ·
          refine ⟨291775585647561873004571843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194517057098374582003047895 291775585647561873004571843)
          ·
            refine ⟨437663378471342809506857765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291775585647561873004571843 437663378471342809506857765)
            ·
              refine ⟨82061883463376776782535831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 437663378471342809506857765 82061883463376776782535831)
              ·
                refine ⟨123092825195065165173803747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82061883463376776782535831 123092825195065165173803747)
                ·
                  refine ⟨184639237792597747760705621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123092825195065165173803747 184639237792597747760705621)
                  ·
                    refine ⟨2163741067882004856570769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 184639237792597747760705621 2163741067882004856570769)
                    ·
                      refine ⟨1622805800911503642428077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163741067882004856570769 1622805800911503642428077)
                      ·
                        rfl

theorem cell23_3160403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 1, 8, 2].length) (baseStart_3160403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160403 prefixEnd_3160403 := by exact prefixLift 3160403
  have htrace : WordTrace (prefixWord ++ tailWord_3160403) baseStart_3160403 baseEnd_3160403 := by
    simpa [prefixWord, tailWord_3160403, baseEnd_3160403] using wordTrace_append hprefix tailTrace_3160403
  have hstable : (prefixWord ++ tailWord_3160403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160403).length < 2 ^ (prefixWord ++ tailWord_3160403).sum := by decide
  have hdescent : baseEnd_3160403 < baseStart_3160403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160420 : List Nat := [2, 3, 1, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_3160420 : Nat := 118140960795 + 3160420 * 2 ^ 59
def prefixEnd_3160420 : Nat := 4983230072969 + 3 ^ 40 * 3160420 * 2
def baseEnd_3160420 : Nat := 1622814530082630075915499

theorem tailTrace_3160420 : CollatzResearch.WordTrace tailWord_3160420 prefixEnd_3160420 1622814530082630075915499 := by
  unfold tailWord_3160420
  simp only [CollatzResearch.WordTrace]
  refine ⟨57634993605172785804439357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76846658140230381072585809 57634993605172785804439357)
  ·
    refine ⟨21613122601939794676664759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57634993605172785804439357 21613122601939794676664759)
    ·
      refine ⟨32419683902909692014997139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21613122601939794676664759 32419683902909692014997139)
      ·
        refine ⟨48629525854364538022495709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32419683902909692014997139 48629525854364538022495709)
        ·
          refine ⟨18236072195386701758435891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48629525854364538022495709 18236072195386701758435891)
          ·
            refine ⟨27354108293080052637653837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18236072195386701758435891 27354108293080052637653837)
            ·
              refine ⟨10257790609905019739120189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27354108293080052637653837 10257790609905019739120189)
              ·
                refine ⟨3846671478714382402170071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10257790609905019739120189 3846671478714382402170071)
                ·
                  refine ⟨5770007218071573603255107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846671478714382402170071 5770007218071573603255107)
                  ·
                    refine ⟨8655010827107360404882661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770007218071573603255107 8655010827107360404882661)
                    ·
                      refine ⟨1622814530082630075915499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8655010827107360404882661 1622814530082630075915499)
                      ·
                        rfl

theorem cell23_3160420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_3160420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160420 prefixEnd_3160420 := by exact prefixLift 3160420
  have htrace : WordTrace (prefixWord ++ tailWord_3160420) baseStart_3160420 baseEnd_3160420 := by
    simpa [prefixWord, tailWord_3160420, baseEnd_3160420] using wordTrace_append hprefix tailTrace_3160420
  have hstable : (prefixWord ++ tailWord_3160420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160420).length < 2 ^ (prefixWord ++ tailWord_3160420).sum := by decide
  have hdescent : baseEnd_3160420 < baseStart_3160420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160457 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 3]
def baseStart_3160457 : Nat := 118140960795 + 3160457 * 2 ^ 59
def prefixEnd_3160457 : Nat := 4983230072969 + 3 ^ 40 * 3160457 * 2
def baseEnd_3160457 : Nat := 1622833528866846431152829

theorem tailTrace_3160457 : CollatzResearch.WordTrace tailWord_3160457 prefixEnd_3160457 1622833528866846431152829 := by
  unfold tailWord_3160457
  simp only [CollatzResearch.WordTrace]
  refine ⟨115271336711211526927975625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76847557807474351285317083 115271336711211526927975625)
  ·
    refine ⟨86453502533408645195981719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115271336711211526927975625 86453502533408645195981719)
    ·
      refine ⟨129680253800112967793972579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86453502533408645195981719 129680253800112967793972579)
      ·
        refine ⟨194520380700169451690958869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129680253800112967793972579 194520380700169451690958869)
        ·
          refine ⟨9118142845320443048013697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194520380700169451690958869 9118142845320443048013697)
          ·
            refine ⟨6838607133990332286010273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9118142845320443048013697 6838607133990332286010273)
            ·
              refine ⟨5128955350492749214507705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6838607133990332286010273 5128955350492749214507705)
              ·
                refine ⟨3846716512869561910880779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5128955350492749214507705 3846716512869561910880779)
                ·
                  refine ⟨5770074769304342866321169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846716512869561910880779 5770074769304342866321169)
                  ·
                    refine ⟨4327556076978257149740877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5770074769304342866321169 4327556076978257149740877)
                    ·
                      refine ⟨1622833528866846431152829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327556076978257149740877 1622833528866846431152829)
                      ·
                        rfl

theorem cell23_3160457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 3].length) (baseStart_3160457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160457 prefixEnd_3160457 := by exact prefixLift 3160457
  have htrace : WordTrace (prefixWord ++ tailWord_3160457) baseStart_3160457 baseEnd_3160457 := by
    simpa [prefixWord, tailWord_3160457, baseEnd_3160457] using wordTrace_append hprefix tailTrace_3160457
  have hstable : (prefixWord ++ tailWord_3160457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160457).length < 2 ^ (prefixWord ++ tailWord_3160457).sum := by decide
  have hdescent : baseEnd_3160457 < baseStart_3160457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160460 : List Nat := [2, 2, 1, 2, 1, 6, 2, 7]
def baseStart_3160460 : Nat := 118140960795 + 3160460 * 2 ^ 59
def prefixEnd_3160460 : Nat := 4983230072969 + 3 ^ 40 * 3160460 * 2
def baseEnd_3160460 : Nat := 60105002566992959978345

theorem tailTrace_3160460 : CollatzResearch.WordTrace tailWord_3160460 prefixEnd_3160460 60105002566992959978345 := by
  unfold tailWord_3160460
  simp only [CollatzResearch.WordTrace]
  refine ⟨57635723065100329220167417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76847630753467105626889889 57635723065100329220167417)
  ·
    refine ⟨43226792298825246915125563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57635723065100329220167417 43226792298825246915125563)
    ·
      refine ⟨64840188448237870372688345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43226792298825246915125563 64840188448237870372688345)
      ·
        refine ⟨48630141336178402779516259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64840188448237870372688345 48630141336178402779516259)
        ·
          refine ⟨72945212004267604169274389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48630141336178402779516259 72945212004267604169274389)
          ·
            refine ⟨3419306812700043945434737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72945212004267604169274389 3419306812700043945434737)
            ·
              refine ⟨2564480109525032959076053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3419306812700043945434737 2564480109525032959076053)
              ·
                refine ⟨60105002566992959978345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2564480109525032959076053 60105002566992959978345)
                ·
                  rfl

theorem cell23_3160460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 7].length) (baseStart_3160460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160460 prefixEnd_3160460 := by exact prefixLift 3160460
  have htrace : WordTrace (prefixWord ++ tailWord_3160460) baseStart_3160460 baseEnd_3160460 := by
    simpa [prefixWord, tailWord_3160460, baseEnd_3160460] using wordTrace_append hprefix tailTrace_3160460
  have hstable : (prefixWord ++ tailWord_3160460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160460).length < 2 ^ (prefixWord ++ tailWord_3160460).sum := by decide
  have hdescent : baseEnd_3160460 < baseStart_3160460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160487 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_3160487 : Nat := 118140960795 + 3160487 * 2 ^ 59
def prefixEnd_3160487 : Nat := 4983230072969 + 3 ^ 40 * 3160487 * 2
def baseEnd_3160487 : Nat := 1622848933286481313777691

theorem tailTrace_3160487 : CollatzResearch.WordTrace tailWord_3160487 prefixEnd_3160487 1622848933286481313777691 := by
  unfold tailWord_3160487
  simp only [CollatzResearch.WordTrace]
  refine ⟨115272430901102842051567715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76848287267401894701045143 115272430901102842051567715)
  ·
    refine ⟨172908646351654263077351573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115272430901102842051567715 172908646351654263077351573)
    ·
      refine ⟨8105092797733793581750855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172908646351654263077351573 8105092797733793581750855)
      ·
        refine ⟨12157639196600690372626283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8105092797733793581750855 12157639196600690372626283)
        ·
          refine ⟨18236458794901035558939425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12157639196600690372626283 18236458794901035558939425)
          ·
            refine ⟨13677344096175776669204569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18236458794901035558939425 13677344096175776669204569)
            ·
              refine ⟨10258008072131832501903427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13677344096175776669204569 10258008072131832501903427)
              ·
                refine ⟨15387012108197748752855141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258008072131832501903427 15387012108197748752855141)
                ·
                  refine ⟨2885064770287077891160339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15387012108197748752855141 2885064770287077891160339)
                  ·
                    refine ⟨4327597155430616836740509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2885064770287077891160339 4327597155430616836740509)
                    ·
                      refine ⟨1622848933286481313777691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327597155430616836740509 1622848933286481313777691)
                      ·
                        rfl

theorem cell23_3160487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_3160487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160487 prefixEnd_3160487 := by exact prefixLift 3160487
  have htrace : WordTrace (prefixWord ++ tailWord_3160487) baseStart_3160487 baseEnd_3160487 := by
    simpa [prefixWord, tailWord_3160487, baseEnd_3160487] using wordTrace_append hprefix tailTrace_3160487
  have hstable : (prefixWord ++ tailWord_3160487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160487).length < 2 ^ (prefixWord ++ tailWord_3160487).sum := by decide
  have hdescent : baseEnd_3160487 < baseStart_3160487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160523 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4]
def baseStart_3160523 : Nat := 118140960795 + 3160523 * 2 ^ 59
def prefixEnd_3160523 : Nat := 4983230072969 + 3 ^ 40 * 3160523 * 2
def baseEnd_3160523 : Nat := 1622867418590043172927525

theorem tailTrace_3160523 : CollatzResearch.WordTrace tailWord_3160523 prefixEnd_3160523 1622867418590043172927525 := by
  unfold tailWord_3160523
  simp only [CollatzResearch.WordTrace]
  refine ⟨115273743928972420199878223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76849162619314946799918815 115273743928972420199878223)
  ·
    refine ⟨172910615893458630299817335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115273743928972420199878223 172910615893458630299817335)
    ·
      refine ⟨259365923840187945449726003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172910615893458630299817335 259365923840187945449726003)
      ·
        refine ⟨389048885760281918174589005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259365923840187945449726003 389048885760281918174589005)
        ·
          refine ⟨145893332160105719315470877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389048885760281918174589005 145893332160105719315470877)
          ·
            refine ⟨54709999560039644743301579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145893332160105719315470877 54709999560039644743301579)
            ·
              refine ⟨82064999340059467114952369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54709999560039644743301579 82064999340059467114952369)
              ·
                refine ⟨61548749505044600336214277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82064999340059467114952369 61548749505044600336214277)
                ·
                  refine ⟨11540390532195862563040177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61548749505044600336214277 11540390532195862563040177)
                  ·
                    refine ⟨8655292899146896922280133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11540390532195862563040177 8655292899146896922280133)
                    ·
                      refine ⟨1622867418590043172927525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8655292899146896922280133 1622867418590043172927525)
                      ·
                        rfl

theorem cell23_3160523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_3160523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160523 prefixEnd_3160523 := by exact prefixLift 3160523
  have htrace : WordTrace (prefixWord ++ tailWord_3160523) baseStart_3160523 baseEnd_3160523 := by
    simpa [prefixWord, tailWord_3160523, baseEnd_3160523] using wordTrace_append hprefix tailTrace_3160523
  have hstable : (prefixWord ++ tailWord_3160523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160523).length < 2 ^ (prefixWord ++ tailWord_3160523).sum := by decide
  have hdescent : baseEnd_3160523 < baseStart_3160523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160544 : List Nat := [2, 1, 1, 3, 1, 1, 6, 2, 2, 2, 2]
def baseStart_3160544 : Nat := 118140960795 + 3160544 * 2 ^ 59
def prefixEnd_3160544 : Nat := 4983230072969 + 3 ^ 40 * 3160544 * 2
def baseEnd_3160544 : Nat := 1622878201683787590764929

theorem tailTrace_3160544 : CollatzResearch.WordTrace tailWord_3160544 prefixEnd_3160544 1622878201683787590764929 := by
  unfold tailWord_3160544
  simp only [CollatzResearch.WordTrace]
  refine ⟨57637254930948170393196343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76849673241264227190928457 57637254930948170393196343)
  ·
    refine ⟨86455882396422255589794515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57637254930948170393196343 86455882396422255589794515)
    ·
      refine ⟨129683823594633383384691773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86455882396422255589794515 129683823594633383384691773)
      ·
        refine ⟨48631433847987518769259415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129683823594633383384691773 48631433847987518769259415)
        ·
          refine ⟨72947150771981278153889123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48631433847987518769259415 72947150771981278153889123)
          ·
            refine ⟨109420726157971917230833685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72947150771981278153889123 109420726157971917230833685)
            ·
              refine ⟨5129096538654933620195329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109420726157971917230833685 5129096538654933620195329)
              ·
                refine ⟨3846822403991200215146497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5129096538654933620195329 3846822403991200215146497)
                ·
                  refine ⟨2885116802993400161359873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3846822403991200215146497 2885116802993400161359873)
                  ·
                    refine ⟨2163837602245050121019905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2885116802993400161359873 2163837602245050121019905)
                    ·
                      refine ⟨1622878201683787590764929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163837602245050121019905 1622878201683787590764929)
                      ·
                        rfl

theorem cell23_3160544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_3160544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160544 prefixEnd_3160544 := by exact prefixLift 3160544
  have htrace : WordTrace (prefixWord ++ tailWord_3160544) baseStart_3160544 baseEnd_3160544 := by
    simpa [prefixWord, tailWord_3160544, baseEnd_3160544] using wordTrace_append hprefix tailTrace_3160544
  have hstable : (prefixWord ++ tailWord_3160544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160544).length < 2 ^ (prefixWord ++ tailWord_3160544).sum := by decide
  have hdescent : baseEnd_3160544 < baseStart_3160544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160557 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3160557 : Nat := 118140960795 + 3160557 * 2 ^ 59
def prefixEnd_3160557 : Nat := 4983230072969 + 3 ^ 40 * 3160557 * 2
def baseEnd_3160557 : Nat := 1622884876932296039902369

theorem tailTrace_3160557 : CollatzResearch.WordTrace tailWord_3160557 prefixEnd_3160557 1622884876932296039902369 := by
  unfold tailWord_3160557
  simp only [CollatzResearch.WordTrace]
  refine ⟨115274984010849244006615925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76849989340566162671077283 115274984010849244006615925)
  ·
    refine ⟨10807029751017116625620243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115274984010849244006615925 10807029751017116625620243)
    ·
      refine ⟨16210544626525674938430365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807029751017116625620243 16210544626525674938430365)
      ·
        refine ⟨6078954234947128101911387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16210544626525674938430365 6078954234947128101911387)
        ·
          refine ⟨9118431352420692152867081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6078954234947128101911387 9118431352420692152867081)
          ·
            refine ⟨6838823514315519114650311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9118431352420692152867081 6838823514315519114650311)
            ·
              refine ⟨10258235271473278671975467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6838823514315519114650311 10258235271473278671975467)
              ·
                refine ⟨15387352907209918007963201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258235271473278671975467 15387352907209918007963201)
                ·
                  refine ⟨11540514680407438505972401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15387352907209918007963201 11540514680407438505972401)
                  ·
                    refine ⟨8655386010305578879479301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11540514680407438505972401 8655386010305578879479301)
                    ·
                      refine ⟨1622884876932296039902369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8655386010305578879479301 1622884876932296039902369)
                      ·
                        rfl

theorem cell23_3160557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3160557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160557 prefixEnd_3160557 := by exact prefixLift 3160557
  have htrace : WordTrace (prefixWord ++ tailWord_3160557) baseStart_3160557 baseEnd_3160557 := by
    simpa [prefixWord, tailWord_3160557, baseEnd_3160557] using wordTrace_append hprefix tailTrace_3160557
  have hstable : (prefixWord ++ tailWord_3160557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160557).length < 2 ^ (prefixWord ++ tailWord_3160557).sum := by decide
  have hdescent : baseEnd_3160557 < baseStart_3160557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160560 : List Nat := [2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3]
def baseStart_3160560 : Nat := 118140960795 + 3160560 * 2 ^ 59
def prefixEnd_3160560 : Nat := 4983230072969 + 3 ^ 40 * 3160560 * 2
def baseEnd_3160560 : Nat := 1622886417374259528164855

theorem tailTrace_3160560 : CollatzResearch.WordTrace tailWord_3160560 prefixEnd_3160560 1622886417374259528164855 := by
  unfold tailWord_3160560
  simp only [CollatzResearch.WordTrace]
  refine ⟨57637546714919187759487567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76850062286558917012650089 57637546714919187759487567)
  ·
    refine ⟨86456320072378781639231351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57637546714919187759487567 86456320072378781639231351)
    ·
      refine ⟨129684480108568172458847027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86456320072378781639231351 129684480108568172458847027)
      ·
        refine ⟨194526720162852258688270541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129684480108568172458847027 194526720162852258688270541)
        ·
          refine ⟨72947520061069597008101453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194526720162852258688270541 72947520061069597008101453)
          ·
            refine ⟨27355320022901098878038045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72947520061069597008101453 27355320022901098878038045)
            ·
              refine ⟨10258245008587912079264267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27355320022901098878038045 10258245008587912079264267)
              ·
                refine ⟨15387367512881868118896401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258245008587912079264267 15387367512881868118896401)
                ·
                  refine ⟨11540525634661401089172301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15387367512881868118896401 11540525634661401089172301)
                  ·
                    refine ⟨4327697112998025408439613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11540525634661401089172301 4327697112998025408439613)
                    ·
                      refine ⟨1622886417374259528164855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327697112998025408439613 1622886417374259528164855)
                      ·
                        rfl

theorem cell23_3160560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 2, 3, 3].length) (baseStart_3160560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160560 prefixEnd_3160560 := by exact prefixLift 3160560
  have htrace : WordTrace (prefixWord ++ tailWord_3160560) baseStart_3160560 baseEnd_3160560 := by
    simpa [prefixWord, tailWord_3160560, baseEnd_3160560] using wordTrace_append hprefix tailTrace_3160560
  have hstable : (prefixWord ++ tailWord_3160560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160560).length < 2 ^ (prefixWord ++ tailWord_3160560).sum := by decide
  have hdescent : baseEnd_3160560 < baseStart_3160560 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160563 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 1, 7]
def baseStart_3160563 : Nat := 118140960795 + 3160563 * 2 ^ 59
def prefixEnd_3160563 : Nat := 4983230072969 + 3 ^ 40 * 3160563 * 2
def baseEnd_3160563 : Nat := 540962652605407672142447

theorem tailTrace_3160563 : CollatzResearch.WordTrace tailWord_3160563 prefixEnd_3160563 540962652605407672142447 := by
  unfold tailWord_3160563
  simp only [CollatzResearch.WordTrace]
  refine ⟨115275202848827507031334343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76850135232551671354222895 115275202848827507031334343)
  ·
    refine ⟨172912804273241260547001515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115275202848827507031334343 172912804273241260547001515)
    ·
      refine ⟨259369206409861890820502273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172912804273241260547001515 259369206409861890820502273)
      ·
        refine ⟨194526904807396418115376705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259369206409861890820502273 194526904807396418115376705)
        ·
          refine ⟨145895178605547313586532529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194526904807396418115376705 145895178605547313586532529)
          ·
            refine ⟨109421383954160485189899397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145895178605547313586532529 109421383954160485189899397)
            ·
              refine ⟨20516509491405090973106137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109421383954160485189899397 20516509491405090973106137)
              ·
                refine ⟨15387382118553818229829603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20516509491405090973106137 15387382118553818229829603)
                ·
                  refine ⟨23081073177830727344744405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15387382118553818229829603 23081073177830727344744405)
                  ·
                    refine ⟨540962652605407672142447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23081073177830727344744405 540962652605407672142447)
                    ·
                      rfl

theorem cell23_3160563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 1, 7].length) (baseStart_3160563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160563 prefixEnd_3160563 := by exact prefixLift 3160563
  have htrace : WordTrace (prefixWord ++ tailWord_3160563) baseStart_3160563 baseEnd_3160563 := by
    simpa [prefixWord, tailWord_3160563, baseEnd_3160563] using wordTrace_append hprefix tailTrace_3160563
  have hstable : (prefixWord ++ tailWord_3160563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160563).length < 2 ^ (prefixWord ++ tailWord_3160563).sum := by decide
  have hdescent : baseEnd_3160563 < baseStart_3160563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160582 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_3160582 : Nat := 118140960795 + 3160582 * 2 ^ 59
def prefixEnd_3160582 : Nat := 4983230072969 + 3 ^ 40 * 3160582 * 2
def baseEnd_3160582 : Nat := 1622897713948658442089755

theorem tailTrace_3160582 : CollatzResearch.WordTrace tailWord_3160582 prefixEnd_3160582 1622897713948658442089755 := by
  unfold tailWord_3160582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602371744867458539883625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76850597223839115517517333 3602371744867458539883625)
  ·
    refine ⟨2701778808650593904912719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3602371744867458539883625 2701778808650593904912719)
    ·
      refine ⟨4052668212975890857369079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701778808650593904912719 4052668212975890857369079)
      ·
        refine ⟨6079002319463836286053619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052668212975890857369079 6079002319463836286053619)
        ·
          refine ⟨9118503479195754429080429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079002319463836286053619 9118503479195754429080429)
          ·
            refine ⟨3419438804698407910905161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9118503479195754429080429 3419438804698407910905161)
            ·
              refine ⟨2564579103523805933178871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3419438804698407910905161 2564579103523805933178871)
              ·
                refine ⟨3846868655285708899768307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564579103523805933178871 3846868655285708899768307)
                ·
                  refine ⟨5770302982928563349652461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846868655285708899768307 5770302982928563349652461)
                  ·
                    refine ⟨2163863618598211256119673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5770302982928563349652461 2163863618598211256119673)
                    ·
                      refine ⟨1622897713948658442089755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2163863618598211256119673 1622897713948658442089755)
                      ·
                        rfl

theorem cell23_3160582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_3160582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160582 prefixEnd_3160582 := by exact prefixLift 3160582
  have htrace : WordTrace (prefixWord ++ tailWord_3160582) baseStart_3160582 baseEnd_3160582 := by
    simpa [prefixWord, tailWord_3160582, baseEnd_3160582] using wordTrace_append hprefix tailTrace_3160582
  have hstable : (prefixWord ++ tailWord_3160582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160582).length < 2 ^ (prefixWord ++ tailWord_3160582).sum := by decide
  have hdescent : baseEnd_3160582 < baseStart_3160582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160637 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_3160637 : Nat := 118140960795 + 3160637 * 2 ^ 59
def prefixEnd_3160637 : Nat := 4983230072969 + 3 ^ 40 * 3160637 * 2
def baseEnd_3160637 : Nat := 1622925955384655726902001

theorem tailTrace_3160637 : CollatzResearch.WordTrace tailWord_3160637 prefixEnd_3160637 1622925955384655726902001 := by
  unfold tailWord_3160637
  simp only [CollatzResearch.WordTrace]
  refine ⟨115277901850559417669528165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76851934567039611779685443 115277901850559417669528165)
  ·
    refine ⟨21614606596979890813036531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115277901850559417669528165 21614606596979890813036531)
    ·
      refine ⟨32421909895469836219554797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21614606596979890813036531 32421909895469836219554797)
      ·
        refine ⟨12158216210801188582333049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32421909895469836219554797 12158216210801188582333049)
        ·
          refine ⟨9118662158100891436749787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12158216210801188582333049 9118662158100891436749787)
          ·
            refine ⟨13677993237151337155124681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9118662158100891436749787 13677993237151337155124681)
            ·
              refine ⟨10258494927863502866343511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13677993237151337155124681 10258494927863502866343511)
              ·
                refine ⟨15387742391795254299515267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10258494927863502866343511 15387742391795254299515267)
                ·
                  refine ⟨23081613587692881449272901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15387742391795254299515267 23081613587692881449272901)
                  ·
                    refine ⟨4327802547692415271738669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23081613587692881449272901 4327802547692415271738669)
                    ·
                      refine ⟨1622925955384655726902001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327802547692415271738669 1622925955384655726902001)
                      ·
                        rfl

theorem cell23_3160637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_3160637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160637 prefixEnd_3160637 := by exact prefixLift 3160637
  have htrace : WordTrace (prefixWord ++ tailWord_3160637) baseStart_3160637 baseEnd_3160637 := by
    simpa [prefixWord, tailWord_3160637, baseEnd_3160637] using wordTrace_append hprefix tailTrace_3160637
  have hstable : (prefixWord ++ tailWord_3160637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160637).length < 2 ^ (prefixWord ++ tailWord_3160637).sum := by decide
  have hdescent : baseEnd_3160637 < baseStart_3160637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160687 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 1, 5]
def baseStart_3160687 : Nat := 118140960795 + 3160687 * 2 ^ 59
def prefixEnd_3160687 : Nat := 4983230072969 + 3 ^ 40 * 3160687 * 2
def baseEnd_3160687 : Nat := 540983876472460177092257

theorem tailTrace_3160687 : CollatzResearch.WordTrace tailWord_3160687 prefixEnd_3160687 540983876472460177092257 := by
  unfold tailWord_3160687
  simp only [CollatzResearch.WordTrace]
  refine ⟨115279725500378276208848315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76853150333585517472565543 115279725500378276208848315)
  ·
    refine ⟨172919588250567414313272473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115279725500378276208848315 172919588250567414313272473)
    ·
      refine ⟨129689691187925560734954355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172919588250567414313272473 129689691187925560734954355)
      ·
        refine ⟨194534536781888341102431533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129689691187925560734954355 194534536781888341102431533)
        ·
          refine ⟨72950451293208127913411825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 194534536781888341102431533 72950451293208127913411825)
          ·
            refine ⟨54712838469906095935058869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72950451293208127913411825 54712838469906095935058869)
            ·
              refine ⟨5129328606553696493911769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54712838469906095935058869 5129328606553696493911769)
              ·
                refine ⟨3846996454915272370433827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5129328606553696493911769 3846996454915272370433827)
                ·
                  refine ⟨5770494682372908555650741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3846996454915272370433827 5770494682372908555650741)
                  ·
                    refine ⟨540983876472460177092257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5770494682372908555650741 540983876472460177092257)
                    ·
                      rfl

theorem cell23_3160687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 5].length) (baseStart_3160687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160687 prefixEnd_3160687 := by exact prefixLift 3160687
  have htrace : WordTrace (prefixWord ++ tailWord_3160687) baseStart_3160687 baseEnd_3160687 := by
    simpa [prefixWord, tailWord_3160687, baseEnd_3160687] using wordTrace_append hprefix tailTrace_3160687
  have hstable : (prefixWord ++ tailWord_3160687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160687).length < 2 ^ (prefixWord ++ tailWord_3160687).sum := by decide
  have hdescent : baseEnd_3160687 < baseStart_3160687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160700 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_3160700 : Nat := 118140960795 + 3160700 * 2 ^ 59
def prefixEnd_3160700 : Nat := 4983230072969 + 3 ^ 40 * 3160700 * 2
def baseEnd_3160700 : Nat := 540986101555296326804737

theorem tailTrace_3160700 : CollatzResearch.WordTrace tailWord_3160700 prefixEnd_3160700 540986101555296326804737 := by
  unfold tailWord_3160700
  simp only [CollatzResearch.WordTrace]
  refine ⟨57640099824665589714535777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76853466432887452952714369 57640099824665589714535777)
  ·
    refine ⟨43230074868499192285901833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57640099824665589714535777 43230074868499192285901833)
    ·
      refine ⟨32422556151374394214426375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43230074868499192285901833 32422556151374394214426375)
      ·
        refine ⟨48633834227061591321639563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32422556151374394214426375 48633834227061591321639563)
        ·
          refine ⟨72950751340592386982459345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48633834227061591321639563 72950751340592386982459345)
          ·
            refine ⟨54713063505444290236844509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72950751340592386982459345 54713063505444290236844509)
            ·
              refine ⟨20517398814541608838816691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54713063505444290236844509 20517398814541608838816691)
              ·
                refine ⟨30776098221812413258225037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20517398814541608838816691 30776098221812413258225037)
                ·
                  refine ⟨11541036833179654971834389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30776098221812413258225037 11541036833179654971834389)
                  ·
                    refine ⟨540986101555296326804737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11541036833179654971834389 540986101555296326804737)
                    ·
                      rfl

theorem cell23_3160700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_3160700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160700 prefixEnd_3160700 := by exact prefixLift 3160700
  have htrace : WordTrace (prefixWord ++ tailWord_3160700) baseStart_3160700 baseEnd_3160700 := by
    simpa [prefixWord, tailWord_3160700, baseEnd_3160700] using wordTrace_append hprefix tailTrace_3160700
  have hstable : (prefixWord ++ tailWord_3160700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160700).length < 2 ^ (prefixWord ++ tailWord_3160700).sum := by decide
  have hdescent : baseEnd_3160700 < baseStart_3160700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160704 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 1, 5]
def baseStart_3160704 : Nat := 118140960795 + 3160704 * 2 ^ 59
def prefixEnd_3160704 : Nat := 4983230072969 + 3 ^ 40 * 3160704 * 2
def baseEnd_3160704 : Nat := 540986786196168988254731

theorem tailTrace_3160704 : CollatzResearch.WordTrace tailWord_3160704 prefixEnd_3160704 540986786196168988254731 := by
  unfold tailWord_3160704
  simp only [CollatzResearch.WordTrace]
  refine ⟨57640172770658344056108583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76853563694211125408144777 57640172770658344056108583)
  ·
    refine ⟨86460259155987516084162875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57640172770658344056108583 86460259155987516084162875)
    ·
      refine ⟨129690388733981274126244313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86460259155987516084162875 129690388733981274126244313)
      ·
        refine ⟨97267791550485955594683235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129690388733981274126244313 97267791550485955594683235)
        ·
          refine ⟨145901687325728933392024853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97267791550485955594683235 145901687325728933392024853)
          ·
            refine ⟨6839141593393543752751165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145901687325728933392024853 6839141593393543752751165)
            ·
              refine ⟨2564678097522578907281687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6839141593393543752751165 2564678097522578907281687)
              ·
                refine ⟨3847017146283868360922531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564678097522578907281687 3847017146283868360922531)
                ·
                  refine ⟨5770525719425802541383797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847017146283868360922531 5770525719425802541383797)
                  ·
                    refine ⟨540986786196168988254731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5770525719425802541383797 540986786196168988254731)
                    ·
                      rfl

theorem cell23_3160704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 1, 5].length) (baseStart_3160704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160704 prefixEnd_3160704 := by exact prefixLift 3160704
  have htrace : WordTrace (prefixWord ++ tailWord_3160704) baseStart_3160704 baseEnd_3160704 := by
    simpa [prefixWord, tailWord_3160704, baseEnd_3160704] using wordTrace_append hprefix tailTrace_3160704
  have hstable : (prefixWord ++ tailWord_3160704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160704).length < 2 ^ (prefixWord ++ tailWord_3160704).sum := by decide
  have hdescent : baseEnd_3160704 < baseStart_3160704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160707 : List Nat := [1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 4]
def baseStart_3160707 : Nat := 118140960795 + 3160707 * 2 ^ 59
def prefixEnd_3160707 : Nat := 4983230072969 + 3 ^ 40 * 3160707 * 2
def baseEnd_3160707 : Nat := 1622961899030470453026679

theorem tailTrace_3160707 : CollatzResearch.WordTrace tailWord_3160707 prefixEnd_3160707 1622961899030470453026679 := by
  unfold tailWord_3160707
  simp only [CollatzResearch.WordTrace]
  refine ⟨115280454960305819624576375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76853636640203879749717583 115280454960305819624576375)
  ·
    refine ⟨172920682440458729436864563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115280454960305819624576375 172920682440458729436864563)
    ·
      refine ⟨259381023660688094155296845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172920682440458729436864563 259381023660688094155296845)
      ·
        refine ⟨97267883872758035308236317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259381023660688094155296845 97267883872758035308236317)
        ·
          refine ⟨36475456452284263240588619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97267883872758035308236317 36475456452284263240588619)
          ·
            refine ⟨54713184678426394860882929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36475456452284263240588619 54713184678426394860882929)
            ·
              refine ⟨41034888508819796145662197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54713184678426394860882929 41034888508819796145662197)
              ·
                refine ⟨3847020797701855888655831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41034888508819796145662197 3847020797701855888655831)
                ·
                  refine ⟨5770531196552783832983747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847020797701855888655831 5770531196552783832983747)
                  ·
                    refine ⟨8655796794829175749475621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770531196552783832983747 8655796794829175749475621)
                    ·
                      refine ⟨1622961899030470453026679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8655796794829175749475621 1622961899030470453026679)
                      ·
                        rfl

theorem cell23_3160707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_3160707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160707 prefixEnd_3160707 := by exact prefixLift 3160707
  have htrace : WordTrace (prefixWord ++ tailWord_3160707) baseStart_3160707 baseEnd_3160707 := by
    simpa [prefixWord, tailWord_3160707, baseEnd_3160707] using wordTrace_append hprefix tailTrace_3160707
  have hstable : (prefixWord ++ tailWord_3160707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160707).length < 2 ^ (prefixWord ++ tailWord_3160707).sum := by decide
  have hdescent : baseEnd_3160707 < baseStart_3160707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160724 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_3160724 : Nat := 118140960795 + 3160724 * 2 ^ 59
def prefixEnd_3160724 : Nat := 4983230072969 + 3 ^ 40 * 3160724 * 2
def baseEnd_3160724 : Nat := 1622970628201596886514101

theorem tailTrace_3160724 : CollatzResearch.WordTrace tailWord_3160724 prefixEnd_3160724 1622970628201596886514101 := by
  unfold tailWord_3160724
  simp only [CollatzResearch.WordTrace]
  refine ⟨57640537500622115763972613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76854050000829487685296817 57640537500622115763972613)
  ·
    refine ⟨10807600781366646705744865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57640537500622115763972613 10807600781366646705744865)
    ·
      refine ⟨8105700586024985029308649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10807600781366646705744865 8105700586024985029308649)
      ·
        refine ⟨6079275439518738771981487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8105700586024985029308649 6079275439518738771981487)
        ·
          refine ⟨9118913159278108157972231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6079275439518738771981487 9118913159278108157972231)
          ·
            refine ⟨13678369738917162236958347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9118913159278108157972231 13678369738917162236958347)
            ·
              refine ⟨20517554608375743355437521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13678369738917162236958347 20517554608375743355437521)
              ·
                refine ⟨15388165956281807516578141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20517554608375743355437521 15388165956281807516578141)
                ·
                  refine ⟨5770562233605677818716803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15388165956281807516578141 5770562233605677818716803)
                  ·
                    refine ⟨8655843350408516728075205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770562233605677818716803 8655843350408516728075205)
                    ·
                      refine ⟨1622970628201596886514101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8655843350408516728075205 1622970628201596886514101)
                      ·
                        rfl

theorem cell23_3160724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_3160724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160724 prefixEnd_3160724 := by exact prefixLift 3160724
  have htrace : WordTrace (prefixWord ++ tailWord_3160724) baseStart_3160724 baseEnd_3160724 := by
    simpa [prefixWord, tailWord_3160724, baseEnd_3160724] using wordTrace_append hprefix tailTrace_3160724
  have hstable : (prefixWord ++ tailWord_3160724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160724).length < 2 ^ (prefixWord ++ tailWord_3160724).sum := by decide
  have hdescent : baseEnd_3160724 < baseStart_3160724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160727 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_3160727 : Nat := 118140960795 + 3160727 * 2 ^ 59
def prefixEnd_3160727 : Nat := 4983230072969 + 3 ^ 40 * 3160727 * 2
def baseEnd_3160727 : Nat := 1622972168643560374776587

theorem tailTrace_3160727 : CollatzResearch.WordTrace tailWord_3160727 prefixEnd_3160727 1622972168643560374776587 := by
  unfold tailWord_3160727
  simp only [CollatzResearch.WordTrace]
  refine ⟨115281184420233363040304435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76854122946822242026869623 115281184420233363040304435)
  ·
    refine ⟨172921776630350044560456653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115281184420233363040304435 172921776630350044560456653)
    ·
      refine ⟨64845666236381266710171245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172921776630350044560456653 64845666236381266710171245)
      ·
        refine ⟨24317124838642975016314217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64845666236381266710171245 24317124838642975016314217)
        ·
          refine ⟨18237843628982231262235663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24317124838642975016314217 18237843628982231262235663)
          ·
            refine ⟨27356765443473346893353495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18237843628982231262235663 27356765443473346893353495)
            ·
              refine ⟨41035148165210020340030243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27356765443473346893353495 41035148165210020340030243)
              ·
                refine ⟨61552722247815030510045365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41035148165210020340030243 61552722247815030510045365)
                ·
                  refine ⟨5770567710732659110316753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61552722247815030510045365 5770567710732659110316753)
                  ·
                    refine ⟨4327925783049494332737565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5770567710732659110316753 4327925783049494332737565)
                    ·
                      refine ⟨1622972168643560374776587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4327925783049494332737565 1622972168643560374776587)
                      ·
                        rfl

theorem cell23_3160727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_3160727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160727 prefixEnd_3160727 := by exact prefixLift 3160727
  have htrace : WordTrace (prefixWord ++ tailWord_3160727) baseStart_3160727 baseEnd_3160727 := by
    simpa [prefixWord, tailWord_3160727, baseEnd_3160727] using wordTrace_append hprefix tailTrace_3160727
  have hstable : (prefixWord ++ tailWord_3160727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160727).length < 2 ^ (prefixWord ++ tailWord_3160727).sum := by decide
  have hdescent : baseEnd_3160727 < baseStart_3160727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160734 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_3160734 : Nat := 118140960795 + 3160734 * 2 ^ 59
def prefixEnd_3160734 : Nat := 4983230072969 + 3 ^ 40 * 3160734 * 2
def baseEnd_3160734 : Nat := 540991921002713949129685

theorem tailTrace_3160734 : CollatzResearch.WordTrace tailWord_3160734 prefixEnd_3160734 540991921002713949129685 := by
  unfold tailWord_3160734
  simp only [CollatzResearch.WordTrace]
  refine ⟨14410179966401000404476157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76854293154138668823872837 14410179966401000404476157)
  ·
    refine ⟨5403817487400375151678559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14410179966401000404476157 5403817487400375151678559)
    ·
      refine ⟨8105726231100562727517839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5403817487400375151678559 8105726231100562727517839)
      ·
        refine ⟨12158589346650844091276759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8105726231100562727517839 12158589346650844091276759)
        ·
          refine ⟨18237884019976266136915139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12158589346650844091276759 18237884019976266136915139)
          ·
            refine ⟨27356826029964399205372709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18237884019976266136915139 27356826029964399205372709)
            ·
              refine ⟨5129404880618324851007383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27356826029964399205372709 5129404880618324851007383)
              ·
                refine ⟨7694107320927487276511075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129404880618324851007383 7694107320927487276511075)
                ·
                  refine ⟨11541160981391230914766613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694107320927487276511075 11541160981391230914766613)
                  ·
                    refine ⟨540991921002713949129685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11541160981391230914766613 540991921002713949129685)
                    ·
                      rfl

theorem cell23_3160734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_3160734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160734 prefixEnd_3160734 := by exact prefixLift 3160734
  have htrace : WordTrace (prefixWord ++ tailWord_3160734) baseStart_3160734 baseEnd_3160734 := by
    simpa [prefixWord, tailWord_3160734, baseEnd_3160734] using wordTrace_append hprefix tailTrace_3160734
  have hstable : (prefixWord ++ tailWord_3160734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160734).length < 2 ^ (prefixWord ++ tailWord_3160734).sum := by decide
  have hdescent : baseEnd_3160734 < baseStart_3160734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160758 : List Nat := [5, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3160758 : Nat := 118140960795 + 3160758 * 2 ^ 59
def prefixEnd_3160758 : Nat := 4983230072969 + 3 ^ 40 * 3160758 * 2
def baseEnd_3160758 : Nat := 1622988086543849753488945

theorem tailTrace_3160758 : CollatzResearch.WordTrace tailWord_3160758 prefixEnd_3160758 1622988086543849753488945 := by
  unfold tailWord_3160758
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205144692695065958417683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76854876722080703556455285 7205144692695065958417683)
  ·
    refine ⟨10807717039042598937626525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205144692695065958417683 10807717039042598937626525)
    ·
      refine ⟨4052893889640974601609947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10807717039042598937626525 4052893889640974601609947)
      ·
        refine ⟨6079340834461461902414921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4052893889640974601609947 6079340834461461902414921)
        ·
          refine ⟨4559505625846096426811191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6079340834461461902414921 4559505625846096426811191)
          ·
            refine ⟨6839258438769144640216787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559505625846096426811191 6839258438769144640216787)
            ·
              refine ⟨10258887658153716960325181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6839258438769144640216787 10258887658153716960325181)
              ·
                refine ⟨3847082871807643860121943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10258887658153716960325181 3847082871807643860121943)
                ·
                  refine ⟨5770624307711465790182915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847082871807643860121943 5770624307711465790182915)
                  ·
                    refine ⟨8655936461567198685274373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770624307711465790182915 8655936461567198685274373)
                    ·
                      refine ⟨1622988086543849753488945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8655936461567198685274373 1622988086543849753488945)
                      ·
                        rfl

theorem cell23_3160758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3160758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160758 prefixEnd_3160758 := by exact prefixLift 3160758
  have htrace : WordTrace (prefixWord ++ tailWord_3160758) baseStart_3160758 baseEnd_3160758 := by
    simpa [prefixWord, tailWord_3160758, baseEnd_3160758] using wordTrace_append hprefix tailTrace_3160758
  have hstable : (prefixWord ++ tailWord_3160758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160758).length < 2 ^ (prefixWord ++ tailWord_3160758).sum := by decide
  have hdescent : baseEnd_3160758 < baseStart_3160758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160788 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_3160788 : Nat := 118140960795 + 3160788 * 2 ^ 59
def prefixEnd_3160788 : Nat := 4983230072969 + 3 ^ 40 * 3160788 * 2
def baseEnd_3160788 : Nat := 1623003490963484636113807

theorem tailTrace_3160788 : CollatzResearch.WordTrace tailWord_3160788 prefixEnd_3160788 1623003490963484636113807 := by
  unfold tailWord_3160788
  simp only [CollatzResearch.WordTrace]
  refine ⟨57641704636506185229137509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76855606182008246972183345 57641704636506185229137509)
  ·
    refine ⟨10807819619344909730463283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57641704636506185229137509 10807819619344909730463283)
    ·
      refine ⟨16211729429017364595694925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10807819619344909730463283 16211729429017364595694925)
      ·
        refine ⟨6079398535881511723385597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16211729429017364595694925 6079398535881511723385597)
        ·
          refine ⟨2279774450955566896269599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6079398535881511723385597 2279774450955566896269599)
          ·
            refine ⟨3419661676433350344404399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2279774450955566896269599 3419661676433350344404399)
            ·
              refine ⟨5129492514650025516606599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419661676433350344404399 5129492514650025516606599)
              ·
                refine ⟨7694238771975038274909899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129492514650025516606599 7694238771975038274909899)
                ·
                  refine ⟨11541358157962557412364849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694238771975038274909899 11541358157962557412364849)
                  ·
                    refine ⟨8656018618471918059273637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11541358157962557412364849 8656018618471918059273637)
                    ·
                      refine ⟨1623003490963484636113807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8656018618471918059273637 1623003490963484636113807)
                      ·
                        rfl

theorem cell23_3160788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_3160788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160788 prefixEnd_3160788 := by exact prefixLift 3160788
  have htrace : WordTrace (prefixWord ++ tailWord_3160788) baseStart_3160788 baseEnd_3160788 := by
    simpa [prefixWord, tailWord_3160788, baseEnd_3160788] using wordTrace_append hprefix tailTrace_3160788
  have hstable : (prefixWord ++ tailWord_3160788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160788).length < 2 ^ (prefixWord ++ tailWord_3160788).sum := by decide
  have hdescent : baseEnd_3160788 < baseStart_3160788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160801 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_3160801 : Nat := 118140960795 + 3160801 * 2 ^ 59
def prefixEnd_3160801 : Nat := 4983230072969 + 3 ^ 40 * 3160801 * 2
def baseEnd_3160801 : Nat := 1623010166211993085251247

theorem tailTrace_3160801 : CollatzResearch.WordTrace tailWord_3160801 prefixEnd_3160801 1623010166211993085251247 := by
  unfold tailWord_3160801
  simp only [CollatzResearch.WordTrace]
  refine ⟨115283883421965273678498257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76855922281310182452332171 115283883421965273678498257)
  ·
    refine ⟨86462912566473955258873693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115283883421965273678498257 86462912566473955258873693)
    ·
      refine ⟨32423592212427733222077635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86462912566473955258873693 32423592212427733222077635)
      ·
        refine ⟨48635388318641599833116453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32423592212427733222077635 48635388318641599833116453)
        ·
          refine ⟨9119135309745299968709335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48635388318641599833116453 9119135309745299968709335)
          ·
            refine ⟨13678702964617949953064003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119135309745299968709335 13678702964617949953064003)
            ·
              refine ⟨20518054446926924929596005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13678702964617949953064003 20518054446926924929596005)
              ·
                refine ⟨3847135208798798424299251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20518054446926924929596005 3847135208798798424299251)
                ·
                  refine ⟨5770702813198197636448877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847135208798798424299251 5770702813198197636448877)
                  ·
                    refine ⟨2164013554949324113668329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5770702813198197636448877 2164013554949324113668329)
                    ·
                      refine ⟨1623010166211993085251247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164013554949324113668329 1623010166211993085251247)
                      ·
                        rfl

theorem cell23_3160801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_3160801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160801 prefixEnd_3160801 := by exact prefixLift 3160801
  have htrace : WordTrace (prefixWord ++ tailWord_3160801) baseStart_3160801 baseEnd_3160801 := by
    simpa [prefixWord, tailWord_3160801, baseEnd_3160801] using wordTrace_append hprefix tailTrace_3160801
  have hstable : (prefixWord ++ tailWord_3160801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160801).length < 2 ^ (prefixWord ++ tailWord_3160801).sum := by decide
  have hdescent : baseEnd_3160801 < baseStart_3160801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160817 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 5]
def baseStart_3160817 : Nat := 118140960795 + 3160817 * 2 ^ 59
def prefixEnd_3160817 : Nat := 4983230072969 + 3 ^ 40 * 3160817 * 2
def baseEnd_3160817 : Nat := 1623018381902465022651173

theorem tailTrace_3160817 : CollatzResearch.WordTrace tailWord_3160817 prefixEnd_3160817 1623018381902465022651173 := by
  unfold tailWord_3160817
  simp only [CollatzResearch.WordTrace]
  refine ⟨115284466989907308411080705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76856311326604872274053803 115284466989907308411080705)
  ·
    refine ⟨86463350242430481308310529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115284466989907308411080705 86463350242430481308310529)
    ·
      refine ⟨64847512681822860981232897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86463350242430481308310529 64847512681822860981232897)
      ·
        refine ⟨48635634511367145735924673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64847512681822860981232897 48635634511367145735924673)
        ·
          refine ⟨36476725883525359301943505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48635634511367145735924673 36476725883525359301943505)
          ·
            refine ⟨27357544412644019476457629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36476725883525359301943505 27357544412644019476457629)
            ·
              refine ⟨10259079154741507303671611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27357544412644019476457629 10259079154741507303671611)
              ·
                refine ⟨15388618732112260955507417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259079154741507303671611 15388618732112260955507417)
                ·
                  refine ⟨11541464049084195716630563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15388618732112260955507417 11541464049084195716630563)
                  ·
                    refine ⟨17312196073626293574945845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11541464049084195716630563 17312196073626293574945845)
                    ·
                      refine ⟨1623018381902465022651173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17312196073626293574945845 1623018381902465022651173)
                      ·
                        rfl

theorem cell23_3160817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_3160817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160817 prefixEnd_3160817 := by exact prefixLift 3160817
  have htrace : WordTrace (prefixWord ++ tailWord_3160817) baseStart_3160817 baseEnd_3160817 := by
    simpa [prefixWord, tailWord_3160817, baseEnd_3160817] using wordTrace_append hprefix tailTrace_3160817
  have hstable : (prefixWord ++ tailWord_3160817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160817).length < 2 ^ (prefixWord ++ tailWord_3160817).sum := by decide
  have hdescent : baseEnd_3160817 < baseStart_3160817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160831 : List Nat := [1, 1, 2, 2, 1, 3, 1, 6, 2, 2, 2]
def baseStart_3160831 : Nat := 118140960795 + 3160831 * 2 ^ 59
def prefixEnd_3160831 : Nat := 4983230072969 + 3 ^ 40 * 3160831 * 2
def baseEnd_3160831 : Nat := 1623025570631627967876109

theorem tailTrace_3160831 : CollatzResearch.WordTrace tailWord_3160831 prefixEnd_3160831 1623025570631627967876109 := by
  unfold tailWord_3160831
  simp only [CollatzResearch.WordTrace]
  refine ⟨115284977611856588802090347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76856651741237725868060231 115284977611856588802090347)
  ·
    refine ⟨172927466417784883203135521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115284977611856588802090347 172927466417784883203135521)
    ·
      refine ⟨129695599813338662402351641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172927466417784883203135521 129695599813338662402351641)
      ·
        refine ⟨97271699860003996801763731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129695599813338662402351641 97271699860003996801763731)
        ·
          refine ⟨145907549790005995202645597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97271699860003996801763731 145907549790005995202645597)
          ·
            refine ⟨54715331171252248200992099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145907549790005995202645597 54715331171252248200992099)
            ·
              refine ⟨82072996756878372301488149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54715331171252248200992099 82072996756878372301488149)
              ·
                refine ⟨3847171722978673701632257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82072996756878372301488149 3847171722978673701632257)
                ·
                  refine ⟨2885378792234005276224193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847171722978673701632257 2885378792234005276224193)
                  ·
                    refine ⟨2164034094175503957168145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2885378792234005276224193 2164034094175503957168145)
                    ·
                      refine ⟨1623025570631627967876109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164034094175503957168145 1623025570631627967876109)
                      ·
                        rfl

theorem cell23_3160831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 6, 2, 2, 2].length) (baseStart_3160831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160831 prefixEnd_3160831 := by exact prefixLift 3160831
  have htrace : WordTrace (prefixWord ++ tailWord_3160831) baseStart_3160831 baseEnd_3160831 := by
    simpa [prefixWord, tailWord_3160831, baseEnd_3160831] using wordTrace_append hprefix tailTrace_3160831
  have hstable : (prefixWord ++ tailWord_3160831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160831).length < 2 ^ (prefixWord ++ tailWord_3160831).sum := by decide
  have hdescent : baseEnd_3160831 < baseStart_3160831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160847 : List Nat := [1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 3]
def baseStart_3160847 : Nat := 118140960795 + 3160847 * 2 ^ 59
def prefixEnd_3160847 : Nat := 4983230072969 + 3 ^ 40 * 3160847 * 2
def baseEnd_3160847 : Nat := 1623033786322099905276035

theorem tailTrace_3160847 : CollatzResearch.WordTrace tailWord_3160847 prefixEnd_3160847 1623033786322099905276035 := by
  unfold tailWord_3160847
  simp only [CollatzResearch.WordTrace]
  refine ⟨115285561179798623534672795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76857040786532415689781863 115285561179798623534672795)
  ·
    refine ⟨172928341769697935302009193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115285561179798623534672795 172928341769697935302009193)
    ·
      refine ⟨129696256327273451476506895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172928341769697935302009193 129696256327273451476506895)
      ·
        refine ⟨194544384490910177214760343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129696256327273451476506895 194544384490910177214760343)
        ·
          refine ⟨291816576736365265822140515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194544384490910177214760343 291816576736365265822140515)
          ·
            refine ⟨437724865104547898733210773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291816576736365265822140515 437724865104547898733210773)
            ·
              refine ⟨20518353051775682753119255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 437724865104547898733210773 20518353051775682753119255)
              ·
                refine ⟨30777529577663524129678883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20518353051775682753119255 30777529577663524129678883)
                ·
                  refine ⟨46166294366495286194518325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30777529577663524129678883 46166294366495286194518325)
                  ·
                    refine ⟨4328090096858933080736093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46166294366495286194518325 4328090096858933080736093)
                    ·
                      refine ⟨1623033786322099905276035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4328090096858933080736093 1623033786322099905276035)
                      ·
                        rfl

theorem cell23_3160847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_3160847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160847 prefixEnd_3160847 := by exact prefixLift 3160847
  have htrace : WordTrace (prefixWord ++ tailWord_3160847) baseStart_3160847 baseEnd_3160847 := by
    simpa [prefixWord, tailWord_3160847, baseEnd_3160847] using wordTrace_append hprefix tailTrace_3160847
  have hstable : (prefixWord ++ tailWord_3160847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160847).length < 2 ^ (prefixWord ++ tailWord_3160847).sum := by decide
  have hdescent : baseEnd_3160847 < baseStart_3160847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160921 : List Nat := [1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 4]
def baseStart_3160921 : Nat := 118140960795 + 3160921 * 2 ^ 59
def prefixEnd_3160921 : Nat := 4983230072969 + 3 ^ 40 * 3160921 * 2
def baseEnd_3160921 : Nat := 1623071783890532615750695

theorem tailTrace_3160921 : CollatzResearch.WordTrace tailWord_3160921 prefixEnd_3160921 1623071783890532615750695 := by
  unfold tailWord_3160921
  simp only [CollatzResearch.WordTrace]
  refine ⟨115288260181530534172866617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76858840121020356115244411 115288260181530534172866617)
  ·
    refine ⟨86466195136147900629649963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115288260181530534172866617 86466195136147900629649963)
    ·
      refine ⟨129699292704221850944474945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86466195136147900629649963 129699292704221850944474945)
      ·
        refine ⟨97274469528166388208356209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129699292704221850944474945 97274469528166388208356209)
        ·
          refine ⟨72955852146124791156267157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97274469528166388208356209 72955852146124791156267157)
          ·
            refine ⟨3419805569349599585450023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72955852146124791156267157 3419805569349599585450023)
            ·
              refine ⟨5129708354024399378175035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3419805569349599585450023 5129708354024399378175035)
              ·
                refine ⟨7694562531036599067262553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5129708354024399378175035 7694562531036599067262553)
                ·
                  refine ⟨5770921898277449300446915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7694562531036599067262553 5770921898277449300446915)
                  ·
                    refine ⟨8656382847416173950670373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5770921898277449300446915 8656382847416173950670373)
                    ·
                      refine ⟨1623071783890532615750695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8656382847416173950670373 1623071783890532615750695)
                      ·
                        rfl

theorem cell23_3160921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 1, 2, 1, 4].length) (baseStart_3160921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160921 prefixEnd_3160921 := by exact prefixLift 3160921
  have htrace : WordTrace (prefixWord ++ tailWord_3160921) baseStart_3160921 baseEnd_3160921 := by
    simpa [prefixWord, tailWord_3160921, baseEnd_3160921] using wordTrace_append hprefix tailTrace_3160921
  have hstable : (prefixWord ++ tailWord_3160921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160921).length < 2 ^ (prefixWord ++ tailWord_3160921).sum := by decide
  have hdescent : baseEnd_3160921 < baseStart_3160921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160927 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 8]
def baseStart_3160927 : Nat := 118140960795 + 3160927 * 2 ^ 59
def prefixEnd_3160927 : Nat := 4983230072969 + 3 ^ 40 * 3160927 * 2
def baseEnd_3160927 : Nat := 180341651641606621363963

theorem tailTrace_3160927 : CollatzResearch.WordTrace tailWord_3160927 prefixEnd_3160927 180341651641606621363963 := by
  unfold tailWord_3160927
  simp only [CollatzResearch.WordTrace]
  refine ⟨115288479019508797197585035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76858986013005864798390023 115288479019508797197585035)
  ·
    refine ⟨172932718529263195796377553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115288479019508797197585035 172932718529263195796377553)
    ·
      refine ⟨129699538896947396847283165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172932718529263195796377553 129699538896947396847283165)
      ·
        refine ⟨48637327086355273817731187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129699538896947396847283165 48637327086355273817731187)
        ·
          refine ⟨72955990629532910726596781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48637327086355273817731187 72955990629532910726596781)
          ·
            refine ⟨27358496486074841522473793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72955990629532910726596781 27358496486074841522473793)
            ·
              refine ⟨20518872364556131141855345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27358496486074841522473793 20518872364556131141855345)
              ·
                refine ⟨15389154273417098356391509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20518872364556131141855345 15389154273417098356391509)
                ·
                  refine ⟨180341651641606621363963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15389154273417098356391509 180341651641606621363963)
                  ·
                    rfl

theorem cell23_3160927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 8].length) (baseStart_3160927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160927 prefixEnd_3160927 := by exact prefixLift 3160927
  have htrace : WordTrace (prefixWord ++ tailWord_3160927) baseStart_3160927 baseEnd_3160927 := by
    simpa [prefixWord, tailWord_3160927, baseEnd_3160927] using wordTrace_append hprefix tailTrace_3160927
  have hstable : (prefixWord ++ tailWord_3160927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160927).length < 2 ^ (prefixWord ++ tailWord_3160927).sum := by decide
  have hdescent : baseEnd_3160927 < baseStart_3160927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160944 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 6]
def baseStart_3160944 : Nat := 118140960795 + 3160944 * 2 ^ 59
def prefixEnd_3160944 : Nat := 4983230072969 + 3 ^ 40 * 3160944 * 2
def baseEnd_3160944 : Nat := 180342621549509558418121

theorem tailTrace_3160944 : CollatzResearch.WordTrace tailWord_3160944 prefixEnd_3160944 180342621549509558418121 := by
  unfold tailWord_3160944
  simp only [CollatzResearch.WordTrace]
  refine ⟨57644549530223604550476943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76859399373631472733969257 57644549530223604550476943)
  ·
    refine ⟨86466824295335406825715415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57644549530223604550476943 86466824295335406825715415)
    ·
      refine ⟨129700236443003110238573123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86466824295335406825715415 129700236443003110238573123)
      ·
        refine ⟨194550354664504665357859685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129700236443003110238573123 194550354664504665357859685)
        ·
          refine ⟨36478191499594624754598691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194550354664504665357859685 36478191499594624754598691)
          ·
            refine ⟨54717287249391937131898037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36478191499594624754598691 54717287249391937131898037)
            ·
              refine ⟨5129745679630494106115441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54717287249391937131898037 5129745679630494106115441)
              ·
                refine ⟨3847309259722870579586581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5129745679630494106115441 3847309259722870579586581)
                ·
                  refine ⟨180342621549509558418121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3847309259722870579586581 180342621549509558418121)
                  ·
                    rfl

theorem cell23_3160944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 6].length) (baseStart_3160944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160944 prefixEnd_3160944 := by exact prefixLift 3160944
  have htrace : WordTrace (prefixWord ++ tailWord_3160944) baseStart_3160944 baseEnd_3160944 := by
    simpa [prefixWord, tailWord_3160944, baseEnd_3160944] using wordTrace_append hprefix tailTrace_3160944
  have hstable : (prefixWord ++ tailWord_3160944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160944).length < 2 ^ (prefixWord ++ tailWord_3160944).sum := by decide
  have hdescent : baseEnd_3160944 < baseStart_3160944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160947 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_3160947 : Nat := 118140960795 + 3160947 * 2 ^ 59
def prefixEnd_3160947 : Nat := 4983230072969 + 3 ^ 40 * 3160947 * 2
def baseEnd_3160947 : Nat := 1623085134387549514025575

theorem tailTrace_3160947 : CollatzResearch.WordTrace tailWord_3160947 prefixEnd_3160947 1623085134387549514025575 := by
  unfold tailWord_3160947
  simp only [CollatzResearch.WordTrace]
  refine ⟨115289208479436340613313095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76859472319624227075542063 115289208479436340613313095)
  ·
    refine ⟨172933812719154510919969643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115289208479436340613313095 172933812719154510919969643)
    ·
      refine ⟨259400719078731766379954465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172933812719154510919969643 259400719078731766379954465)
      ·
        refine ⟨194550539309048824784965849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259400719078731766379954465 194550539309048824784965849)
        ·
          refine ⟨145912904481786618588724387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194550539309048824784965849 145912904481786618588724387)
          ·
            refine ⟨218869356722679927883086581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145912904481786618588724387 218869356722679927883086581)
            ·
              refine ⟨20519002192751243239039367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218869356722679927883086581 20519002192751243239039367)
              ·
                refine ⟨30778503289126864858559051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20519002192751243239039367 30778503289126864858559051)
                ·
                  refine ⟨46167754933690297287838577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30778503289126864858559051 46167754933690297287838577)
                  ·
                    refine ⟨34625816200267722965878933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46167754933690297287838577 34625816200267722965878933)
                    ·
                      refine ⟨1623085134387549514025575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34625816200267722965878933 1623085134387549514025575)
                      ·
                        rfl

theorem cell23_3160947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_3160947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160947 prefixEnd_3160947 := by exact prefixLift 3160947
  have htrace : WordTrace (prefixWord ++ tailWord_3160947) baseStart_3160947 baseEnd_3160947 := by
    simpa [prefixWord, tailWord_3160947, baseEnd_3160947] using wordTrace_append hprefix tailTrace_3160947
  have hstable : (prefixWord ++ tailWord_3160947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160947).length < 2 ^ (prefixWord ++ tailWord_3160947).sum := by decide
  have hdescent : baseEnd_3160947 < baseStart_3160947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160971 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 3]
def baseStart_3160971 : Nat := 118140960795 + 3160971 * 2 ^ 59
def prefixEnd_3160971 : Nat := 4983230072969 + 3 ^ 40 * 3160971 * 2
def baseEnd_3160971 : Nat := 1623097457923257420125465

theorem tailTrace_3160971 : CollatzResearch.WordTrace tailWord_3160971 prefixEnd_3160971 1623097457923257420125465 := by
  unfold tailWord_3160971
  simp only [CollatzResearch.WordTrace]
  refine ⟨115290083831349392712186767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76860055887566261808124511 115290083831349392712186767)
  ·
    refine ⟨172935125747024089068280151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115290083831349392712186767 172935125747024089068280151)
    ·
      refine ⟨259402688620536133602420227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172935125747024089068280151 259402688620536133602420227)
      ·
        refine ⟨389104032930804200403630341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259402688620536133602420227 389104032930804200403630341)
        ·
          refine ⟨72957006174525787575680689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389104032930804200403630341 72957006174525787575680689)
          ·
            refine ⟨54717754630894340681760517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72957006174525787575680689 54717754630894340681760517)
            ·
              refine ⟨10259578993292688877830097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54717754630894340681760517 10259578993292688877830097)
              ·
                refine ⟨7694684244969516658372573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10259578993292688877830097 7694684244969516658372573)
                ·
                  refine ⟨2885506591863568746889715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7694684244969516658372573 2885506591863568746889715)
                  ·
                    refine ⟨4328259887795353120334573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2885506591863568746889715 4328259887795353120334573)
                    ·
                      refine ⟨1623097457923257420125465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4328259887795353120334573 1623097457923257420125465)
                      ·
                        rfl

theorem cell23_3160971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 3].length) (baseStart_3160971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160971 prefixEnd_3160971 := by exact prefixLift 3160971
  have htrace : WordTrace (prefixWord ++ tailWord_3160971) baseStart_3160971 baseEnd_3160971 := by
    simpa [prefixWord, tailWord_3160971, baseEnd_3160971] using wordTrace_append hprefix tailTrace_3160971
  have hstable : (prefixWord ++ tailWord_3160971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160971).length < 2 ^ (prefixWord ++ tailWord_3160971).sum := by decide
  have hdescent : baseEnd_3160971 < baseStart_3160971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160981 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 1, 5, 2]
def baseStart_3160981 : Nat := 118140960795 + 3160981 * 2 ^ 59
def prefixEnd_3160981 : Nat := 4983230072969 + 3 ^ 40 * 3160981 * 2
def baseEnd_3160981 : Nat := 1623102592729802381000419

theorem tailTrace_3160981 : CollatzResearch.WordTrace tailWord_3160981 prefixEnd_3160981 1623102592729802381000419 := by
  unfold tailWord_3160981
  simp only [CollatzResearch.WordTrace]
  refine ⟨115290448561313164420050797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76860299040875442946700531 115290448561313164420050797)
  ·
    refine ⟨43233918210492436657519049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115290448561313164420050797 43233918210492436657519049)
    ·
      refine ⟨32425438657869327493139287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43233918210492436657519049 32425438657869327493139287)
      ·
        refine ⟨48638157986803991239708931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32425438657869327493139287 48638157986803991239708931)
        ·
          refine ⟨72957236980205986859563397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48638157986803991239708931 72957236980205986859563397)
          ·
            refine ⟨13679481933788622536168137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72957236980205986859563397 13679481933788622536168137)
            ·
              refine ⟨10259611450341466902126103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13679481933788622536168137 10259611450341466902126103)
              ·
                refine ⟨15389417175512200353189155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259611450341466902126103 15389417175512200353189155)
                ·
                  refine ⟨23084125763268300529783733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15389417175512200353189155 23084125763268300529783733)
                  ·
                    refine ⟨2164136790306403174667225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23084125763268300529783733 2164136790306403174667225)
                    ·
                      refine ⟨1623102592729802381000419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164136790306403174667225 1623102592729802381000419)
                      ·
                        rfl

theorem cell23_3160981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_3160981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160981 prefixEnd_3160981 := by exact prefixLift 3160981
  have htrace : WordTrace (prefixWord ++ tailWord_3160981) baseStart_3160981 baseEnd_3160981 := by
    simpa [prefixWord, tailWord_3160981, baseEnd_3160981] using wordTrace_append hprefix tailTrace_3160981
  have hstable : (prefixWord ++ tailWord_3160981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160981).length < 2 ^ (prefixWord ++ tailWord_3160981).sum := by decide
  have hdescent : baseEnd_3160981 < baseStart_3160981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3160991 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 1, 5]
def baseStart_3160991 : Nat := 118140960795 + 3160991 * 2 ^ 59
def prefixEnd_3160991 : Nat := 4983230072969 + 3 ^ 40 * 3160991 * 2
def baseEnd_3160991 : Nat := 541035909178782447291791

theorem tailTrace_3160991 : CollatzResearch.WordTrace tailWord_3160991 prefixEnd_3160991 541035909178782447291791 := by
  unfold tailWord_3160991
  simp only [CollatzResearch.WordTrace]
  refine ⟨115290813291276936127914827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76860542194184624085276551 115290813291276936127914827)
  ·
    refine ⟨172936219936915404191872241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115290813291276936127914827 172936219936915404191872241)
    ·
      refine ⟨129702164952686553143904181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172936219936915404191872241 129702164952686553143904181)
      ·
        refine ⟨12159577964314364357241017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129702164952686553143904181 12159577964314364357241017)
        ·
          refine ⟨9119683473235773267930763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12159577964314364357241017 9119683473235773267930763)
          ·
            refine ⟨13679525209853659901896145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119683473235773267930763 13679525209853659901896145)
            ·
              refine ⟨10259643907390244926422109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13679525209853659901896145 10259643907390244926422109)
              ·
                refine ⟨3847366465271341847408291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10259643907390244926422109 3847366465271341847408291)
                ·
                  refine ⟨5771049697907012771112437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847366465271341847408291 5771049697907012771112437)
                  ·
                    refine ⟨541035909178782447291791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5771049697907012771112437 541035909178782447291791)
                    ·
                      rfl

theorem cell23_3160991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 1, 5].length) (baseStart_3160991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3160991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3160991 prefixEnd_3160991 := by exact prefixLift 3160991
  have htrace : WordTrace (prefixWord ++ tailWord_3160991) baseStart_3160991 baseEnd_3160991 := by
    simpa [prefixWord, tailWord_3160991, baseEnd_3160991] using wordTrace_append hprefix tailTrace_3160991
  have hstable : (prefixWord ++ tailWord_3160991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3160991).length < 2 ^ (prefixWord ++ tailWord_3160991).sum := by decide
  have hdescent : baseEnd_3160991 < baseStart_3160991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3160991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161024 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_3161024 : Nat := 118140960795 + 3161024 * 2 ^ 59
def prefixEnd_3161024 : Nat := 4983230072969 + 3 ^ 40 * 3161024 * 2
def baseEnd_3161024 : Nat := 1623124672397945712762721

theorem tailTrace_3161024 : CollatzResearch.WordTrace tailWord_3161024 prefixEnd_3161024 1623124672397945712762721 := by
  unfold tailWord_3161024
  simp only [CollatzResearch.WordTrace]
  refine ⟨57646008450078691381933063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76861344600104921842577417 57646008450078691381933063)
  ·
    refine ⟨86469012675118037072899595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57646008450078691381933063 86469012675118037072899595)
    ·
      refine ⟨129703519012677055609349393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86469012675118037072899595 129703519012677055609349393)
      ·
        refine ⟨97277639259507791707012045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129703519012677055609349393 97277639259507791707012045)
        ·
          refine ⟨36479114722315421890129517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97277639259507791707012045 36479114722315421890129517)
          ·
            refine ⟨13679668020868283208798569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36479114722315421890129517 13679668020868283208798569)
            ·
              refine ⟨10259751015651212406598927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13679668020868283208798569 10259751015651212406598927)
              ·
                refine ⟨15389626523476818609898391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10259751015651212406598927 15389626523476818609898391)
                ·
                  refine ⟨23084439785215227914847587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15389626523476818609898391 23084439785215227914847587)
                  ·
                    refine ⟨34626659677822841872271381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23084439785215227914847587 34626659677822841872271381)
                    ·
                      refine ⟨1623124672397945712762721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34626659677822841872271381 1623124672397945712762721)
                      ·
                        rfl

theorem cell23_3161024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_3161024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161024 prefixEnd_3161024 := by exact prefixLift 3161024
  have htrace : WordTrace (prefixWord ++ tailWord_3161024) baseStart_3161024 baseEnd_3161024 := by
    simpa [prefixWord, tailWord_3161024, baseEnd_3161024] using wordTrace_append hprefix tailTrace_3161024
  have hstable : (prefixWord ++ tailWord_3161024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161024).length < 2 ^ (prefixWord ++ tailWord_3161024).sum := by decide
  have hdescent : baseEnd_3161024 < baseStart_3161024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161045 : List Nat := [1, 3, 2, 3, 3, 1, 3, 1, 1, 1, 4]
def baseStart_3161045 : Nat := 118140960795 + 3161045 * 2 ^ 59
def prefixEnd_3161045 : Nat := 4983230072969 + 3 ^ 40 * 3161045 * 2
def baseEnd_3161045 : Nat := 1623135455491690130600125

theorem tailTrace_3161045 : CollatzResearch.WordTrace tailWord_3161045 prefixEnd_3161045 1623135455491690130600125 := by
  unfold tailWord_3161045
  simp only [CollatzResearch.WordTrace]
  refine ⟨115292782833081303350380589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76861855222054202233587059 115292782833081303350380589)
  ·
    refine ⟨43234793562405488756392721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115292782833081303350380589 43234793562405488756392721)
    ·
      refine ⟨32426095171804116567294541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43234793562405488756392721 32426095171804116567294541)
      ·
        refine ⟨12159785689426543712735453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32426095171804116567294541 12159785689426543712735453)
        ·
          refine ⟨4559919633534953892275795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12159785689426543712735453 4559919633534953892275795)
          ·
            refine ⟨6839879450302430838413693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4559919633534953892275795 6839879450302430838413693)
            ·
              refine ⟨2564954793863411564405135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6839879450302430838413693 2564954793863411564405135)
              ·
                refine ⟨3847432190795117346607703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2564954793863411564405135 3847432190795117346607703)
                ·
                  refine ⟨5771148286192676019911555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3847432190795117346607703 5771148286192676019911555)
                  ·
                    refine ⟨8656722429289014029867333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5771148286192676019911555 8656722429289014029867333)
                    ·
                      refine ⟨1623135455491690130600125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8656722429289014029867333 1623135455491690130600125)
                      ·
                        rfl

theorem cell23_3161045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_3161045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161045 prefixEnd_3161045 := by exact prefixLift 3161045
  have htrace : WordTrace (prefixWord ++ tailWord_3161045) baseStart_3161045 baseEnd_3161045 := by
    simpa [prefixWord, tailWord_3161045, baseEnd_3161045] using wordTrace_append hprefix tailTrace_3161045
  have hstable : (prefixWord ++ tailWord_3161045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161045).length < 2 ^ (prefixWord ++ tailWord_3161045).sum := by decide
  have hdescent : baseEnd_3161045 < baseStart_3161045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161064 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 2, 7]
def baseStart_3161064 : Nat := 118140960795 + 3161064 * 2 ^ 59
def prefixEnd_3161064 : Nat := 4983230072969 + 3 ^ 40 * 3161064 * 2
def baseEnd_3161064 : Nat := 541048403874708518754179

theorem tailTrace_3161064 : CollatzResearch.WordTrace tailWord_3161064 prefixEnd_3161064 541048403874708518754179 := by
  unfold tailWord_3161064
  simp only [CollatzResearch.WordTrace]
  refine ⟨57646737910006234797661123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76862317213341646396881497 57646737910006234797661123)
  ·
    refine ⟨86470106865009352196491685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57646737910006234797661123 86470106865009352196491685)
    ·
      refine ⟨16213145037189253536842191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86470106865009352196491685 16213145037189253536842191)
      ·
        refine ⟨24319717555783880305263287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16213145037189253536842191 24319717555783880305263287)
        ·
          refine ⟨36479576333675820457894931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24319717555783880305263287 36479576333675820457894931)
          ·
            refine ⟨54719364500513730686842397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36479576333675820457894931 54719364500513730686842397)
            ·
              refine ⟨20519761687692649007565899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54719364500513730686842397 20519761687692649007565899)
              ·
                refine ⟨30779642531538973511348849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20519761687692649007565899 30779642531538973511348849)
                ·
                  refine ⟨23084731898654230133511637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30779642531538973511348849 23084731898654230133511637)
                  ·
                    refine ⟨541048403874708518754179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23084731898654230133511637 541048403874708518754179)
                    ·
                      rfl

theorem cell23_3161064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_3161064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161064 prefixEnd_3161064 := by exact prefixLift 3161064
  have htrace : WordTrace (prefixWord ++ tailWord_3161064) baseStart_3161064 baseEnd_3161064 := by
    simpa [prefixWord, tailWord_3161064, baseEnd_3161064] using wordTrace_append hprefix tailTrace_3161064
  have hstable : (prefixWord ++ tailWord_3161064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161064).length < 2 ^ (prefixWord ++ tailWord_3161064).sum := by decide
  have hdescent : baseEnd_3161064 < baseStart_3161064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161078 : List Nat := [5, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_3161078 : Nat := 118140960795 + 3161078 * 2 ^ 59
def prefixEnd_3161078 : Nat := 4983230072969 + 3 ^ 40 * 3161078 * 2
def baseEnd_3161078 : Nat := 1623152400353288501487473

theorem tailTrace_3161078 : CollatzResearch.WordTrace tailWord_3161078 prefixEnd_3161078 1623152400353288501487473 := by
  unfold tailWord_3161078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7205874152622609374145743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76862657627974499990887925 7205874152622609374145743)
  ·
    refine ⟨10808811228933914061218615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7205874152622609374145743 10808811228933914061218615)
    ·
      refine ⟨16213216843400871091827923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10808811228933914061218615 16213216843400871091827923)
      ·
        refine ⟨24319825265101306637741885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16213216843400871091827923 24319825265101306637741885)
        ·
          refine ⟨9119934474412989989153207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24319825265101306637741885 9119934474412989989153207)
          ·
            refine ⟨13679901711619484983729811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9119934474412989989153207 13679901711619484983729811)
            ·
              refine ⟨20519852567429227475594717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13679901711619484983729811 20519852567429227475594717)
              ·
                refine ⟨7694944712785960303348019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20519852567429227475594717 7694944712785960303348019)
                ·
                  refine ⟨11542417069178940455022029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7694944712785960303348019 11542417069178940455022029)
                  ·
                    refine ⟨4328406400942102670633261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11542417069178940455022029 4328406400942102670633261)
                    ·
                      refine ⟨1623152400353288501487473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4328406400942102670633261 1623152400353288501487473)
                      ·
                        rfl

theorem cell23_3161078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_3161078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161078 prefixEnd_3161078 := by exact prefixLift 3161078
  have htrace : WordTrace (prefixWord ++ tailWord_3161078) baseStart_3161078 baseEnd_3161078 := by
    simpa [prefixWord, tailWord_3161078, baseEnd_3161078] using wordTrace_append hprefix tailTrace_3161078
  have hstable : (prefixWord ++ tailWord_3161078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161078).length < 2 ^ (prefixWord ++ tailWord_3161078).sum := by decide
  have hdescent : baseEnd_3161078 < baseStart_3161078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161106 : List Nat := [3, 2, 5, 1, 2, 1, 1, 2, 2, 4]
def baseStart_3161106 : Nat := 118140960795 + 3161106 * 2 ^ 59
def prefixEnd_3161106 : Nat := 4983230072969 + 3 ^ 40 * 3161106 * 2
def baseEnd_3161106 : Nat := 541055592603871463979115

theorem tailTrace_3161106 : CollatzResearch.WordTrace tailWord_3161106 prefixEnd_3161106 541055592603871463979115 := by
  unfold tailWord_3161106
  simp only [CollatzResearch.WordTrace]
  refine ⟨28823751921465077692087793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76863338457240207178900781 28823751921465077692087793)
  ·
    refine ⟨21617813941098808269065845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28823751921465077692087793 21617813941098808269065845)
    ·
      refine ⟨2026670056978013275224923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21617813941098808269065845 2026670056978013275224923)
      ·
        refine ⟨3040005085467019912837385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026670056978013275224923 3040005085467019912837385)
        ·
          refine ⟨2280003814100264934628039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3040005085467019912837385 2280003814100264934628039)
          ·
            refine ⟨3420005721150397401942059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280003814100264934628039 3420005721150397401942059)
            ·
              refine ⟨5130008581725596102913089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420005721150397401942059 5130008581725596102913089)
              ·
                refine ⟨3847506436294197077184817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5130008581725596102913089 3847506436294197077184817)
                ·
                  refine ⟨2885629827220647807888613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847506436294197077184817 2885629827220647807888613)
                  ·
                    refine ⟨541055592603871463979115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2885629827220647807888613 541055592603871463979115)
                    ·
                      rfl

theorem cell23_3161106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_3161106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161106 prefixEnd_3161106 := by exact prefixLift 3161106
  have htrace : WordTrace (prefixWord ++ tailWord_3161106) baseStart_3161106 baseEnd_3161106 := by
    simpa [prefixWord, tailWord_3161106, baseEnd_3161106] using wordTrace_append hprefix tailTrace_3161106
  have hstable : (prefixWord ++ tailWord_3161106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161106).length < 2 ^ (prefixWord ++ tailWord_3161106).sum := by decide
  have hdescent : baseEnd_3161106 < baseStart_3161106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161111 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 2, 6]
def baseStart_3161111 : Nat := 118140960795 + 3161111 * 2 ^ 59
def prefixEnd_3161111 : Nat := 4983230072969 + 3 ^ 40 * 3161111 * 2
def baseEnd_3161111 : Nat := 541056448404962290791607

theorem tailTrace_3161111 : CollatzResearch.WordTrace tailWord_3161111 prefixEnd_3161111 541056448404962290791607 := by
  unfold tailWord_3161111
  simp only [CollatzResearch.WordTrace]
  refine ⟨115295190050842196622283187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76863460033894797748188791 115295190050842196622283187)
  ·
    refine ⟨172942785076263294933424781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115295190050842196622283187 172942785076263294933424781)
    ·
      refine ⟨64853544403598735600034293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172942785076263294933424781 64853544403598735600034293)
      ·
        refine ⟨6080019787837381462503215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64853544403598735600034293 6080019787837381462503215)
        ·
          refine ⟨9120029681756072193754823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080019787837381462503215 9120029681756072193754823)
          ·
            refine ⟨13680044522634108290632235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9120029681756072193754823 13680044522634108290632235)
            ·
              refine ⟨20520066783951162435948353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13680044522634108290632235 20520066783951162435948353)
              ·
                refine ⟨15390050087963371826961265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20520066783951162435948353 15390050087963371826961265)
                ·
                  refine ⟨11542537565972528870220949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15390050087963371826961265 11542537565972528870220949)
                  ·
                    refine ⟨541056448404962290791607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11542537565972528870220949 541056448404962290791607)
                    ·
                      rfl

theorem cell23_3161111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_3161111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161111 prefixEnd_3161111 := by exact prefixLift 3161111
  have htrace : WordTrace (prefixWord ++ tailWord_3161111) baseStart_3161111 baseEnd_3161111 := by
    simpa [prefixWord, tailWord_3161111, baseEnd_3161111] using wordTrace_append hprefix tailTrace_3161111
  have hstable : (prefixWord ++ tailWord_3161111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161111).length < 2 ^ (prefixWord ++ tailWord_3161111).sum := by decide
  have hdescent : baseEnd_3161111 < baseStart_3161111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161186 : List Nat := [3, 3, 2, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_3161186 : Nat := 118140960795 + 3161186 * 2 ^ 59
def prefixEnd_3161186 : Nat := 4983230072969 + 3 ^ 40 * 3161186 * 2
def baseEnd_3161186 : Nat := 1623207856263974078936977

theorem tailTrace_3161186 : CollatzResearch.WordTrace tailWord_3161186 prefixEnd_3161186 1623207856263974078936977 := by
  unfold tailWord_3161186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28824481381392621107815853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76865283683713656287508941 28824481381392621107815853)
  ·
    refine ⟨10809180518022232915430945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28824481381392621107815853 10809180518022232915430945)
    ·
      refine ⟨8106885388516674686573209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10809180518022232915430945 8106885388516674686573209)
      ·
        refine ⟨6080164041387506014929907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8106885388516674686573209 6080164041387506014929907)
        ·
          refine ⟨9120246062081259022394861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080164041387506014929907 9120246062081259022394861)
          ·
            refine ⟨3420092273280472133398073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9120246062081259022394861 3420092273280472133398073)
            ·
              refine ⟨2565069204960354100048555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420092273280472133398073 2565069204960354100048555)
              ·
                refine ⟨3847603807440531150072833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565069204960354100048555 3847603807440531150072833)
                ·
                  refine ⟨2885702855580398362554625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847603807440531150072833 2885702855580398362554625)
                  ·
                    refine ⟨2164277141685298771915969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2885702855580398362554625 2164277141685298771915969)
                    ·
                      refine ⟨1623207856263974078936977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164277141685298771915969 1623207856263974078936977)
                      ·
                        rfl

theorem cell23_3161186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_3161186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161186 prefixEnd_3161186 := by exact prefixLift 3161186
  have htrace : WordTrace (prefixWord ++ tailWord_3161186) baseStart_3161186 baseEnd_3161186 := by
    simpa [prefixWord, tailWord_3161186, baseEnd_3161186] using wordTrace_append hprefix tailTrace_3161186
  have hstable : (prefixWord ++ tailWord_3161186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161186).length < 2 ^ (prefixWord ++ tailWord_3161186).sum := by decide
  have hdescent : baseEnd_3161186 < baseStart_3161186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161211 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 3]
def baseStart_3161211 : Nat := 118140960795 + 3161211 * 2 ^ 59
def prefixEnd_3161211 : Nat := 4983230072969 + 3 ^ 40 * 3161211 * 2
def baseEnd_3161211 : Nat := 1623220693280336481124361

theorem tailTrace_3161211 : CollatzResearch.WordTrace tailWord_3161211 prefixEnd_3161211 1623220693280336481124361 := by
  unfold tailWord_3161211
  simp only [CollatzResearch.WordTrace]
  refine ⟨115298837350479913700923487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76865891566986609133948991 115298837350479913700923487)
  ·
    refine ⟨172948256025719870551385231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115298837350479913700923487 172948256025719870551385231)
    ·
      refine ⟨259422384038579805827077847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172948256025719870551385231 259422384038579805827077847)
      ·
        refine ⟨389133576057869708740616771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259422384038579805827077847 389133576057869708740616771)
        ·
          refine ⟨583700364086804563110925157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389133576057869708740616771 583700364086804563110925157)
          ·
            refine ⟨109443818266275855583298467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 583700364086804563110925157 109443818266275855583298467)
            ·
              refine ⟨164165727399413783374947701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109443818266275855583298467 164165727399413783374947701)
              ·
                refine ⟨15390536943695042191401347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 164165727399413783374947701 15390536943695042191401347)
                ·
                  refine ⟨23085805415542563287102021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15390536943695042191401347 23085805415542563287102021)
                  ·
                    refine ⟨4328588515414230616331629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23085805415542563287102021 4328588515414230616331629)
                    ·
                      refine ⟨1623220693280336481124361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4328588515414230616331629 1623220693280336481124361)
                      ·
                        rfl

theorem cell23_3161211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 3].length) (baseStart_3161211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161211 prefixEnd_3161211 := by exact prefixLift 3161211
  have htrace : WordTrace (prefixWord ++ tailWord_3161211) baseStart_3161211 baseEnd_3161211 := by
    simpa [prefixWord, tailWord_3161211, baseEnd_3161211] using wordTrace_append hprefix tailTrace_3161211
  have hstable : (prefixWord ++ tailWord_3161211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161211).length < 2 ^ (prefixWord ++ tailWord_3161211).sum := by decide
  have hdescent : baseEnd_3161211 < baseStart_3161211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161241 : List Nat := [1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 3]
def baseStart_3161241 : Nat := 118140960795 + 3161241 * 2 ^ 59
def prefixEnd_3161241 : Nat := 4983230072969 + 3 ^ 40 * 3161241 * 2
def baseEnd_3161241 : Nat := 1623236097699971363749223

theorem tailTrace_3161241 : CollatzResearch.WordTrace tailWord_3161241 prefixEnd_3161241 1623236097699971363749223 := by
  unfold tailWord_3161241
  simp only [CollatzResearch.WordTrace]
  refine ⟨115299931540371228824515577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76866621026914152549677051 115299931540371228824515577)
  ·
    refine ⟨86474948655278421618386683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115299931540371228824515577 86474948655278421618386683)
    ·
      refine ⟨129712422982917632427580025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86474948655278421618386683 129712422982917632427580025)
      ·
        refine ⟨97284317237188224320685019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129712422982917632427580025 97284317237188224320685019)
        ·
          refine ⟨145926475855782336481027529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97284317237188224320685019 145926475855782336481027529)
          ·
            refine ⟨109444856891836752360770647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145926475855782336481027529 109444856891836752360770647)
            ·
              refine ⟨164167285337755128541155971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109444856891836752360770647 164167285337755128541155971)
              ·
                refine ⟨246250928006632692811733957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164167285337755128541155971 246250928006632692811733957)
                ·
                  refine ⟨46172049001243629902200117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246250928006632692811733957 46172049001243629902200117)
                  ·
                    refine ⟨4328629593866590303331261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46172049001243629902200117 4328629593866590303331261)
                    ·
                      refine ⟨1623236097699971363749223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4328629593866590303331261 1623236097699971363749223)
                      ·
                        rfl

theorem cell23_3161241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 5, 3].length) (baseStart_3161241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161241 prefixEnd_3161241 := by exact prefixLift 3161241
  have htrace : WordTrace (prefixWord ++ tailWord_3161241) baseStart_3161241 baseEnd_3161241 := by
    simpa [prefixWord, tailWord_3161241, baseEnd_3161241] using wordTrace_append hprefix tailTrace_3161241
  have hstable : (prefixWord ++ tailWord_3161241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161241).length < 2 ^ (prefixWord ++ tailWord_3161241).sum := by decide
  have hdescent : baseEnd_3161241 < baseStart_3161241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161282 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 8]
def baseStart_3161282 : Nat := 118140960795 + 3161282 * 2 ^ 59
def prefixEnd_3161282 : Nat := 4983230072969 + 3 ^ 40 * 3161282 * 2
def baseEnd_3161282 : Nat := 180361905600756189259615

theorem tailTrace_3161282 : CollatzResearch.WordTrace tailWord_3161282 prefixEnd_3161282 180361905600756189259615 := by
  unfold tailWord_3161282
  simp only [CollatzResearch.WordTrace]
  refine ⟨28825356733305673206689525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76867617955481795217838733 28825356733305673206689525)
  ·
    refine ⟨2702377193747406863127143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28825356733305673206689525 2702377193747406863127143)
    ·
      refine ⟨4053565790621110294690715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2702377193747406863127143 4053565790621110294690715)
      ·
        refine ⟨6080348685931665442036073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4053565790621110294690715 6080348685931665442036073)
        ·
          refine ⟨4560261514448749081527055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080348685931665442036073 4560261514448749081527055)
          ·
            refine ⟨6840392271673123622290583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560261514448749081527055 6840392271673123622290583)
            ·
              refine ⟨10260588407509685433435875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6840392271673123622290583 10260588407509685433435875)
              ·
                refine ⟨15390882611264528150153813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10260588407509685433435875 15390882611264528150153813)
                ·
                  refine ⟨180361905600756189259615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15390882611264528150153813 180361905600756189259615)
                  ·
                    rfl

theorem cell23_3161282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_3161282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161282 prefixEnd_3161282 := by exact prefixLift 3161282
  have htrace : WordTrace (prefixWord ++ tailWord_3161282) baseStart_3161282 baseEnd_3161282 := by
    simpa [prefixWord, tailWord_3161282, baseEnd_3161282] using wordTrace_append hprefix tailTrace_3161282
  have hstable : (prefixWord ++ tailWord_3161282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161282).length < 2 ^ (prefixWord ++ tailWord_3161282).sum := by decide
  have hdescent : baseEnd_3161282 < baseStart_3161282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161286 : List Nat := [6, 1, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_3161286 : Nat := 118140960795 + 3161286 * 2 ^ 59
def prefixEnd_3161286 : Nat := 4983230072969 + 3 ^ 40 * 3161286 * 2
def baseEnd_3161286 : Nat := 541086401443141229228839

theorem tailTrace_3161286 : CollatzResearch.WordTrace tailWord_3161286 prefixEnd_3161286 541086401443141229228839 := by
  unfold tailWord_3161286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603174150787756297184491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 76867715216805467673269141 3603174150787756297184491)
  ·
    refine ⟨5404761226181634445776737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3603174150787756297184491 5404761226181634445776737)
    ·
      refine ⟨4053570919636225834332553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5404761226181634445776737 4053570919636225834332553)
      ·
        refine ⟨3040178189727169375749415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4053570919636225834332553 3040178189727169375749415)
        ·
          refine ⟨4560267284590754063624123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3040178189727169375749415 4560267284590754063624123)
          ·
            refine ⟨6840400926886131095436185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560267284590754063624123 6840400926886131095436185)
            ·
              refine ⟨5130300695164598321577139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6840400926886131095436185 5130300695164598321577139)
              ·
                refine ⟨7695451042746897482365709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130300695164598321577139 7695451042746897482365709)
                ·
                  refine ⟨2885794141030086555887141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7695451042746897482365709 2885794141030086555887141)
                  ·
                    refine ⟨541086401443141229228839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2885794141030086555887141 541086401443141229228839)
                    ·
                      rfl

theorem cell23_3161286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_3161286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161286 prefixEnd_3161286 := by exact prefixLift 3161286
  have htrace : WordTrace (prefixWord ++ tailWord_3161286) baseStart_3161286 baseEnd_3161286 := by
    simpa [prefixWord, tailWord_3161286, baseEnd_3161286] using wordTrace_append hprefix tailTrace_3161286
  have hstable : (prefixWord ++ tailWord_3161286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161286).length < 2 ^ (prefixWord ++ tailWord_3161286).sum := by decide
  have hdescent : baseEnd_3161286 < baseStart_3161286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161325 : List Nat := [1, 5, 1, 2, 2, 1, 1, 2, 4, 4]
def baseStart_3161325 : Nat := 118140960795 + 3161325 * 2 ^ 59
def prefixEnd_3161325 : Nat := 4983230072969 + 3 ^ 40 * 3161325 * 2
def baseEnd_3161325 : Nat := 541093076691649678366279

theorem tailTrace_3161325 : CollatzResearch.WordTrace tailWord_3161325 prefixEnd_3161325 541093076691649678366279 := by
  unfold tailWord_3161325
  simp only [CollatzResearch.WordTrace]
  refine ⟨115302995272066911170573429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76868663514711274113715619 115302995272066911170573429)
  ·
    refine ⟨10809655806756272922241259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115302995272066911170573429 10809655806756272922241259)
    ·
      refine ⟨16214483710134409383361889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10809655806756272922241259 16214483710134409383361889)
      ·
        refine ⟨12160862782600807037521417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16214483710134409383361889 12160862782600807037521417)
        ·
          refine ⟨9120647086950605278141063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12160862782600807037521417 9120647086950605278141063)
          ·
            refine ⟨13680970630425907917211595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9120647086950605278141063 13680970630425907917211595)
            ·
              refine ⟨20521455945638861875817393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13680970630425907917211595 20521455945638861875817393)
              ·
                refine ⟨15391091959229146406863045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20521455945638861875817393 15391091959229146406863045)
                ·
                  refine ⟨2885829742355464951286821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15391091959229146406863045 2885829742355464951286821)
                  ·
                    refine ⟨541093076691649678366279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2885829742355464951286821 541093076691649678366279)
                    ·
                      rfl

theorem cell23_3161325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_3161325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161325 prefixEnd_3161325 := by exact prefixLift 3161325
  have htrace : WordTrace (prefixWord ++ tailWord_3161325) baseStart_3161325 baseEnd_3161325 := by
    simpa [prefixWord, tailWord_3161325, baseEnd_3161325] using wordTrace_append hprefix tailTrace_3161325
  have hstable : (prefixWord ++ tailWord_3161325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161325).length < 2 ^ (prefixWord ++ tailWord_3161325).sum := by decide
  have hdescent : baseEnd_3161325 < baseStart_3161325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161371 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_3161371 : Nat := 118140960795 + 3161371 * 2 ^ 59
def prefixEnd_3161371 : Nat := 4983230072969 + 3 ^ 40 * 3161371 * 2
def baseEnd_3161371 : Nat := 1623302850185055855123625

theorem tailTrace_3161371 : CollatzResearch.WordTrace tailWord_3161371 prefixEnd_3161371 1623302850185055855123625 := by
  unfold tailWord_3161371
  simp only [CollatzResearch.WordTrace]
  refine ⟨115304673029900261026747967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76869782019933507351165311 115304673029900261026747967)
  ·
    refine ⟨172957009544850391540121951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115304673029900261026747967 172957009544850391540121951)
    ·
      refine ⟨259435514317275587310182927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172957009544850391540121951 259435514317275587310182927)
      ·
        refine ⟨389153271475913380965274391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259435514317275587310182927 389153271475913380965274391)
        ·
          refine ⟨583729907213870071447911587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389153271475913380965274391 583729907213870071447911587)
          ·
            refine ⟨875594860820805107171867381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583729907213870071447911587 875594860820805107171867381)
            ·
              refine ⟨82087018201950478797362567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 875594860820805107171867381 82087018201950478797362567)
              ·
                refine ⟨123130527302925718196043851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82087018201950478797362567 123130527302925718196043851)
                ·
                  refine ⟨184695790954388577294065777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 123130527302925718196043851 184695790954388577294065777)
                  ·
                    refine ⟨138521843215791432970549333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184695790954388577294065777 138521843215791432970549333)
                    ·
                      refine ⟨1623302850185055855123625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138521843215791432970549333 1623302850185055855123625)
                      ·
                        rfl

theorem cell23_3161371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_3161371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161371 prefixEnd_3161371 := by exact prefixLift 3161371
  have htrace : WordTrace (prefixWord ++ tailWord_3161371) baseStart_3161371 baseEnd_3161371 := by
    simpa [prefixWord, tailWord_3161371, baseEnd_3161371] using wordTrace_append hprefix tailTrace_3161371
  have hstable : (prefixWord ++ tailWord_3161371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161371).length < 2 ^ (prefixWord ++ tailWord_3161371).sum := by decide
  have hdescent : baseEnd_3161371 < baseStart_3161371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161408 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3]
def baseStart_3161408 : Nat := 118140960795 + 3161408 * 2 ^ 59
def prefixEnd_3161408 : Nat := 4983230072969 + 3 ^ 40 * 3161408 * 2
def baseEnd_3161408 : Nat := 1623321848969272210360955

theorem tailTrace_3161408 : CollatzResearch.WordTrace tailWord_3161408 prefixEnd_3161408 1623321848969272210360955 := by
  unfold tailWord_3161408
  simp only [CollatzResearch.WordTrace]
  refine ⟨57653011265383108172922439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76870681687177477563896585 57653011265383108172922439)
  ·
    refine ⟨86479516898074662259383659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57653011265383108172922439 86479516898074662259383659)
    ·
      refine ⟨129719275347111993389075489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86479516898074662259383659 129719275347111993389075489)
      ·
        refine ⟨97289456510333995041806617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129719275347111993389075489 97289456510333995041806617)
        ·
          refine ⟨72967092382750496281354963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97289456510333995041806617 72967092382750496281354963)
          ·
            refine ⟨109450638574125744422032445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72967092382750496281354963 109450638574125744422032445)
            ·
              refine ⟨41043989465297154158262167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109450638574125744422032445 41043989465297154158262167)
              ·
                refine ⟨61565984197945731237393251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41043989465297154158262167 61565984197945731237393251)
                ·
                  refine ⟨92348976296918596856089877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61565984197945731237393251 92348976296918596856089877)
                  ·
                    refine ⟨4328858263918059227629213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92348976296918596856089877 4328858263918059227629213)
                    ·
                      refine ⟨1623321848969272210360955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4328858263918059227629213 1623321848969272210360955)
                      ·
                        rfl

theorem cell23_3161408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 3].length) (baseStart_3161408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161408 prefixEnd_3161408 := by exact prefixLift 3161408
  have htrace : WordTrace (prefixWord ++ tailWord_3161408) baseStart_3161408 baseEnd_3161408 := by
    simpa [prefixWord, tailWord_3161408, baseEnd_3161408] using wordTrace_append hprefix tailTrace_3161408
  have hstable : (prefixWord ++ tailWord_3161408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161408).length < 2 ^ (prefixWord ++ tailWord_3161408).sum := by decide
  have hdescent : baseEnd_3161408 < baseStart_3161408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161422 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_3161422 : Nat := 118140960795 + 3161422 * 2 ^ 59
def prefixEnd_3161422 : Nat := 4983230072969 + 3 ^ 40 * 3161422 * 2
def baseEnd_3161422 : Nat := 1623329037698435155585891

theorem tailTrace_3161422 : CollatzResearch.WordTrace tailWord_3161422 prefixEnd_3161422 1623329037698435155585891 := by
  unfold tailWord_3161422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413316644089437092106815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76871022101810331157903013 14413316644089437092106815)
  ·
    refine ⟨21619974966134155638160223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14413316644089437092106815 21619974966134155638160223)
    ·
      refine ⟨32429962449201233457240335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21619974966134155638160223 32429962449201233457240335)
      ·
        refine ⟨48644943673801850185860503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32429962449201233457240335 48644943673801850185860503)
        ·
          refine ⟨72967415510702775278790755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48644943673801850185860503 72967415510702775278790755)
          ·
            refine ⟨109451123266054162918186133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72967415510702775278790755 109451123266054162918186133)
            ·
              refine ⟨5130521403096288886789975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109451123266054162918186133 5130521403096288886789975)
              ·
                refine ⟨7695782104644433330184963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5130521403096288886789975 7695782104644433330184963)
                ·
                  refine ⟨11543673156966649995277445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7695782104644433330184963 11543673156966649995277445)
                  ·
                    refine ⟨2164438716931246874114521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11543673156966649995277445 2164438716931246874114521)
                    ·
                      refine ⟨1623329037698435155585891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164438716931246874114521 1623329037698435155585891)
                      ·
                        rfl

theorem cell23_3161422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_3161422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161422 prefixEnd_3161422 := by exact prefixLift 3161422
  have htrace : WordTrace (prefixWord ++ tailWord_3161422) baseStart_3161422 baseEnd_3161422 := by
    simpa [prefixWord, tailWord_3161422, baseEnd_3161422] using wordTrace_append hprefix tailTrace_3161422
  have hstable : (prefixWord ++ tailWord_3161422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161422).length < 2 ^ (prefixWord ++ tailWord_3161422).sum := by decide
  have hdescent : baseEnd_3161422 < baseStart_3161422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161465 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 1, 7, 2]
def baseStart_3161465 : Nat := 118140960795 + 3161465 * 2 ^ 59
def prefixEnd_3161465 : Nat := 4983230072969 + 3 ^ 40 * 3161465 * 2
def baseEnd_3161465 : Nat := 1623351117366578487348193

theorem tailTrace_3161465 : CollatzResearch.WordTrace tailWord_3161465 prefixEnd_3161465 1623351117366578487348193 := by
  unfold tailWord_3161465
  simp only [CollatzResearch.WordTrace]
  refine ⟨115308101491559715080669849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76872067661039810053779899 115308101491559715080669849)
  ·
    refine ⟨86481076118669786310502387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115308101491559715080669849 86481076118669786310502387)
    ·
      refine ⟨129721614178004679465753581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86481076118669786310502387 129721614178004679465753581)
      ·
        refine ⟨48645605316751754799657593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129721614178004679465753581 48645605316751754799657593)
        ·
          refine ⟨36484203987563816099743195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48645605316751754799657593 36484203987563816099743195)
          ·
            refine ⟨54726305981345724149614793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36484203987563816099743195 54726305981345724149614793)
            ·
              refine ⟨41044729486009293112211095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54726305981345724149614793 41044729486009293112211095)
              ·
                refine ⟨61567094229013939668316643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41044729486009293112211095 61567094229013939668316643)
                ·
                  refine ⟨92350641343520909502474965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61567094229013939668316643 92350641343520909502474965)
                  ·
                    refine ⟨2164468156488771316464257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 92350641343520909502474965 2164468156488771316464257)
                    ·
                      refine ⟨1623351117366578487348193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164468156488771316464257 1623351117366578487348193)
                      ·
                        rfl

theorem cell23_3161465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 7, 2].length) (baseStart_3161465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161465 prefixEnd_3161465 := by exact prefixLift 3161465
  have htrace : WordTrace (prefixWord ++ tailWord_3161465) baseStart_3161465 baseEnd_3161465 := by
    simpa [prefixWord, tailWord_3161465, baseEnd_3161465] using wordTrace_append hprefix tailTrace_3161465
  have hstable : (prefixWord ++ tailWord_3161465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161465).length < 2 ^ (prefixWord ++ tailWord_3161465).sum := by decide
  have hdescent : baseEnd_3161465 < baseStart_3161465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161468 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3161468 : Nat := 118140960795 + 3161468 * 2 ^ 59
def prefixEnd_3161468 : Nat := 4983230072969 + 3 ^ 40 * 3161468 * 2
def baseEnd_3161468 : Nat := 1623352657808541975610679

theorem tailTrace_3161468 : CollatzResearch.WordTrace tailWord_3161468 prefixEnd_3161468 1623352657808541975610679 := by
  unfold tailWord_3161468
  simp only [CollatzResearch.WordTrace]
  refine ⟨57654105455274423296514529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76872140607032564395352705 57654105455274423296514529)
  ·
    refine ⟨43240579091455817472385897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57654105455274423296514529 43240579091455817472385897)
    ·
      refine ⟨32430434318591863104289423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43240579091455817472385897 32430434318591863104289423)
      ·
        refine ⟨48645651477887794656434135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32430434318591863104289423 48645651477887794656434135)
        ·
          refine ⟨72968477216831691984651203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48645651477887794656434135 72968477216831691984651203)
          ·
            refine ⟨109452715825247537976976805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72968477216831691984651203 109452715825247537976976805)
            ·
              refine ⟨20522384217233913370683151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109452715825247537976976805 20522384217233913370683151)
              ·
                refine ⟨30783576325850870056024727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20522384217233913370683151 30783576325850870056024727)
                ·
                  refine ⟨46175364488776305084037091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30783576325850870056024727 46175364488776305084037091)
                  ·
                    refine ⟨69263046733164457626055637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46175364488776305084037091 69263046733164457626055637)
                    ·
                      refine ⟨1623352657808541975610679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69263046733164457626055637 1623352657808541975610679)
                      ·
                        rfl

theorem cell23_3161468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3161468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161468 prefixEnd_3161468 := by exact prefixLift 3161468
  have htrace : WordTrace (prefixWord ++ tailWord_3161468) baseStart_3161468 baseEnd_3161468 := by
    simpa [prefixWord, tailWord_3161468, baseEnd_3161468] using wordTrace_append hprefix tailTrace_3161468
  have hstable : (prefixWord ++ tailWord_3161468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161468).length < 2 ^ (prefixWord ++ tailWord_3161468).sum := by decide
  have hdescent : baseEnd_3161468 < baseStart_3161468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161473 : List Nat := [1, 2, 4, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_3161473 : Nat := 118140960795 + 3161473 * 2 ^ 59
def prefixEnd_3161473 : Nat := 4983230072969 + 3 ^ 40 * 3161473 * 2
def baseEnd_3161473 : Nat := 1623355225211814456048157

theorem tailTrace_3161473 : CollatzResearch.WordTrace tailWord_3161473 prefixEnd_3161473 1623355225211814456048157 := by
  unfold tailWord_3161473
  simp only [CollatzResearch.WordTrace]
  refine ⟨115308393275530732446961073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76872262183687154964640715 115308393275530732446961073)
  ·
    refine ⟨86481294956648049335220805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115308393275530732446961073 86481294956648049335220805)
    ·
      refine ⟨16215242804371509250353901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86481294956648049335220805 16215242804371509250353901)
      ·
        refine ⟨6080716051639315968882713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16215242804371509250353901 6080716051639315968882713)
        ·
          refine ⟨4560537038729486976662035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6080716051639315968882713 4560537038729486976662035)
          ·
            refine ⟨6840805558094230464993053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4560537038729486976662035 6840805558094230464993053)
            ·
              refine ⟨2565302084285336424372395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6840805558094230464993053 2565302084285336424372395)
              ·
                refine ⟨3847953126428004636558593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565302084285336424372395 3847953126428004636558593)
                ·
                  refine ⟨2885964844821003477418945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3847953126428004636558593 2885964844821003477418945)
                  ·
                    refine ⟨2164473633615752608064209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2885964844821003477418945 2164473633615752608064209)
                    ·
                      refine ⟨1623355225211814456048157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164473633615752608064209 1623355225211814456048157)
                      ·
                        rfl

theorem cell23_3161473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_3161473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161473 prefixEnd_3161473 := by exact prefixLift 3161473
  have htrace : WordTrace (prefixWord ++ tailWord_3161473) baseStart_3161473 baseEnd_3161473 := by
    simpa [prefixWord, tailWord_3161473, baseEnd_3161473] using wordTrace_append hprefix tailTrace_3161473
  have hstable : (prefixWord ++ tailWord_3161473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161473).length < 2 ^ (prefixWord ++ tailWord_3161473).sum := by decide
  have hdescent : baseEnd_3161473 < baseStart_3161473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161495 : List Nat := [1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_3161495 : Nat := 118140960795 + 3161495 * 2 ^ 59
def prefixEnd_3161495 : Nat := 4983230072969 + 3 ^ 40 * 3161495 * 2
def baseEnd_3161495 : Nat := 1623366521786213369973055

theorem tailTrace_3161495 : CollatzResearch.WordTrace tailWord_3161495 prefixEnd_3161495 1623366521786213369973055 := by
  unfold tailWord_3161495
  simp only [CollatzResearch.WordTrace]
  refine ⟨115309195681451030204261939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76872797120967353469507959 115309195681451030204261939)
  ·
    refine ⟨172963793522176545306392909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115309195681451030204261939 172963793522176545306392909)
    ·
      refine ⟨64861422570816204489897341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172963793522176545306392909 64861422570816204489897341)
      ·
        refine ⟨24323033464056076683711503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64861422570816204489897341 24323033464056076683711503)
        ·
          refine ⟨36484550196084115025567255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24323033464056076683711503 36484550196084115025567255)
          ·
            refine ⟨54726825294126172538350883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36484550196084115025567255 54726825294126172538350883)
            ·
              refine ⟨82090237941189258807526325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54726825294126172538350883 82090237941189258807526325)
              ·
                refine ⟨7695959806986493013205593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82090237941189258807526325 7695959806986493013205593)
                ·
                  refine ⟨5771969855239869759904195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7695959806986493013205593 5771969855239869759904195)
                  ·
                    refine ⟨8657954782859804639856293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5771969855239869759904195 8657954782859804639856293)
                    ·
                      refine ⟨1623366521786213369973055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8657954782859804639856293 1623366521786213369973055)
                      ·
                        rfl

theorem cell23_3161495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_3161495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161495 prefixEnd_3161495 := by exact prefixLift 3161495
  have htrace : WordTrace (prefixWord ++ tailWord_3161495) baseStart_3161495 baseEnd_3161495 := by
    simpa [prefixWord, tailWord_3161495, baseEnd_3161495] using wordTrace_append hprefix tailTrace_3161495
  have hstable : (prefixWord ++ tailWord_3161495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161495).length < 2 ^ (prefixWord ++ tailWord_3161495).sum := by decide
  have hdescent : baseEnd_3161495 < baseStart_3161495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161496 : List Nat := [2, 1, 2, 5, 3, 1, 1, 3, 5]
def baseStart_3161496 : Nat := 118140960795 + 3161496 * 2 ^ 59
def prefixEnd_3161496 : Nat := 4983230072969 + 3 ^ 40 * 3161496 * 2
def baseEnd_3161496 : Nat := 180374115029651985117839

theorem tailTrace_3161496 : CollatzResearch.WordTrace tailWord_3161496 prefixEnd_3161496 180374115029651985117839 := by
  unfold tailWord_3161496
  simp only [CollatzResearch.WordTrace]
  refine ⟨57654616077223703687524171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76872821436298271583365561 57654616077223703687524171)
  ·
    refine ⟨86481924115835555531286257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57654616077223703687524171 86481924115835555531286257)
    ·
      refine ⟨64861443086876666648464693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86481924115835555531286257 64861443086876666648464693)
      ·
        refine ⟨6080760289394687498293565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64861443086876666648464693 6080760289394687498293565)
        ·
          refine ⟨2280285108523007811860087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6080760289394687498293565 2280285108523007811860087)
          ·
            refine ⟨3420427662784511717790131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280285108523007811860087 3420427662784511717790131)
            ·
              refine ⟨5130641494176767576685197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3420427662784511717790131 5130641494176767576685197)
              ·
                refine ⟨1923990560316287841256949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5130641494176767576685197 1923990560316287841256949)
                ·
                  refine ⟨180374115029651985117839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923990560316287841256949 180374115029651985117839)
                  ·
                    rfl

theorem cell23_3161496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 3, 5].length) (baseStart_3161496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161496 prefixEnd_3161496 := by exact prefixLift 3161496
  have htrace : WordTrace (prefixWord ++ tailWord_3161496) baseStart_3161496 baseEnd_3161496 := by
    simpa [prefixWord, tailWord_3161496, baseEnd_3161496] using wordTrace_append hprefix tailTrace_3161496
  have hstable : (prefixWord ++ tailWord_3161496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161496).length < 2 ^ (prefixWord ++ tailWord_3161496).sum := by decide
  have hdescent : baseEnd_3161496 < baseStart_3161496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161573 : List Nat := [1, 3, 1, 5, 1, 3, 2, 2, 1, 4]
def baseStart_3161573 : Nat := 118140960795 + 3161573 * 2 ^ 59
def prefixEnd_3161573 : Nat := 4983230072969 + 3 ^ 40 * 3161573 * 2
def baseEnd_3161573 : Nat := 541135524425754688265899

theorem tailTrace_3161573 : CollatzResearch.WordTrace tailWord_3161573 prefixEnd_3161573 541135524425754688265899 := by
  unfold tailWord_3161573
  simp only [CollatzResearch.WordTrace]
  refine ⟨115312040575168449525601373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76874693716778966350400915 115312040575168449525601373)
  ·
    refine ⟨43242015215688168572100515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115312040575168449525601373 43242015215688168572100515)
    ·
      refine ⟨64863022823532252858150773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43242015215688168572100515 64863022823532252858150773)
      ·
        refine ⟨6080908389706148705451635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64863022823532252858150773 6080908389706148705451635)
        ·
          refine ⟨9121362584559223058177453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6080908389706148705451635 9121362584559223058177453)
          ·
            refine ⟨3420510969209708646816545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9121362584559223058177453 3420510969209708646816545)
            ·
              refine ⟨2565383226907281485112409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3420510969209708646816545 2565383226907281485112409)
              ·
                refine ⟨1924037420180461113834307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565383226907281485112409 1924037420180461113834307)
                ·
                  refine ⟨2886056130270691670751461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924037420180461113834307 2886056130270691670751461)
                  ·
                    refine ⟨541135524425754688265899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886056130270691670751461 541135524425754688265899)
                    ·
                      rfl

theorem cell23_3161573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 2, 1, 4].length) (baseStart_3161573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161573 prefixEnd_3161573 := by exact prefixLift 3161573
  have htrace : WordTrace (prefixWord ++ tailWord_3161573) baseStart_3161573 baseEnd_3161573 := by
    simpa [prefixWord, tailWord_3161573, baseEnd_3161573] using wordTrace_append hprefix tailTrace_3161573
  have hstable : (prefixWord ++ tailWord_3161573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161573).length < 2 ^ (prefixWord ++ tailWord_3161573).sum := by decide
  have hdescent : baseEnd_3161573 < baseStart_3161573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161619 : List Nat := [1, 1, 1, 2, 1, 6, 4, 1, 1, 1, 4]
def baseStart_3161619 : Nat := 118140960795 + 3161619 * 2 ^ 59
def prefixEnd_3161619 : Nat := 4983230072969 + 3 ^ 40 * 3161619 * 2
def baseEnd_3161619 : Nat := 1623430193387370884822485

theorem tailTrace_3161619 : CollatzResearch.WordTrace tailWord_3161619 prefixEnd_3161619 1623430193387370884822485 := by
  unfold tailWord_3161619
  simp only [CollatzResearch.WordTrace]
  refine ⟨115313718333001799381775911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76875812222001199587850607 115313718333001799381775911)
  ·
    refine ⟨172970577499502699072663867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115313718333001799381775911 172970577499502699072663867)
    ·
      refine ⟨259455866249254048608995801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172970577499502699072663867 259455866249254048608995801)
      ·
        refine ⟨194591899686940536456746851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259455866249254048608995801 194591899686940536456746851)
        ·
          refine ⟨291887849530410804685120277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194591899686940536456746851 291887849530410804685120277)
          ·
            refine ⟨13682242946738006469615013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 291887849530410804685120277 13682242946738006469615013)
            ·
              refine ⟨2565420552513376213052815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13682242946738006469615013 2565420552513376213052815)
              ·
                refine ⟨3848130828770064319579223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565420552513376213052815 3848130828770064319579223)
                ·
                  refine ⟨5772196243155096479368835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848130828770064319579223 5772196243155096479368835)
                  ·
                    refine ⟨8658294364732644719053253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5772196243155096479368835 8658294364732644719053253)
                    ·
                      refine ⟨1623430193387370884822485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8658294364732644719053253 1623430193387370884822485)
                      ·
                        rfl

theorem cell23_3161619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 1, 1, 1, 4].length) (baseStart_3161619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161619 prefixEnd_3161619 := by exact prefixLift 3161619
  have htrace : WordTrace (prefixWord ++ tailWord_3161619) baseStart_3161619 baseEnd_3161619 := by
    simpa [prefixWord, tailWord_3161619, baseEnd_3161619] using wordTrace_append hprefix tailTrace_3161619
  have hstable : (prefixWord ++ tailWord_3161619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161619).length < 2 ^ (prefixWord ++ tailWord_3161619).sum := by decide
  have hdescent : baseEnd_3161619 < baseStart_3161619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161675 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4]
def baseStart_3161675 : Nat := 118140960795 + 3161675 * 2 ^ 59
def prefixEnd_3161675 : Nat := 4983230072969 + 3 ^ 40 * 3161675 * 2
def baseEnd_3161675 : Nat := 1623458948304022665722227

theorem tailTrace_3161675 : CollatzResearch.WordTrace tailWord_3161675 prefixEnd_3161675 1623458948304022665722227 := by
  unfold tailWord_3161675
  simp only [CollatzResearch.WordTrace]
  refine ⟨115315760820798920945814479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76877173880532613963876319 115315760820798920945814479)
  ·
    refine ⟨172973641231198381418721719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115315760820798920945814479 172973641231198381418721719)
    ·
      refine ⟨259460461846797572128082579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172973641231198381418721719 259460461846797572128082579)
      ·
        refine ⟨389190692770196358192123869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259460461846797572128082579 389190692770196358192123869)
        ·
          refine ⟨145946509788823634322046451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389190692770196358192123869 145946509788823634322046451)
          ·
            refine ⟨218919764683235451483069677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145946509788823634322046451 218919764683235451483069677)
            ·
              refine ⟨82094911756213294306151129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218919764683235451483069677 82094911756213294306151129)
              ·
                refine ⟨61571183817159970729613347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82094911756213294306151129 61571183817159970729613347)
                ·
                  refine ⟨92356775725739956094420021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61571183817159970729613347 92356775725739956094420021)
                  ·
                    refine ⟨8658447724288120883851877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 92356775725739956094420021 8658447724288120883851877)
                    ·
                      refine ⟨1623458948304022665722227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8658447724288120883851877 1623458948304022665722227)
                      ·
                        rfl

theorem cell23_3161675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_3161675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161675 prefixEnd_3161675 := by exact prefixLift 3161675
  have htrace : WordTrace (prefixWord ++ tailWord_3161675) baseStart_3161675 baseEnd_3161675 := by
    simpa [prefixWord, tailWord_3161675, baseEnd_3161675] using wordTrace_append hprefix tailTrace_3161675
  have hstable : (prefixWord ++ tailWord_3161675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161675).length < 2 ^ (prefixWord ++ tailWord_3161675).sum := by decide
  have hdescent : baseEnd_3161675 < baseStart_3161675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161712 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_3161712 : Nat := 118140960795 + 3161712 * 2 ^ 59
def prefixEnd_3161712 : Nat := 4983230072969 + 3 ^ 40 * 3161712 * 2
def baseEnd_3161712 : Nat := 1623477947088239020959557

theorem tailTrace_3161712 : CollatzResearch.WordTrace tailWord_3161712 prefixEnd_3161712 1623477947088239020959557 := by
  unfold tailWord_3161712
  simp only [CollatzResearch.WordTrace]
  refine ⟨57658555160832438132455695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76878073547776584176607593 57658555160832438132455695)
  ·
    refine ⟨86487832741248657198683543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57658555160832438132455695 86487832741248657198683543)
    ·
      refine ⟨129731749111872985798025315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86487832741248657198683543 129731749111872985798025315)
      ·
        refine ⟨194597623667809478697037973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129731749111872985798025315 194597623667809478697037973)
        ·
          refine ⟨9121763609428569313923655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 194597623667809478697037973 9121763609428569313923655)
          ·
            refine ⟨13682645414142853970885483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9121763609428569313923655 13682645414142853970885483)
            ·
              refine ⟨20523968121214280956328225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13682645414142853970885483 20523968121214280956328225)
              ·
                refine ⟨15392976090910710717246169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20523968121214280956328225 15392976090910710717246169)
                ·
                  refine ⟨11544732068183033037934627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15392976090910710717246169 11544732068183033037934627)
                  ·
                    refine ⟨17317098102274549556901941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11544732068183033037934627 17317098102274549556901941)
                    ·
                      refine ⟨1623477947088239020959557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17317098102274549556901941 1623477947088239020959557)
                      ·
                        rfl

theorem cell23_3161712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_3161712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161712 prefixEnd_3161712 := by exact prefixLift 3161712
  have htrace : WordTrace (prefixWord ++ tailWord_3161712) baseStart_3161712 baseEnd_3161712 := by
    simpa [prefixWord, tailWord_3161712, baseEnd_3161712] using wordTrace_append hprefix tailTrace_3161712
  have hstable : (prefixWord ++ tailWord_3161712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161712).length < 2 ^ (prefixWord ++ tailWord_3161712).sum := by decide
  have hdescent : baseEnd_3161712 < baseStart_3161712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161799 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 4, 4, 2]
def baseStart_3161799 : Nat := 118140960795 + 3161799 * 2 ^ 59
def prefixEnd_3161799 : Nat := 4983230072969 + 3 ^ 40 * 3161799 * 2
def baseEnd_3161799 : Nat := 1623522619905180180571657

theorem tailTrace_3161799 : CollatzResearch.WordTrace tailWord_3161799 prefixEnd_3161799 1623522619905180180571657 := by
  unfold tailWord_3161799
  simp only [CollatzResearch.WordTrace]
  refine ⟨115320283472349690123328451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76880188981566460082218967 115320283472349690123328451)
  ·
    refine ⟨172980425208524535184992677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115320283472349690123328451 172980425208524535184992677)
    ·
      refine ⟨32433829726598350347186127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172980425208524535184992677 32433829726598350347186127)
      ·
        refine ⟨48650744589897525520779191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32433829726598350347186127 48650744589897525520779191)
        ·
          refine ⟨72976116884846288281168787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48650744589897525520779191 72976116884846288281168787)
          ·
            refine ⟨109464175327269432421753181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72976116884846288281168787 109464175327269432421753181)
            ·
              refine ⟨41049065747726037158157443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109464175327269432421753181 41049065747726037158157443)
              ·
                refine ⟨61573598621589055737236165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41049065747726037158157443 61573598621589055737236165)
                ·
                  refine ⟨11545049741547947950731781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61573598621589055737236165 11545049741547947950731781)
                  ·
                    refine ⟨2164696826540240240762209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11545049741547947950731781 2164696826540240240762209)
                    ·
                      refine ⟨1623522619905180180571657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164696826540240240762209 1623522619905180180571657)
                      ·
                        rfl

theorem cell23_3161799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 4, 4, 2].length) (baseStart_3161799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161799 prefixEnd_3161799 := by exact prefixLift 3161799
  have htrace : WordTrace (prefixWord ++ tailWord_3161799) baseStart_3161799 baseEnd_3161799 := by
    simpa [prefixWord, tailWord_3161799, baseEnd_3161799] using wordTrace_append hprefix tailTrace_3161799
  have hstable : (prefixWord ++ tailWord_3161799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161799).length < 2 ^ (prefixWord ++ tailWord_3161799).sum := by decide
  have hdescent : baseEnd_3161799 < baseStart_3161799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161809 : List Nat := [1, 2, 2, 1, 2, 4, 1, 3, 3, 4]
def baseStart_3161809 : Nat := 118140960795 + 3161809 * 2 ^ 59
def prefixEnd_3161809 : Nat := 4983230072969 + 3 ^ 40 * 3161809 * 2
def baseEnd_3161809 : Nat := 541175918237241713815537

theorem tailTrace_3161809 : CollatzResearch.WordTrace tailWord_3161809 prefixEnd_3161809 541175918237241713815537 := by
  unfold tailWord_3161809
  simp only [CollatzResearch.WordTrace]
  refine ⟨115320648202313461831192481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76880432134875641220794987 115320648202313461831192481)
  ·
    refine ⟨86490486151735096373394361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115320648202313461831192481 86490486151735096373394361)
    ·
      refine ⟨64867864613801322280045771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86490486151735096373394361 64867864613801322280045771)
      ·
        refine ⟨97301796920701983420068657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64867864613801322280045771 97301796920701983420068657)
        ·
          refine ⟨72976347690526487565051493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97301796920701983420068657 72976347690526487565051493)
          ·
            refine ⟨13683065191973716418447155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72976347690526487565051493 13683065191973716418447155)
            ·
              refine ⟨20524597787960574627670733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13683065191973716418447155 20524597787960574627670733)
              ·
                refine ⟨7696724170485215485376525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20524597787960574627670733 7696724170485215485376525)
                ·
                  refine ⟨2886271563931955807016197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7696724170485215485376525 2886271563931955807016197)
                  ·
                    refine ⟨541175918237241713815537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886271563931955807016197 541175918237241713815537)
                    ·
                      rfl

theorem cell23_3161809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 4].length) (baseStart_3161809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161809 prefixEnd_3161809 := by exact prefixLift 3161809
  have htrace : WordTrace (prefixWord ++ tailWord_3161809) baseStart_3161809 baseEnd_3161809 := by
    simpa [prefixWord, tailWord_3161809, baseEnd_3161809] using wordTrace_append hprefix tailTrace_3161809
  have hstable : (prefixWord ++ tailWord_3161809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161809).length < 2 ^ (prefixWord ++ tailWord_3161809).sum := by decide
  have hdescent : baseEnd_3161809 < baseStart_3161809 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161860 : List Nat := [2, 3, 2, 2, 1, 3, 3, 2, 1, 4]
def baseStart_3161860 : Nat := 118140960795 + 3161860 * 2 ^ 59
def prefixEnd_3161860 : Nat := 4983230072969 + 3 ^ 40 * 3161860 * 2
def baseEnd_3161860 : Nat := 541184647408368147302959

theorem tailTrace_3161860 : CollatzResearch.WordTrace tailWord_3161860 prefixEnd_3161860 541184647408368147302959 := by
  unfold tailWord_3161860
  simp only [CollatzResearch.WordTrace]
  refine ⟨57661254162564348770649517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76881672216752465027532689 57661254162564348770649517)
  ·
    refine ⟨21622970310961630788993569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57661254162564348770649517 21622970310961630788993569)
    ·
      refine ⟨16217227733221223091745177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21622970310961630788993569 16217227733221223091745177)
      ·
        refine ⟨12162920799915917318808883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16217227733221223091745177 12162920799915917318808883)
        ·
          refine ⟨18244381199873875978213325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12162920799915917318808883 18244381199873875978213325)
          ·
            refine ⟨6841642949952703491829997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18244381199873875978213325 6841642949952703491829997)
            ·
              refine ⟨2565616106232263809436249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6841642949952703491829997 2565616106232263809436249)
              ·
                refine ⟨1924212079674197857077187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565616106232263809436249 1924212079674197857077187)
                ·
                  refine ⟨2886318119511296785615781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924212079674197857077187 2886318119511296785615781)
                  ·
                    refine ⟨541184647408368147302959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886318119511296785615781 541184647408368147302959)
                    ·
                      rfl

theorem cell23_3161860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_3161860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161860 prefixEnd_3161860 := by exact prefixLift 3161860
  have htrace : WordTrace (prefixWord ++ tailWord_3161860) baseStart_3161860 baseEnd_3161860 := by
    simpa [prefixWord, tailWord_3161860, baseEnd_3161860] using wordTrace_append hprefix tailTrace_3161860
  have hstable : (prefixWord ++ tailWord_3161860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161860).length < 2 ^ (prefixWord ++ tailWord_3161860).sum := by decide
  have hdescent : baseEnd_3161860 < baseStart_3161860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161893 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 2, 3, 2]
def baseStart_3161893 : Nat := 118140960795 + 3161893 * 2 ^ 59
def prefixEnd_3161893 : Nat := 4983230072969 + 3 ^ 40 * 3161893 * 2
def baseEnd_3161893 : Nat := 1623570887086702812796225

theorem tailTrace_3161893 : CollatzResearch.WordTrace tailWord_3161893 prefixEnd_3161893 1623570887086702812796225 := by
  unfold tailWord_3161893
  simp only [CollatzResearch.WordTrace]
  refine ⟨115323711934009144177250333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76882474622672762784833555 115323711934009144177250333)
  ·
    refine ⟨43246391975253429066468875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115323711934009144177250333 43246391975253429066468875)
    ·
      refine ⟨64869587962880143599703313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43246391975253429066468875 64869587962880143599703313)
      ·
        refine ⟨48652190972160107699777485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64869587962880143599703313 48652190972160107699777485)
        ·
          refine ⟨18244571614560040387416557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48652190972160107699777485 18244571614560040387416557)
          ·
            refine ⟨6841714355460015145281209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18244571614560040387416557 6841714355460015145281209)
            ·
              refine ⟨5131285766595011358960907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6841714355460015145281209 5131285766595011358960907)
              ·
                refine ⟨7696928649892517038441361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5131285766595011358960907 7696928649892517038441361)
                ·
                  refine ⟨5772696487419387778831021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7696928649892517038441361 5772696487419387778831021)
                  ·
                    refine ⟨2164761182782270417061633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5772696487419387778831021 2164761182782270417061633)
                    ·
                      refine ⟨1623570887086702812796225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164761182782270417061633 1623570887086702812796225)
                      ·
                        rfl

theorem cell23_3161893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_3161893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161893 prefixEnd_3161893 := by exact prefixLift 3161893
  have htrace : WordTrace (prefixWord ++ tailWord_3161893) baseStart_3161893 baseEnd_3161893 := by
    simpa [prefixWord, tailWord_3161893, baseEnd_3161893] using wordTrace_append hprefix tailTrace_3161893
  have hstable : (prefixWord ++ tailWord_3161893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161893).length < 2 ^ (prefixWord ++ tailWord_3161893).sum := by decide
  have hdescent : baseEnd_3161893 < baseStart_3161893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161910 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_3161910 : Nat := 118140960795 + 3161910 * 2 ^ 59
def prefixEnd_3161910 : Nat := 4983230072969 + 3 ^ 40 * 3161910 * 2
def baseEnd_3161910 : Nat := 1623579616257829246283647

theorem tailTrace_3161910 : CollatzResearch.WordTrace tailWord_3161910 prefixEnd_3161910 1623579616257829246283647 := by
  unfold tailWord_3161910
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207770748434222255038699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 76882887983298370720412789 7207770748434222255038699)
  ·
    refine ⟨10811656122651333382558049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7207770748434222255038699 10811656122651333382558049)
    ·
      refine ⟨8108742091988500036918537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10811656122651333382558049 8108742091988500036918537)
      ·
        refine ⟨6081556568991375027688903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8108742091988500036918537 6081556568991375027688903)
        ·
          refine ⟨9122334853487062541533355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081556568991375027688903 9122334853487062541533355)
          ·
            refine ⟨13683502280230593812300033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122334853487062541533355 13683502280230593812300033)
            ·
              refine ⟨10262626710172945359225025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13683502280230593812300033 10262626710172945359225025)
              ·
                refine ⟨7696970032629709019418769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10262626710172945359225025 7696970032629709019418769)
                ·
                  refine ⟨5772727524472281764564077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7696970032629709019418769 5772727524472281764564077)
                  ·
                    refine ⟨2164772821677105661711529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5772727524472281764564077 2164772821677105661711529)
                    ·
                      refine ⟨1623579616257829246283647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164772821677105661711529 1623579616257829246283647)
                      ·
                        rfl

theorem cell23_3161910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_3161910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161910 prefixEnd_3161910 := by exact prefixLift 3161910
  have htrace : WordTrace (prefixWord ++ tailWord_3161910) baseStart_3161910 baseEnd_3161910 := by
    simpa [prefixWord, tailWord_3161910, baseEnd_3161910] using wordTrace_append hprefix tailTrace_3161910
  have hstable : (prefixWord ++ tailWord_3161910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161910).length < 2 ^ (prefixWord ++ tailWord_3161910).sum := by decide
  have hdescent : baseEnd_3161910 < baseStart_3161910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161912 : List Nat := [2, 1, 2, 1, 3, 14]
def baseStart_3161912 : Nat := 118140960795 + 3161912 * 2 ^ 59
def prefixEnd_3161912 : Nat := 4983230072969 + 3 ^ 40 * 3161912 * 2
def baseEnd_3161912 : Nat := 6681401823947070940159

theorem tailTrace_3161912 : CollatzResearch.WordTrace tailWord_3161912 prefixEnd_3161912 6681401823947070940159 := by
  unfold tailWord_3161912
  simp only [CollatzResearch.WordTrace]
  refine ⟨57662202460470155211095995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76882936613960206948127993 57662202460470155211095995)
  ·
    refine ⟨86493303690705232816643993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57662202460470155211095995 86493303690705232816643993)
    ·
      refine ⟨64869977768028924612482995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86493303690705232816643993 64869977768028924612482995)
      ·
        refine ⟨97304966652043386918724493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64869977768028924612482995 97304966652043386918724493)
        ·
          refine ⟨36489362494516270094521685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97304966652043386918724493 36489362494516270094521685)
          ·
            refine ⟨6681401823947070940159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 36489362494516270094521685 6681401823947070940159)
            ·
              rfl

theorem cell23_3161912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 14].length) (baseStart_3161912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161912 prefixEnd_3161912 := by exact prefixLift 3161912
  have htrace : WordTrace (prefixWord ++ tailWord_3161912) baseStart_3161912 baseEnd_3161912 := by
    simpa [prefixWord, tailWord_3161912, baseEnd_3161912] using wordTrace_append hprefix tailTrace_3161912
  have hstable : (prefixWord ++ tailWord_3161912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161912).length < 2 ^ (prefixWord ++ tailWord_3161912).sum := by decide
  have hdescent : baseEnd_3161912 < baseStart_3161912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161916 : List Nat := [2, 2, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_3161916 : Nat := 118140960795 + 3161916 * 2 ^ 59
def prefixEnd_3161916 : Nat := 4983230072969 + 3 ^ 40 * 3161916 * 2
def baseEnd_3161916 : Nat := 541194232380585407602873

theorem tailTrace_3161916 : CollatzResearch.WordTrace tailWord_3161916 prefixEnd_3161916 541194232380585407602873 := by
  unfold tailWord_3161916
  simp only [CollatzResearch.WordTrace]
  refine ⟨57662275406462909552668801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76883033875283879403558401 57662275406462909552668801)
  ·
    refine ⟨43246706554847182164501601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57662275406462909552668801 43246706554847182164501601)
    ·
      refine ⟨32435029916135386623376201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43246706554847182164501601 32435029916135386623376201)
      ·
        refine ⟨24326272437101539967532151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32435029916135386623376201 24326272437101539967532151)
        ·
          refine ⟨36489408655652309951298227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24326272437101539967532151 36489408655652309951298227)
          ·
            refine ⟨54734112983478464926947341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36489408655652309951298227 54734112983478464926947341)
            ·
              refine ⟨20525292368804424347605253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54734112983478464926947341 20525292368804424347605253)
              ·
                refine ⟨3848492319150829565175985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20525292368804424347605253 3848492319150829565175985)
                ·
                  refine ⟨2886369239363122173881989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848492319150829565175985 2886369239363122173881989)
                  ·
                    refine ⟨541194232380585407602873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886369239363122173881989 541194232380585407602873)
                    ·
                      rfl

theorem cell23_3161916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_3161916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161916 prefixEnd_3161916 := by exact prefixLift 3161916
  have htrace : WordTrace (prefixWord ++ tailWord_3161916) baseStart_3161916 baseEnd_3161916 := by
    simpa [prefixWord, tailWord_3161916, baseEnd_3161916] using wordTrace_append hprefix tailTrace_3161916
  have hstable : (prefixWord ++ tailWord_3161916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161916).length < 2 ^ (prefixWord ++ tailWord_3161916).sum := by decide
  have hdescent : baseEnd_3161916 < baseStart_3161916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161917 : List Nat := [1, 4, 1, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3161917 : Nat := 118140960795 + 3161917 * 2 ^ 59
def prefixEnd_3161917 : Nat := 4983230072969 + 3 ^ 40 * 3161917 * 2
def baseEnd_3161917 : Nat := 1623583210622410718896115

theorem tailTrace_3161917 : CollatzResearch.WordTrace tailWord_3161917 prefixEnd_3161917 1623583210622410718896115 := by
  unfold tailWord_3161917
  simp only [CollatzResearch.WordTrace]
  refine ⟨115324587285922196276124005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76883058190614797517416003 115324587285922196276124005)
  ·
    refine ⟨21623360116110411801773251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115324587285922196276124005 21623360116110411801773251)
    ·
      refine ⟨32435040174165617702659877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21623360116110411801773251 32435040174165617702659877)
      ·
        refine ⟨6081570032656053319248727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32435040174165617702659877 6081570032656053319248727)
        ·
          refine ⟨9122355048984079978873091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081570032656053319248727 9122355048984079978873091)
          ·
            refine ⟨13683532573476119968309637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122355048984079978873091 13683532573476119968309637)
            ·
              refine ⟨2565662357526772494058057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13683532573476119968309637 2565662357526772494058057)
              ·
                refine ⟨1924246768145079370543543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565662357526772494058057 1924246768145079370543543)
                ·
                  refine ⟨2886370152217619055815315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924246768145079370543543 2886370152217619055815315)
                  ·
                    refine ⟨4329555228326428583722973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2886370152217619055815315 4329555228326428583722973)
                    ·
                      refine ⟨1623583210622410718896115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4329555228326428583722973 1623583210622410718896115)
                      ·
                        rfl

theorem cell23_3161917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3161917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161917 prefixEnd_3161917 := by exact prefixLift 3161917
  have htrace : WordTrace (prefixWord ++ tailWord_3161917) baseStart_3161917 baseEnd_3161917 := by
    simpa [prefixWord, tailWord_3161917, baseEnd_3161917] using wordTrace_append hprefix tailTrace_3161917
  have hstable : (prefixWord ++ tailWord_3161917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161917).length < 2 ^ (prefixWord ++ tailWord_3161917).sum := by decide
  have hdescent : baseEnd_3161917 < baseStart_3161917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161933 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 1, 6]
def baseStart_3161933 : Nat := 118140960795 + 3161933 * 2 ^ 59
def prefixEnd_3161933 : Nat := 4983230072969 + 3 ^ 40 * 3161933 * 2
def baseEnd_3161933 : Nat := 541197142104294218765347

theorem tailTrace_3161933 : CollatzResearch.WordTrace tailWord_3161933 prefixEnd_3161933 541197142104294218765347 := by
  unfold tailWord_3161933
  simp only [CollatzResearch.WordTrace]
  refine ⟨115325170853864231008706453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76883447235909487339137635 115325170853864231008706453)
  ·
    refine ⟨5405867383774885828533115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 115325170853864231008706453 5405867383774885828533115)
    ·
      refine ⟨8108801075662328742799673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5405867383774885828533115 8108801075662328742799673)
      ·
        refine ⟨6081600806746746557099755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8108801075662328742799673 6081600806746746557099755)
        ·
          refine ⟨9122401210120119835649633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081600806746746557099755 9122401210120119835649633)
          ·
            refine ⟨6841800907590089876737225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9122401210120119835649633 6841800907590089876737225)
            ·
              refine ⟨5131350680692567407552919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6841800907590089876737225 5131350680692567407552919)
              ·
                refine ⟨7697026021038851111329379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5131350680692567407552919 7697026021038851111329379)
                ·
                  refine ⟨11545539031558276666994069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7697026021038851111329379 11545539031558276666994069)
                  ·
                    refine ⟨541197142104294218765347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11545539031558276666994069 541197142104294218765347)
                    ·
                      rfl

theorem cell23_3161933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_3161933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161933 prefixEnd_3161933 := by exact prefixLift 3161933
  have htrace : WordTrace (prefixWord ++ tailWord_3161933) baseStart_3161933 baseEnd_3161933 := by
    simpa [prefixWord, tailWord_3161933, baseEnd_3161933] using wordTrace_append hprefix tailTrace_3161933
  have hstable : (prefixWord ++ tailWord_3161933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161933).length < 2 ^ (prefixWord ++ tailWord_3161933).sum := by decide
  have hdescent : baseEnd_3161933 < baseStart_3161933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161940 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_3161940 : Nat := 118140960795 + 3161940 * 2 ^ 59
def prefixEnd_3161940 : Nat := 4983230072969 + 3 ^ 40 * 3161940 * 2
def baseEnd_3161940 : Nat := 1623595020677464128908509

theorem tailTrace_3161940 : CollatzResearch.WordTrace tailWord_3161940 prefixEnd_3161940 1623595020677464128908509 := by
  unfold tailWord_3161940
  simp only [CollatzResearch.WordTrace]
  refine ⟨57662713082419435602105637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76883617443225914136140849 57662713082419435602105637)
  ·
    refine ⟨10811758702953644175394807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57662713082419435602105637 10811758702953644175394807)
    ·
      refine ⟨16217638054430466263092211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10811758702953644175394807 16217638054430466263092211)
      ·
        refine ⟨24326457081645699394638317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16217638054430466263092211 24326457081645699394638317)
        ·
          refine ⟨9122421405617137272989369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24326457081645699394638317 9122421405617137272989369)
          ·
            refine ⟨6841816054212852954742027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9122421405617137272989369 6841816054212852954742027)
            ·
              refine ⟨10262724081319279432113041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6841816054212852954742027 10262724081319279432113041)
              ·
                refine ⟨7697043060989459574084781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10262724081319279432113041 7697043060989459574084781)
                ·
                  refine ⟨2886391147871047340281793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7697043060989459574084781 2886391147871047340281793)
                  ·
                    refine ⟨2164793360903285505211345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2886391147871047340281793 2164793360903285505211345)
                    ·
                      refine ⟨1623595020677464128908509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164793360903285505211345 1623595020677464128908509)
                      ·
                        rfl

theorem cell23_3161940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_3161940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161940 prefixEnd_3161940 := by exact prefixLift 3161940
  have htrace : WordTrace (prefixWord ++ tailWord_3161940) baseStart_3161940 baseEnd_3161940 := by
    simpa [prefixWord, tailWord_3161940, baseEnd_3161940] using wordTrace_append hprefix tailTrace_3161940
  have hstable : (prefixWord ++ tailWord_3161940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161940).length < 2 ^ (prefixWord ++ tailWord_3161940).sum := by decide
  have hdescent : baseEnd_3161940 < baseStart_3161940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161973 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 3]
def baseStart_3161973 : Nat := 118140960795 + 3161973 * 2 ^ 59
def prefixEnd_3161973 : Nat := 4983230072969 + 3 ^ 40 * 3161973 * 2
def baseEnd_3161973 : Nat := 1623611965539062499795857

theorem tailTrace_3161973 : CollatzResearch.WordTrace tailWord_3161973 prefixEnd_3161973 1623611965539062499795857 := by
  unfold tailWord_3161973
  simp only [CollatzResearch.WordTrace]
  refine ⟨115326629773719317840162573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76884419849146211893441715 115326629773719317840162573)
  ·
    refine ⟨43247486165144744190060965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115326629773719317840162573 43247486165144744190060965)
    ·
      refine ⟨8108903655964639535636431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43247486165144744190060965 8108903655964639535636431)
      ·
        refine ⟨12163355483946959303454647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8108903655964639535636431 12163355483946959303454647)
        ·
          refine ⟨18245033225920438955181971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12163355483946959303454647 18245033225920438955181971)
          ·
            refine ⟨27367549838880658432772957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18245033225920438955181971 27367549838880658432772957)
            ·
              refine ⟨10262831189580246912289859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27367549838880658432772957 10262831189580246912289859)
              ·
                refine ⟨15394246784370370368434789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10262831189580246912289859 15394246784370370368434789)
                ·
                  refine ⟨2886421272069444444081523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15394246784370370368434789 2886421272069444444081523)
                  ·
                    refine ⟨4329631908104166666122285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2886421272069444444081523 4329631908104166666122285)
                    ·
                      refine ⟨1623611965539062499795857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4329631908104166666122285 1623611965539062499795857)
                      ·
                        rfl

theorem cell23_3161973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_3161973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161973 prefixEnd_3161973 := by exact prefixLift 3161973
  have htrace : WordTrace (prefixWord ++ tailWord_3161973) baseStart_3161973 baseEnd_3161973 := by
    simpa [prefixWord, tailWord_3161973, baseEnd_3161973] using wordTrace_append hprefix tailTrace_3161973
  have hstable : (prefixWord ++ tailWord_3161973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161973).length < 2 ^ (prefixWord ++ tailWord_3161973).sum := by decide
  have hdescent : baseEnd_3161973 < baseStart_3161973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161989 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 2, 6]
def baseStart_3161989 : Nat := 118140960795 + 3161989 * 2 ^ 59
def prefixEnd_3161989 : Nat := 4983230072969 + 3 ^ 40 * 3161989 * 2
def baseEnd_3161989 : Nat := 541206727076511479065261

theorem tailTrace_3161989 : CollatzResearch.WordTrace tailWord_3161989 prefixEnd_3161989 541206727076511479065261 := by
  unfold tailWord_3161989
  simp only [CollatzResearch.WordTrace]
  refine ⟨115327213341661352572745021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76884808894440901715163347 115327213341661352572745021)
  ·
    refine ⟨43247705003123007214779383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115327213341661352572745021 43247705003123007214779383)
    ·
      refine ⟨64871557504684510822169075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43247705003123007214779383 64871557504684510822169075)
      ·
        refine ⟨97307336257026766233253613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64871557504684510822169075 97307336257026766233253613)
        ·
          refine ⟨36490251096385037337470105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97307336257026766233253613 36490251096385037337470105)
          ·
            refine ⟨27367688322288778003102579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36490251096385037337470105 27367688322288778003102579)
            ·
              refine ⟨41051532483433167004653869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27367688322288778003102579 41051532483433167004653869)
              ·
                refine ⟨15394324681287437626745201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41051532483433167004653869 15394324681287437626745201)
                ·
                  refine ⟨11545743510965578220058901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15394324681287437626745201 11545743510965578220058901)
                  ·
                    refine ⟨541206727076511479065261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11545743510965578220058901 541206727076511479065261)
                    ·
                      rfl

theorem cell23_3161989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 6].length) (baseStart_3161989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161989 prefixEnd_3161989 := by exact prefixLift 3161989
  have htrace : WordTrace (prefixWord ++ tailWord_3161989) baseStart_3161989 baseEnd_3161989 := by
    simpa [prefixWord, tailWord_3161989, baseEnd_3161989] using wordTrace_append hprefix tailTrace_3161989
  have hstable : (prefixWord ++ tailWord_3161989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161989).length < 2 ^ (prefixWord ++ tailWord_3161989).sum := by decide
  have hdescent : baseEnd_3161989 < baseStart_3161989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3161999 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 3]
def baseStart_3161999 : Nat := 118140960795 + 3161999 * 2 ^ 59
def prefixEnd_3161999 : Nat := 4983230072969 + 3 ^ 40 * 3161999 * 2
def baseEnd_3161999 : Nat := 1623625316036079398070737

theorem tailTrace_3161999 : CollatzResearch.WordTrace tailWord_3161999 prefixEnd_3161999 1623625316036079398070737 := by
  unfold tailWord_3161999
  simp only [CollatzResearch.WordTrace]
  refine ⟨115327578071625124280609051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76885052047750082853739367 115327578071625124280609051)
  ·
    refine ⟨172991367107437686420913577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115327578071625124280609051 172991367107437686420913577)
    ·
      refine ⟨129743525330578264815685183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172991367107437686420913577 129743525330578264815685183)
      ·
        refine ⟨194615287995867397223527775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129743525330578264815685183 194615287995867397223527775)
        ·
          refine ⟨291922931993801095835291663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194615287995867397223527775 291922931993801095835291663)
          ·
            refine ⟨437884397990701643752937495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291922931993801095835291663 437884397990701643752937495)
            ·
              refine ⟨656826596986052465629406243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 437884397990701643752937495 656826596986052465629406243)
              ·
                refine ⟨985239895479078698444109365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 656826596986052465629406243 985239895479078698444109365)
                ·
                  refine ⟨92366240201163627979135253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 985239895479078698444109365 92366240201163627979135253)
                  ·
                    refine ⟨4329667509429545061521965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 92366240201163627979135253 4329667509429545061521965)
                    ·
                      refine ⟨1623625316036079398070737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4329667509429545061521965 1623625316036079398070737)
                      ·
                        rfl

theorem cell23_3161999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_3161999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3161999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3161999 prefixEnd_3161999 := by exact prefixLift 3161999
  have htrace : WordTrace (prefixWord ++ tailWord_3161999) baseStart_3161999 baseEnd_3161999 := by
    simpa [prefixWord, tailWord_3161999, baseEnd_3161999] using wordTrace_append hprefix tailTrace_3161999
  have hstable : (prefixWord ++ tailWord_3161999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3161999).length < 2 ^ (prefixWord ++ tailWord_3161999).sum := by decide
  have hdescent : baseEnd_3161999 < baseStart_3161999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3161999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162009 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 4]
def baseStart_3162009 : Nat := 118140960795 + 3162009 * 2 ^ 59
def prefixEnd_3162009 : Nat := 4983230072969 + 3 ^ 40 * 3162009 * 2
def baseEnd_3162009 : Nat := 1623630450842624358945691

theorem tailTrace_3162009 : CollatzResearch.WordTrace tailWord_3162009 prefixEnd_3162009 1623630450842624358945691 := by
  unfold tailWord_3162009
  simp only [CollatzResearch.WordTrace]
  refine ⟨115327942801588895988473081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76885295201059263992315387 115327942801588895988473081)
  ·
    refine ⟨86495957101191671991354811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115327942801588895988473081 86495957101191671991354811)
    ·
      refine ⟨129743935651787507987032217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86495957101191671991354811 129743935651787507987032217)
      ·
        refine ⟨97307951738840630990274163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129743935651787507987032217 97307951738840630990274163)
        ·
          refine ⟨145961927608260946485411245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97307951738840630990274163 145961927608260946485411245)
          ·
            refine ⟨54735722853097854932029217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145961927608260946485411245 54735722853097854932029217)
            ·
              refine ⟨41051792139823391199021913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54735722853097854932029217 41051792139823391199021913)
              ·
                refine ⟨30788844104867543399266435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41051792139823391199021913 30788844104867543399266435)
                ·
                  refine ⟨46183266157301315098899653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30788844104867543399266435 46183266157301315098899653)
                  ·
                    refine ⟨8659362404493996581043685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46183266157301315098899653 8659362404493996581043685)
                    ·
                      refine ⟨1623630450842624358945691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8659362404493996581043685 1623630450842624358945691)
                      ·
                        rfl

theorem cell23_3162009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_3162009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162009 prefixEnd_3162009 := by exact prefixLift 3162009
  have htrace : WordTrace (prefixWord ++ tailWord_3162009) baseStart_3162009 baseEnd_3162009 := by
    simpa [prefixWord, tailWord_3162009, baseEnd_3162009] using wordTrace_append hprefix tailTrace_3162009
  have hstable : (prefixWord ++ tailWord_3162009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162009).length < 2 ^ (prefixWord ++ tailWord_3162009).sum := by decide
  have hdescent : baseEnd_3162009 < baseStart_3162009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162059 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7]
def baseStart_3162059 : Nat := 118140960795 + 3162059 * 2 ^ 59
def prefixEnd_3162059 : Nat := 4983230072969 + 3 ^ 40 * 3162059 * 2
def baseEnd_3162059 : Nat := 1623656124875349163320461

theorem tailTrace_3162059 : CollatzResearch.WordTrace tailWord_3162059 prefixEnd_3162059 1623656124875349163320461 := by
  unfold tailWord_3162059
  simp only [CollatzResearch.WordTrace]
  refine ⟨115329766451407754527793231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76886510967605169685195487 115329766451407754527793231)
  ·
    refine ⟨172994649677111631791689847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115329766451407754527793231 172994649677111631791689847)
    ·
      refine ⟨259491974515667447687534771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172994649677111631791689847 259491974515667447687534771)
      ·
        refine ⟨389237961773501171531302157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259491974515667447687534771 389237961773501171531302157)
        ·
          refine ⟨145964235665062939324238309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389237961773501171531302157 145964235665062939324238309)
          ·
            refine ⟨27368294187199301123294683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145964235665062939324238309 27368294187199301123294683)
            ·
              refine ⟨41052441280798951684942025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27368294187199301123294683 41052441280798951684942025)
              ·
                refine ⟨30789330960599213763706519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41052441280798951684942025 30789330960599213763706519)
                ·
                  refine ⟨46183996440898820645559779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30789330960599213763706519 46183996440898820645559779)
                  ·
                    refine ⟨69275994661348230968339669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46183996440898820645559779 69275994661348230968339669)
                    ·
                      refine ⟨1623656124875349163320461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69275994661348230968339669 1623656124875349163320461)
                      ·
                        rfl

theorem cell23_3162059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 7].length) (baseStart_3162059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162059 prefixEnd_3162059 := by exact prefixLift 3162059
  have htrace : WordTrace (prefixWord ++ tailWord_3162059) baseStart_3162059 baseEnd_3162059 := by
    simpa [prefixWord, tailWord_3162059, baseEnd_3162059] using wordTrace_append hprefix tailTrace_3162059
  have hstable : (prefixWord ++ tailWord_3162059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162059).length < 2 ^ (prefixWord ++ tailWord_3162059).sum := by decide
  have hdescent : baseEnd_3162059 < baseStart_3162059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162087 : List Nat := [1, 1, 5, 2, 3, 2, 2, 2, 5]
def baseStart_3162087 : Nat := 118140960795 + 3162087 * 2 ^ 59
def prefixEnd_3162087 : Nat := 4983230072969 + 3 ^ 40 * 3162087 * 2
def baseEnd_3162087 : Nat := 180407833592630561530037

theorem tailTrace_3162087 : CollatzResearch.WordTrace tailWord_3162087 prefixEnd_3162087 180407833592630561530037 := by
  unfold tailWord_3162087
  simp only [CollatzResearch.WordTrace]
  refine ⟨115330787695306315309812515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76887191796870876873208343 115330787695306315309812515)
  ·
    refine ⟨172996181542959472964718773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115330787695306315309812515 172996181542959472964718773)
    ·
      refine ⟨16218392019652450590442385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172996181542959472964718773 16218392019652450590442385)
      ·
        refine ⟨12163794014739337942831789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16218392019652450590442385 12163794014739337942831789)
        ·
          refine ⟨4561422755527251728561921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12163794014739337942831789 4561422755527251728561921)
          ·
            refine ⟨3421067066645438796421441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4561422755527251728561921 3421067066645438796421441)
            ·
              refine ⟨2565800299984079097316081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421067066645438796421441 2565800299984079097316081)
              ·
                refine ⟨1924350224988059322987061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2565800299984079097316081 1924350224988059322987061)
                ·
                  refine ⟨180407833592630561530037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1924350224988059322987061 180407833592630561530037)
                  ·
                    rfl

theorem cell23_3162087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 2, 5].length) (baseStart_3162087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162087 prefixEnd_3162087 := by exact prefixLift 3162087
  have htrace : WordTrace (prefixWord ++ tailWord_3162087) baseStart_3162087 baseEnd_3162087 := by
    simpa [prefixWord, tailWord_3162087, baseEnd_3162087] using wordTrace_append hprefix tailTrace_3162087
  have hstable : (prefixWord ++ tailWord_3162087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162087).length < 2 ^ (prefixWord ++ tailWord_3162087).sum := by decide
  have hdescent : baseEnd_3162087 < baseStart_3162087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162113 : List Nat := [1, 2, 4, 1, 2, 1, 3, 2, 3, 4]
def baseStart_3162113 : Nat := 118140960795 + 3162113 * 2 ^ 59
def prefixEnd_3162113 : Nat := 4983230072969 + 3 ^ 40 * 3162113 * 2
def baseEnd_3162113 : Nat := 541227950943563984015071

theorem tailTrace_3162113 : CollatzResearch.WordTrace tailWord_3162113 prefixEnd_3162113 541227950943563984015071 := by
  unfold tailWord_3162113
  simp only [CollatzResearch.WordTrace]
  refine ⟨115331735993212121750258993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76887823995474747833505995 115331735993212121750258993)
  ·
    refine ⟨86498801994909091312694245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115331735993212121750258993 86498801994909091312694245)
    ·
      refine ⟨16218525374045454621130171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86498801994909091312694245 16218525374045454621130171)
      ·
        refine ⟨24327788061068181931695257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16218525374045454621130171 24327788061068181931695257)
        ·
          refine ⟨18245841045801136448771443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24327788061068181931695257 18245841045801136448771443)
          ·
            refine ⟨27368761568701704673157165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18245841045801136448771443 27368761568701704673157165)
            ·
              refine ⟨10263285588263139252433937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27368761568701704673157165 10263285588263139252433937)
              ·
                refine ⟨7697464191197354439325453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10263285588263139252433937 7697464191197354439325453)
                ·
                  refine ⟨2886549071699007914747045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7697464191197354439325453 2886549071699007914747045)
                  ·
                    refine ⟨541227950943563984015071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886549071699007914747045 541227950943563984015071)
                    ·
                      rfl

theorem cell23_3162113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_3162113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162113 prefixEnd_3162113 := by exact prefixLift 3162113
  have htrace : WordTrace (prefixWord ++ tailWord_3162113) baseStart_3162113 baseEnd_3162113 := by
    simpa [prefixWord, tailWord_3162113, baseEnd_3162113] using wordTrace_append hprefix tailTrace_3162113
  have hstable : (prefixWord ++ tailWord_3162113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162113).length < 2 ^ (prefixWord ++ tailWord_3162113).sum := by decide
  have hdescent : baseEnd_3162113 < baseStart_3162113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162126 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 8]
def baseStart_3162126 : Nat := 118140960795 + 3162126 * 2 ^ 59
def prefixEnd_3162126 : Nat := 4983230072969 + 3 ^ 40 * 3162126 * 2
def baseEnd_3162126 : Nat := 180410058675466711242517

theorem tailTrace_3162126 : CollatzResearch.WordTrace tailWord_3162126 prefixEnd_3162126 180410058675466711242517 := by
  unfold tailWord_3162126
  simp only [CollatzResearch.WordTrace]
  refine ⟨14416526267770628121310279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76888140094776683313654821 14416526267770628121310279)
  ·
    refine ⟨21624789401655942181965419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14416526267770628121310279 21624789401655942181965419)
    ·
      refine ⟨32437184102483913272948129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21624789401655942181965419 32437184102483913272948129)
      ·
        refine ⟨24327888076862934954711097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32437184102483913272948129 24327888076862934954711097)
        ·
          refine ⟨18245916057647201216033323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24327888076862934954711097 18245916057647201216033323)
          ·
            refine ⟨27368874086470801824049985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18245916057647201216033323 27368874086470801824049985)
            ·
              refine ⟨20526655564853101368037489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27368874086470801824049985 20526655564853101368037489)
              ·
                refine ⟨15394991673639826026028117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20526655564853101368037489 15394991673639826026028117)
                ·
                  refine ⟨180410058675466711242517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15394991673639826026028117 180410058675466711242517)
                  ·
                    rfl

theorem cell23_3162126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_3162126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162126 prefixEnd_3162126 := by exact prefixLift 3162126
  have htrace : WordTrace (prefixWord ++ tailWord_3162126) baseStart_3162126 baseEnd_3162126 := by
    simpa [prefixWord, tailWord_3162126, baseEnd_3162126] using wordTrace_append hprefix tailTrace_3162126
  have hstable : (prefixWord ++ tailWord_3162126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162126).length < 2 ^ (prefixWord ++ tailWord_3162126).sum := by decide
  have hdescent : baseEnd_3162126 < baseStart_3162126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162146 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_3162146 : Nat := 118140960795 + 3162146 * 2 ^ 59
def prefixEnd_3162146 : Nat := 4983230072969 + 3 ^ 40 * 3162146 * 2
def baseEnd_3162146 : Nat := 1623700797692290322932561

theorem tailTrace_3162146 : CollatzResearch.WordTrace tailWord_3162146 prefixEnd_3162146 1623700797692290322932561 := by
  unfold tailWord_3162146
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833234900523142096552573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76888626401395045590806861 28833234900523142096552573)
  ·
    refine ⟨10812463087696178286207215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28833234900523142096552573 10812463087696178286207215)
    ·
      refine ⟨16218694631544267429310823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10812463087696178286207215 16218694631544267429310823)
      ·
        refine ⟨24328041947316401143966235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16218694631544267429310823 24328041947316401143966235)
        ·
          refine ⟨36492062920974601715949353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24328041947316401143966235 36492062920974601715949353)
          ·
            refine ⟨27369047190730951286962015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36492062920974601715949353 27369047190730951286962015)
            ·
              refine ⟨41053570786096426930443023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27369047190730951286962015 41053570786096426930443023)
              ·
                refine ⟨61580356179144640395664535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41053570786096426930443023 61580356179144640395664535)
                ·
                  refine ⟨92370534268716960593496803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61580356179144640395664535 92370534268716960593496803)
                  ·
                    refine ⟨138555801403075440890245205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92370534268716960593496803 138555801403075440890245205)
                    ·
                      refine ⟨1623700797692290322932561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138555801403075440890245205 1623700797692290322932561)
                      ·
                        rfl

theorem cell23_3162146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_3162146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162146 prefixEnd_3162146 := by exact prefixLift 3162146
  have htrace : WordTrace (prefixWord ++ tailWord_3162146) baseStart_3162146 baseEnd_3162146 := by
    simpa [prefixWord, tailWord_3162146, baseEnd_3162146] using wordTrace_append hprefix tailTrace_3162146
  have hstable : (prefixWord ++ tailWord_3162146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162146).length < 2 ^ (prefixWord ++ tailWord_3162146).sum := by decide
  have hdescent : baseEnd_3162146 < baseStart_3162146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162156 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_3162156 : Nat := 118140960795 + 3162156 * 2 ^ 59
def prefixEnd_3162156 : Nat := 4983230072969 + 3 ^ 40 * 3162156 * 2
def baseEnd_3162156 : Nat := 541235310832945094602505

theorem tailTrace_3162156 : CollatzResearch.WordTrace tailWord_3162156 prefixEnd_3162156 541235310832945094602505 := by
  unfold tailWord_3162156
  simp only [CollatzResearch.WordTrace]
  refine ⟨57666652166028170047037161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76888869554704226729382881 57666652166028170047037161)
  ·
    refine ⟨43249989124521127535277871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57666652166028170047037161 43249989124521127535277871)
    ·
      refine ⟨64874983686781691302916807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43249989124521127535277871 64874983686781691302916807)
      ·
        refine ⟨97312475530172536954375211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64874983686781691302916807 97312475530172536954375211)
        ·
          refine ⟨145968713295258805431562817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97312475530172536954375211 145968713295258805431562817)
          ·
            refine ⟨109476534971444104073672113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145968713295258805431562817 109476534971444104073672113)
            ·
              refine ⟨82107401228583078055254085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109476534971444104073672113 82107401228583078055254085)
              ·
                refine ⟨15395137730359327135360141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82107401228583078055254085 15395137730359327135360141)
                ·
                  refine ⟨5773176648884747675760053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15395137730359327135360141 5773176648884747675760053)
                  ·
                    refine ⟨541235310832945094602505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5773176648884747675760053 541235310832945094602505)
                    ·
                      rfl

theorem cell23_3162156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_3162156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162156 prefixEnd_3162156 := by exact prefixLift 3162156
  have htrace : WordTrace (prefixWord ++ tailWord_3162156) baseStart_3162156 baseEnd_3162156 := by
    simpa [prefixWord, tailWord_3162156, baseEnd_3162156] using wordTrace_append hprefix tailTrace_3162156
  have hstable : (prefixWord ++ tailWord_3162156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162156).length < 2 ^ (prefixWord ++ tailWord_3162156).sum := by decide
  have hdescent : baseEnd_3162156 < baseStart_3162156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162163 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 1, 5, 2]
def baseStart_3162163 : Nat := 118140960795 + 3162163 * 2 ^ 59
def prefixEnd_3162163 : Nat := 4983230072969 + 3 ^ 40 * 3162163 * 2
def baseEnd_3162163 : Nat := 1623709526863416756419983

theorem tailTrace_3162163 : CollatzResearch.WordTrace tailWord_3162163 prefixEnd_3162163 1623709526863416756419983 := by
  unfold tailWord_3162163
  simp only [CollatzResearch.WordTrace]
  refine ⟨115333559643030980289579143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76889039762020653526386095 115333559643030980289579143)
  ·
    refine ⟨173000339464546470434368715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115333559643030980289579143 173000339464546470434368715)
    ·
      refine ⟨259500509196819705651553073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173000339464546470434368715 259500509196819705651553073)
      ·
        refine ⟨194625381897614779238664805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 259500509196819705651553073 194625381897614779238664805)
        ·
          refine ⟨36492259105802771107249651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 194625381897614779238664805 36492259105802771107249651)
          ·
            refine ⟨54738388658704156660874477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36492259105802771107249651 54738388658704156660874477)
            ·
              refine ⟨20526895747014058747827929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54738388658704156660874477 20526895747014058747827929)
              ·
                refine ⟨15395171810260544060870947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20526895747014058747827929 15395171810260544060870947)
                ·
                  refine ⟨23092757715390816091306421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15395171810260544060870947 23092757715390816091306421)
                  ·
                    refine ⟨2164946035817889008559977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23092757715390816091306421 2164946035817889008559977)
                    ·
                      refine ⟨1623709526863416756419983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2164946035817889008559977 1623709526863416756419983)
                      ·
                        rfl

theorem cell23_3162163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 1, 5, 2].length) (baseStart_3162163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162163 prefixEnd_3162163 := by exact prefixLift 3162163
  have htrace : WordTrace (prefixWord ++ tailWord_3162163) baseStart_3162163 baseEnd_3162163 := by
    simpa [prefixWord, tailWord_3162163, baseEnd_3162163] using wordTrace_append hprefix tailTrace_3162163
  have hstable : (prefixWord ++ tailWord_3162163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162163).length < 2 ^ (prefixWord ++ tailWord_3162163).sum := by decide
  have hdescent : baseEnd_3162163 < baseStart_3162163 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162186 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 3, 6]
def baseStart_3162186 : Nat := 118140960795 + 3162186 * 2 ^ 59
def prefixEnd_3162186 : Nat := 4983230072969 + 3 ^ 40 * 3162186 * 2
def baseEnd_3162186 : Nat := 541240445639490055477459

theorem tailTrace_3162186 : CollatzResearch.WordTrace tailWord_3162186 prefixEnd_3162186 541240445639490055477459 := by
  unfold tailWord_3162186
  simp only [CollatzResearch.WordTrace]
  refine ⟨28833599630486913804416603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76889599014631770145110941 28833599630486913804416603)
  ·
    refine ⟨43250399445730370706624905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28833599630486913804416603 43250399445730370706624905)
    ·
      refine ⟨32437799584297778029968679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43250399445730370706624905 32437799584297778029968679)
      ·
        refine ⟨48656699376446667044953019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32437799584297778029968679 48656699376446667044953019)
        ·
          refine ⟨72985049064670000567429529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48656699376446667044953019 72985049064670000567429529)
          ·
            refine ⟨54738786798502500425572147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72985049064670000567429529 54738786798502500425572147)
            ·
              refine ⟨82108180197753750638358221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54738786798502500425572147 82108180197753750638358221)
              ·
                refine ⟨30790567574157656489384333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82108180197753750638358221 30790567574157656489384333)
                ·
                  refine ⟨11546462840309121183519125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30790567574157656489384333 11546462840309121183519125)
                  ·
                    refine ⟨541240445639490055477459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11546462840309121183519125 541240445639490055477459)
                    ·
                      rfl

theorem cell23_3162186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_3162186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162186 prefixEnd_3162186 := by exact prefixLift 3162186
  have htrace : WordTrace (prefixWord ++ tailWord_3162186) baseStart_3162186 baseEnd_3162186 := by
    simpa [prefixWord, tailWord_3162186, baseEnd_3162186] using wordTrace_append hprefix tailTrace_3162186
  have hstable : (prefixWord ++ tailWord_3162186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162186).length < 2 ^ (prefixWord ++ tailWord_3162186).sum := by decide
  have hdescent : baseEnd_3162186 < baseStart_3162186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162213 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3162213 : Nat := 118140960795 + 3162213 * 2 ^ 59
def prefixEnd_3162213 : Nat := 4983230072969 + 3 ^ 40 * 3162213 * 2
def baseEnd_3162213 : Nat := 1623735200896141560794753

theorem tailTrace_3162213 : CollatzResearch.WordTrace tailWord_3162213 prefixEnd_3162213 1623735200896141560794753 := by
  unfold tailWord_3162213
  simp only [CollatzResearch.WordTrace]
  refine ⟨115335383292849838828899293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76890255528566559219266195 115335383292849838828899293)
  ·
    refine ⟨43250768734818689560837235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115335383292849838828899293 43250768734818689560837235)
    ·
      refine ⟨64876153102228034341255853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43250768734818689560837235 64876153102228034341255853)
      ·
        refine ⟨24328557413335512877970945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64876153102228034341255853 24328557413335512877970945)
        ·
          refine ⟨18246418060001634658478209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24328557413335512877970945 18246418060001634658478209)
          ·
            refine ⟨13684813545001225993858657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18246418060001634658478209 13684813545001225993858657)
            ·
              refine ⟨10263610158750919495393993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13684813545001225993858657 10263610158750919495393993)
              ·
                refine ⟨7697707619063189621545495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10263610158750919495393993 7697707619063189621545495)
                ·
                  refine ⟨11546561428594784432318243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7697707619063189621545495 11546561428594784432318243)
                  ·
                    refine ⟨17319842142892176648477365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11546561428594784432318243 17319842142892176648477365)
                    ·
                      refine ⟨1623735200896141560794753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17319842142892176648477365 1623735200896141560794753)
                      ·
                        rfl

theorem cell23_3162213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3162213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162213 prefixEnd_3162213 := by exact prefixLift 3162213
  have htrace : WordTrace (prefixWord ++ tailWord_3162213) baseStart_3162213 baseEnd_3162213 := by
    simpa [prefixWord, tailWord_3162213, baseEnd_3162213] using wordTrace_append hprefix tailTrace_3162213
  have hstable : (prefixWord ++ tailWord_3162213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162213).length < 2 ^ (prefixWord ++ tailWord_3162213).sum := by decide
  have hdescent : baseEnd_3162213 < baseStart_3162213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162220 : List Nat := [2, 2, 1, 1, 3, 4, 1, 3, 2, 4]
def baseStart_3162220 : Nat := 118140960795 + 3162220 * 2 ^ 59
def prefixEnd_3162220 : Nat := 4983230072969 + 3 ^ 40 * 3162220 * 2
def baseEnd_3162220 : Nat := 541246265086907677802407

theorem tailTrace_3162220 : CollatzResearch.WordTrace tailWord_3162220 prefixEnd_3162220 541246265086907677802407 := by
  unfold tailWord_3162220
  simp only [CollatzResearch.WordTrace]
  refine ⟨57667819301912239512202057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76890425735882986016269409 57667819301912239512202057)
  ·
    refine ⟨43250864476434179634151543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57667819301912239512202057 43250864476434179634151543)
    ·
      refine ⟨64876296714651269451227315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43250864476434179634151543 64876296714651269451227315)
      ·
        refine ⟨97314445071976904176840973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64876296714651269451227315 97314445071976904176840973)
        ·
          refine ⟨36492916901991339066315365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97314445071976904176840973 36492916901991339066315365)
          ·
            refine ⟨6842421919123376074934131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36492916901991339066315365 6842421919123376074934131)
            ·
              refine ⟨10263632878685064112401197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6842421919123376074934131 10263632878685064112401197)
              ·
                refine ⟨3848862329506899042150449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10263632878685064112401197 3848862329506899042150449)
                ·
                  refine ⟨2886646747130174281612837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3848862329506899042150449 2886646747130174281612837)
                  ·
                    refine ⟨541246265086907677802407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2886646747130174281612837 541246265086907677802407)
                    ·
                      rfl

theorem cell23_3162220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 4].length) (baseStart_3162220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162220 prefixEnd_3162220 := by exact prefixLift 3162220
  have htrace : WordTrace (prefixWord ++ tailWord_3162220) baseStart_3162220 baseEnd_3162220 := by
    simpa [prefixWord, tailWord_3162220, baseEnd_3162220] using wordTrace_append hprefix tailTrace_3162220
  have hstable : (prefixWord ++ tailWord_3162220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162220).length < 2 ^ (prefixWord ++ tailWord_3162220).sum := by decide
  have hdescent : baseEnd_3162220 < baseStart_3162220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162243 : List Nat := [1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 3]
def baseStart_3162243 : Nat := 118140960795 + 3162243 * 2 ^ 59
def prefixEnd_3162243 : Nat := 4983230072969 + 3 ^ 40 * 3162243 * 2
def baseEnd_3162243 : Nat := 1623750605315776443419615

theorem tailTrace_3162243 : CollatzResearch.WordTrace tailWord_3162243 prefixEnd_3162243 1623750605315776443419615 := by
  unfold tailWord_3162243
  simp only [CollatzResearch.WordTrace]
  refine ⟨115336477482741153952491383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76890984988494102634994255 115336477482741153952491383)
  ·
    refine ⟨173004716224111730928737075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115336477482741153952491383 173004716224111730928737075)
    ·
      refine ⟨259507074336167596393105613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173004716224111730928737075 259507074336167596393105613)
      ·
        refine ⟨97315152876062848647414605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 259507074336167596393105613 97315152876062848647414605)
        ·
          refine ⟨36493182328523568242780477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97315152876062848647414605 36493182328523568242780477)
          ·
            refine ⟨13684943373196338091042679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36493182328523568242780477 13684943373196338091042679)
            ·
              refine ⟨20527415059794507136564019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13684943373196338091042679 20527415059794507136564019)
              ·
                refine ⟨30791122589691760704846029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20527415059794507136564019 30791122589691760704846029)
                ·
                  refine ⟨11546670971134410264317261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30791122589691760704846029 11546670971134410264317261)
                  ·
                    refine ⟨4330001614175403849118973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11546670971134410264317261 4330001614175403849118973)
                    ·
                      refine ⟨1623750605315776443419615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4330001614175403849118973 1623750605315776443419615)
                      ·
                        rfl

theorem cell23_3162243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 3].length) (baseStart_3162243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162243 prefixEnd_3162243 := by exact prefixLift 3162243
  have htrace : WordTrace (prefixWord ++ tailWord_3162243) baseStart_3162243 baseEnd_3162243 := by
    simpa [prefixWord, tailWord_3162243, baseEnd_3162243] using wordTrace_append hprefix tailTrace_3162243
  have hstable : (prefixWord ++ tailWord_3162243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162243).length < 2 ^ (prefixWord ++ tailWord_3162243).sum := by decide
  have hdescent : baseEnd_3162243 < baseStart_3162243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162244 : List Nat := [2, 3, 2, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_3162244 : Nat := 118140960795 + 3162244 * 2 ^ 59
def prefixEnd_3162244 : Nat := 4983230072969 + 3 ^ 40 * 3162244 * 2
def baseEnd_3162244 : Nat := 1623751118796430939507111

theorem tailTrace_3162244 : CollatzResearch.WordTrace tailWord_3162244 prefixEnd_3162244 1623751118796430939507111 := by
  unfold tailWord_3162244
  simp only [CollatzResearch.WordTrace]
  refine ⟨57668256977868765561638893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76891009303825020748851857 57668256977868765561638893)
  ·
    refine ⟨21625596366700787085614585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57668256977868765561638893 21625596366700787085614585)
    ·
      refine ⟨16219197275025590314210939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21625596366700787085614585 16219197275025590314210939)
      ·
        refine ⟨24328795912538385471316409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16219197275025590314210939 24328795912538385471316409)
        ·
          refine ⟨18246596934403789103487307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24328795912538385471316409 18246596934403789103487307)
          ·
            refine ⟨27369895401605683655230961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18246596934403789103487307 27369895401605683655230961)
            ·
              refine ⟨20527421551204262741423221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27369895401605683655230961 20527421551204262741423221)
              ·
                refine ⟨1924445770425399632008427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20527421551204262741423221 1924445770425399632008427)
                ·
                  refine ⟨2886668655638099448012641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924445770425399632008427 2886668655638099448012641)
                  ·
                    refine ⟨2165001491728574586009481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2886668655638099448012641 2165001491728574586009481)
                    ·
                      refine ⟨1623751118796430939507111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165001491728574586009481 1623751118796430939507111)
                      ·
                        rfl

theorem cell23_3162244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_3162244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162244 prefixEnd_3162244 := by exact prefixLift 3162244
  have htrace : WordTrace (prefixWord ++ tailWord_3162244) baseStart_3162244 baseEnd_3162244 := by
    simpa [prefixWord, tailWord_3162244, baseEnd_3162244] using wordTrace_append hprefix tailTrace_3162244
  have hstable : (prefixWord ++ tailWord_3162244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162244).length < 2 ^ (prefixWord ++ tailWord_3162244).sum := by decide
  have hdescent : baseEnd_3162244 < baseStart_3162244 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162304 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 1, 3, 2]
def baseStart_3162304 : Nat := 118140960795 + 3162304 * 2 ^ 59
def prefixEnd_3162304 : Nat := 4983230072969 + 3 ^ 40 * 3162304 * 2
def baseEnd_3162304 : Nat := 1623781927635700704756835

theorem tailTrace_3162304 : CollatzResearch.WordTrace tailWord_3162304 prefixEnd_3162304 1623781927635700704756835 := by
  unfold tailWord_3162304
  simp only [CollatzResearch.WordTrace]
  refine ⟨57669351167760080685230983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76892468223680107580307977 57669351167760080685230983)
  ·
    refine ⟨86504026751640121027846475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57669351167760080685230983 86504026751640121027846475)
    ·
      refine ⟨129756040127460181541769713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86504026751640121027846475 129756040127460181541769713)
      ·
        refine ⟨97317030095595136156327285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129756040127460181541769713 97317030095595136156327285)
        ·
          refine ⟨9123471571462044014655683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 97317030095595136156327285 9123471571462044014655683)
          ·
            refine ⟨13685207357193066021983525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9123471571462044014655683 13685207357193066021983525)
            ·
              refine ⟨2565976379473699879121911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13685207357193066021983525 2565976379473699879121911)
              ·
                refine ⟨3848964569210549818682867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2565976379473699879121911 3848964569210549818682867)
                ·
                  refine ⟨5773446853815824728024301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3848964569210549818682867 5773446853815824728024301)
                  ·
                    refine ⟨2165042570180934273009113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5773446853815824728024301 2165042570180934273009113)
                    ·
                      refine ⟨1623781927635700704756835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165042570180934273009113 1623781927635700704756835)
                      ·
                        rfl

theorem cell23_3162304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 1, 3, 2].length) (baseStart_3162304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162304 prefixEnd_3162304 := by exact prefixLift 3162304
  have htrace : WordTrace (prefixWord ++ tailWord_3162304) baseStart_3162304 baseEnd_3162304 := by
    simpa [prefixWord, tailWord_3162304, baseEnd_3162304] using wordTrace_append hprefix tailTrace_3162304
  have hstable : (prefixWord ++ tailWord_3162304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162304).length < 2 ^ (prefixWord ++ tailWord_3162304).sum := by decide
  have hdescent : baseEnd_3162304 < baseStart_3162304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162353 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 1, 7]
def baseStart_3162353 : Nat := 118140960795 + 3162353 * 2 ^ 59
def prefixEnd_3162353 : Nat := 4983230072969 + 3 ^ 40 * 3162353 * 2
def baseEnd_3162353 : Nat := 541269029395923671014703

theorem tailTrace_3162353 : CollatzResearch.WordTrace tailWord_3162353 prefixEnd_3162353 541269029395923671014703 := by
  unfold tailWord_3162353
  simp only [CollatzResearch.WordTrace]
  refine ⟨115340489512342642738995713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76893659674895095159330475 115340489512342642738995713)
  ·
    refine ⟨86505367134256982054246785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115340489512342642738995713 86505367134256982054246785)
    ·
      refine ⟨64879025350692736540685089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86505367134256982054246785 64879025350692736540685089)
      ·
        refine ⟨48659269013019552405513817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64879025350692736540685089 48659269013019552405513817)
        ·
          refine ⟨36494451759764664304135363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48659269013019552405513817 36494451759764664304135363)
          ·
            refine ⟨54741677639646996456203045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36494451759764664304135363 54741677639646996456203045)
            ·
              refine ⟨10264064557433811835538071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54741677639646996456203045 10264064557433811835538071)
              ·
                refine ⟨15396096836150717753307107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10264064557433811835538071 15396096836150717753307107)
                ·
                  refine ⟨23094145254226076629960661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15396096836150717753307107 23094145254226076629960661)
                  ·
                    refine ⟨541269029395923671014703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23094145254226076629960661 541269029395923671014703)
                    ·
                      rfl

theorem cell23_3162353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 7].length) (baseStart_3162353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162353 prefixEnd_3162353 := by exact prefixLift 3162353
  have htrace : WordTrace (prefixWord ++ tailWord_3162353) baseStart_3162353 baseEnd_3162353 := by
    simpa [prefixWord, tailWord_3162353, baseEnd_3162353] using wordTrace_append hprefix tailTrace_3162353
  have hstable : (prefixWord ++ tailWord_3162353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162353).length < 2 ^ (prefixWord ++ tailWord_3162353).sum := by decide
  have hdescent : baseEnd_3162353 < baseStart_3162353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162373 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 4]
def baseStart_3162373 : Nat := 118140960795 + 3162373 * 2 ^ 59
def prefixEnd_3162373 : Nat := 4983230072969 + 3 ^ 40 * 3162373 * 2
def baseEnd_3162373 : Nat := 1623817357800860934794017

theorem tailTrace_3162373 : CollatzResearch.WordTrace tailWord_3162373 prefixEnd_3162373 1623817357800860934794017 := by
  unfold tailWord_3162373
  simp only [CollatzResearch.WordTrace]
  refine ⟨115341218972270186154723773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76894145981513457436482515 115341218972270186154723773)
  ·
    refine ⟨43252957114601319808021415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115341218972270186154723773 43252957114601319808021415)
    ·
      refine ⟨64879435671901979712032123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43252957114601319808021415 64879435671901979712032123)
      ·
        refine ⟨97319153507852969568048185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64879435671901979712032123 97319153507852969568048185)
        ·
          refine ⟨72989365130889727176036139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97319153507852969568048185 72989365130889727176036139)
          ·
            refine ⟨109484047696334590764054209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72989365130889727176036139 109484047696334590764054209)
            ·
              refine ⟨82113035772250943073040657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109484047696334590764054209 82113035772250943073040657)
              ·
                refine ⟨61584776829188207304780493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82113035772250943073040657 61584776829188207304780493)
                ·
                  refine ⟨23094291310945577739292685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61584776829188207304780493 23094291310945577739292685)
                  ·
                    refine ⟨8660359241604591652234757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23094291310945577739292685 8660359241604591652234757)
                    ·
                      refine ⟨1623817357800860934794017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8660359241604591652234757 1623817357800860934794017)
                      ·
                        rfl

theorem cell23_3162373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_3162373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162373 prefixEnd_3162373 := by exact prefixLift 3162373
  have htrace : WordTrace (prefixWord ++ tailWord_3162373) baseStart_3162373 baseEnd_3162373 := by
    simpa [prefixWord, tailWord_3162373, baseEnd_3162373] using wordTrace_append hprefix tailTrace_3162373
  have hstable : (prefixWord ++ tailWord_3162373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162373).length < 2 ^ (prefixWord ++ tailWord_3162373).sum := by decide
  have hdescent : baseEnd_3162373 < baseStart_3162373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162467 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 1, 5, 2]
def baseStart_3162467 : Nat := 118140960795 + 3162467 * 2 ^ 59
def prefixEnd_3162467 : Nat := 4983230072969 + 3 ^ 40 * 3162467 * 2
def baseEnd_3162467 : Nat := 1623865624982383567018585

theorem tailTrace_3162467 : CollatzResearch.WordTrace tailWord_3162467 prefixEnd_3162467 1623865624982383567018585 := by
  unfold tailWord_3162467
  simp only [CollatzResearch.WordTrace]
  refine ⟨115344647433929640208645655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76896431622619760139097103 115344647433929640208645655)
  ·
    refine ⟨173016971150894460312968483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115344647433929640208645655 173016971150894460312968483)
    ·
      refine ⟨259525456726341690469452725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173016971150894460312968483 259525456726341690469452725)
      ·
        refine ⟨24330511568094533481511193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 259525456726341690469452725 24330511568094533481511193)
        ·
          refine ⟨18247883676070900111133395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24330511568094533481511193 18247883676070900111133395)
          ·
            refine ⟨27371825514106350166700093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18247883676070900111133395 27371825514106350166700093)
            ·
              refine ⟨10264434567789881312512535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27371825514106350166700093 10264434567789881312512535)
              ·
                refine ⟨15396651851684821968768803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10264434567789881312512535 15396651851684821968768803)
                ·
                  refine ⟨23094977777527232953153205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15396651851684821968768803 23094977777527232953153205)
                  ·
                    refine ⟨2165154166643178089358113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23094977777527232953153205 2165154166643178089358113)
                    ·
                      refine ⟨1623865624982383567018585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165154166643178089358113 1623865624982383567018585)
                      ·
                        rfl

theorem cell23_3162467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_3162467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162467 prefixEnd_3162467 := by exact prefixLift 3162467
  have htrace : WordTrace (prefixWord ++ tailWord_3162467) baseStart_3162467 baseEnd_3162467 := by
    simpa [prefixWord, tailWord_3162467, baseEnd_3162467] using wordTrace_append hprefix tailTrace_3162467
  have hstable : (prefixWord ++ tailWord_3162467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162467).length < 2 ^ (prefixWord ++ tailWord_3162467).sum := by decide
  have hdescent : baseEnd_3162467 < baseStart_3162467 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162477 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 1, 5]
def baseStart_3162477 : Nat := 118140960795 + 3162477 * 2 ^ 59
def prefixEnd_3162477 : Nat := 4983230072969 + 3 ^ 40 * 3162477 * 2
def baseEnd_3162477 : Nat := 541290253262976175964513

theorem tailTrace_3162477 : CollatzResearch.WordTrace tailWord_3162477 prefixEnd_3162477 541290253262976175964513 := by
  unfold tailWord_3162477
  simp only [CollatzResearch.WordTrace]
  refine ⟨115345012163893411916509685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76896674775928941277673123 115345012163893411916509685)
  ·
    refine ⟨10813594890365007367172783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 115345012163893411916509685 10813594890365007367172783)
    ·
      refine ⟨16220392335547511050759175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10813594890365007367172783 16220392335547511050759175)
      ·
        refine ⟨24330588503321266576138763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16220392335547511050759175 24330588503321266576138763)
        ·
          refine ⟨36495882754981899864208145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24330588503321266576138763 36495882754981899864208145)
          ·
            refine ⟨27371912066236424898156109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36495882754981899864208145 27371912066236424898156109)
            ·
              refine ⟨10264467024838659336808541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27371912066236424898156109 10264467024838659336808541)
              ·
                refine ⟨3849175134314497251303203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10264467024838659336808541 3849175134314497251303203)
                ·
                  refine ⟨5773762701471745876954805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3849175134314497251303203 5773762701471745876954805)
                  ·
                    refine ⟨541290253262976175964513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5773762701471745876954805 541290253262976175964513)
                    ·
                      rfl

theorem cell23_3162477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_3162477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162477 prefixEnd_3162477 := by exact prefixLift 3162477
  have htrace : WordTrace (prefixWord ++ tailWord_3162477) baseStart_3162477 baseEnd_3162477 := by
    simpa [prefixWord, tailWord_3162477, baseEnd_3162477] using wordTrace_append hprefix tailTrace_3162477
  have hstable : (prefixWord ++ tailWord_3162477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162477).length < 2 ^ (prefixWord ++ tailWord_3162477).sum := by decide
  have hdescent : baseEnd_3162477 < baseStart_3162477 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162507 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 1, 6]
def baseStart_3162507 : Nat := 118140960795 + 3162507 * 2 ^ 59
def prefixEnd_3162507 : Nat := 4983230072969 + 3 ^ 40 * 3162507 * 2
def baseEnd_3162507 : Nat := 541295388069521136839467

theorem tailTrace_3162507 : CollatzResearch.WordTrace tailWord_3162507 prefixEnd_3162507 541295388069521136839467 := by
  unfold tailWord_3162507
  simp only [CollatzResearch.WordTrace]
  refine ⟨115346106353784727040101775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76897404235856484693401183 115346106353784727040101775)
  ·
    refine ⟨173019159530677090560152663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115346106353784727040101775 173019159530677090560152663)
    ·
      refine ⟨259528739296015635840228995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173019159530677090560152663 259528739296015635840228995)
      ·
        refine ⟨389293108944023453760343493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259528739296015635840228995 389293108944023453760343493)
        ·
          refine ⟨72992457927004397580064405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 389293108944023453760343493 72992457927004397580064405)
          ·
            refine ⟨3421521465328331136565519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72992457927004397580064405 3421521465328331136565519)
            ·
              refine ⟨5132282197992496704848279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421521465328331136565519 5132282197992496704848279)
              ·
                refine ⟨7698423296988745057272419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5132282197992496704848279 7698423296988745057272419)
                ·
                  refine ⟨11547634945483117585908629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7698423296988745057272419 11547634945483117585908629)
                  ·
                    refine ⟨541295388069521136839467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11547634945483117585908629 541295388069521136839467)
                    ·
                      rfl

theorem cell23_3162507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 6].length) (baseStart_3162507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162507 prefixEnd_3162507 := by exact prefixLift 3162507
  have htrace : WordTrace (prefixWord ++ tailWord_3162507) baseStart_3162507 baseEnd_3162507 := by
    simpa [prefixWord, tailWord_3162507, baseEnd_3162507] using wordTrace_append hprefix tailTrace_3162507
  have hstable : (prefixWord ++ tailWord_3162507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162507).length < 2 ^ (prefixWord ++ tailWord_3162507).sum := by decide
  have hdescent : baseEnd_3162507 < baseStart_3162507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162525 : List Nat := [1, 4, 2, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_3162525 : Nat := 118140960795 + 3162525 * 2 ^ 59
def prefixEnd_3162525 : Nat := 4983230072969 + 3 ^ 40 * 3162525 * 2
def baseEnd_3162525 : Nat := 1623895406860344340093319

theorem tailTrace_3162525 : CollatzResearch.WordTrace tailWord_3162525 prefixEnd_3162525 1623895406860344340093319 := by
  unfold tailWord_3162525
  simp only [CollatzResearch.WordTrace]
  refine ⟨115346762867719516114257029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76897841911813010742838019 115346762867719516114257029)
  ·
    refine ⟨21627518037697409271423193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115346762867719516114257029 21627518037697409271423193)
    ·
      refine ⟨16220638528273056953567395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21627518037697409271423193 16220638528273056953567395)
      ·
        refine ⟨24330957792409585430351093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16220638528273056953567395 24330957792409585430351093)
        ·
          refine ⟨2281027293038398634095415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24330957792409585430351093 2281027293038398634095415)
          ·
            refine ⟨3421540939557597951143123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281027293038398634095415 3421540939557597951143123)
            ·
              refine ⟨5132311409336396926714685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421540939557597951143123 5132311409336396926714685)
              ·
                refine ⟨1924616778501148847518007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5132311409336396926714685 1924616778501148847518007)
                ·
                  refine ⟨2886925167751723271277011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924616778501148847518007 2886925167751723271277011)
                  ·
                    refine ⟨4330387751627584906915517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2886925167751723271277011 4330387751627584906915517)
                    ·
                      refine ⟨1623895406860344340093319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4330387751627584906915517 1623895406860344340093319)
                      ·
                        rfl

theorem cell23_3162525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_3162525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162525 prefixEnd_3162525 := by exact prefixLift 3162525
  have htrace : WordTrace (prefixWord ++ tailWord_3162525) baseStart_3162525 baseEnd_3162525 := by
    simpa [prefixWord, tailWord_3162525, baseEnd_3162525] using wordTrace_append hprefix tailTrace_3162525
  have hstable : (prefixWord ++ tailWord_3162525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162525).length < 2 ^ (prefixWord ++ tailWord_3162525).sum := by decide
  have hdescent : baseEnd_3162525 < baseStart_3162525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162621 : List Nat := [1, 4, 1, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_3162621 : Nat := 118140960795 + 3162621 * 2 ^ 59
def prefixEnd_3162621 : Nat := 4983230072969 + 3 ^ 40 * 3162621 * 2
def baseEnd_3162621 : Nat := 1623944701003175964492877

theorem tailTrace_3162621 : CollatzResearch.WordTrace tailWord_3162621 prefixEnd_3162621 1623944701003175964492877 := by
  unfold tailWord_3162621
  simp only [CollatzResearch.WordTrace]
  refine ⟨115350264275371724509751717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76900176183581149673167811 115350264275371724509751717)
  ·
    refine ⟨21628174551632198345578447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 115350264275371724509751717 21628174551632198345578447)
    ·
      refine ⟨32442261827448297518367671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21628174551632198345578447 32442261827448297518367671)
      ·
        refine ⟨48663392741172446277551507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32442261827448297518367671 48663392741172446277551507)
        ·
          refine ⟨72995089111758669416327261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48663392741172446277551507 72995089111758669416327261)
          ·
            refine ⟨27373158416909501031122723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72995089111758669416327261 27373158416909501031122723)
            ·
              refine ⟨41059737625364251546684085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27373158416909501031122723 41059737625364251546684085)
              ·
                refine ⟨3849350402377898582501633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41059737625364251546684085 3849350402377898582501633)
                ·
                  refine ⟨2887012801783423936876225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3849350402377898582501633 2887012801783423936876225)
                  ·
                    refine ⟨2165259601337567952657169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2887012801783423936876225 2165259601337567952657169)
                    ·
                      refine ⟨1623944701003175964492877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165259601337567952657169 1623944701003175964492877)
                      ·
                        rfl

theorem cell23_3162621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_3162621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162621 prefixEnd_3162621 := by exact prefixLift 3162621
  have htrace : WordTrace (prefixWord ++ tailWord_3162621) baseStart_3162621 baseEnd_3162621 := by
    simpa [prefixWord, tailWord_3162621, baseEnd_3162621] using wordTrace_append hprefix tailTrace_3162621
  have hstable : (prefixWord ++ tailWord_3162621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162621).length < 2 ^ (prefixWord ++ tailWord_3162621).sum := by decide
  have hdescent : baseEnd_3162621 < baseStart_3162621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162657 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3162657 : Nat := 118140960795 + 3162657 * 2 ^ 59
def prefixEnd_3162657 : Nat := 4983230072969 + 3 ^ 40 * 3162657 * 2
def baseEnd_3162657 : Nat := 541321062102245941214237

theorem tailTrace_3162657 : CollatzResearch.WordTrace tailWord_3162657 prefixEnd_3162657 541321062102245941214237 := by
  unfold tailWord_3162657
  simp only [CollatzResearch.WordTrace]
  refine ⟨115351577303241302658062225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76901051535494201772041483 115351577303241302658062225)
  ·
    refine ⟨86513682977430976993546669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115351577303241302658062225 86513682977430976993546669)
    ·
      refine ⟨32442631116536616372580001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86513682977430976993546669 32442631116536616372580001)
      ·
        refine ⟨24331973337402462279435001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32442631116536616372580001 24331973337402462279435001)
        ·
          refine ⟨18248980003051846709576251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24331973337402462279435001 18248980003051846709576251)
          ·
            refine ⟨27373470004577770064364377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18248980003051846709576251 27373470004577770064364377)
            ·
              refine ⟨20530102503433327548273283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27373470004577770064364377 20530102503433327548273283)
              ·
                refine ⟨30795153755149991322409925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20530102503433327548273283 30795153755149991322409925)
                ·
                  refine ⟨5774091329090623372951861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30795153755149991322409925 5774091329090623372951861)
                  ·
                    refine ⟨541321062102245941214237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5774091329090623372951861 541321062102245941214237)
                    ·
                      rfl

theorem cell23_3162657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3162657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162657 prefixEnd_3162657 := by exact prefixLift 3162657
  have htrace : WordTrace (prefixWord ++ tailWord_3162657) baseStart_3162657 baseEnd_3162657 := by
    simpa [prefixWord, tailWord_3162657, baseEnd_3162657] using wordTrace_append hprefix tailTrace_3162657
  have hstable : (prefixWord ++ tailWord_3162657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162657).length < 2 ^ (prefixWord ++ tailWord_3162657).sum := by decide
  have hdescent : baseEnd_3162657 < baseStart_3162657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162677 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_3162677 : Nat := 118140960795 + 3162677 * 2 ^ 59
def prefixEnd_3162677 : Nat := 4983230072969 + 3 ^ 40 * 3162677 * 2
def baseEnd_3162677 : Nat := 1623973455919827745392619

theorem tailTrace_3162677 : CollatzResearch.WordTrace tailWord_3162677 prefixEnd_3162677 1623973455919827745392619 := by
  unfold tailWord_3162677
  simp only [CollatzResearch.WordTrace]
  refine ⟨115352306763168846073790285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76901537842112564049193523 115352306763168846073790285)
  ·
    refine ⟨43257115036188317277671357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115352306763168846073790285 43257115036188317277671357)
    ·
      refine ⟨16221418138570618979126759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43257115036188317277671357 16221418138570618979126759)
      ·
        refine ⟨24332127207855928468690139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16221418138570618979126759 24332127207855928468690139)
        ·
          refine ⟨36498190811783892703035209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24332127207855928468690139 36498190811783892703035209)
          ·
            refine ⟨27373643108837919527276407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36498190811783892703035209 27373643108837919527276407)
            ·
              refine ⟨41060464663256879290914611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27373643108837919527276407 41060464663256879290914611)
              ·
                refine ⟨61590696994885318936371917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41060464663256879290914611 61590696994885318936371917)
                ·
                  refine ⟨23096511373081994601139469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61590696994885318936371917 23096511373081994601139469)
                  ·
                    refine ⟨8661191764905747975427301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23096511373081994601139469 8661191764905747975427301)
                    ·
                      refine ⟨1623973455919827745392619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8661191764905747975427301 1623973455919827745392619)
                      ·
                        rfl

theorem cell23_3162677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_3162677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162677 prefixEnd_3162677 := by exact prefixLift 3162677
  have htrace : WordTrace (prefixWord ++ tailWord_3162677) baseStart_3162677 baseEnd_3162677 := by
    simpa [prefixWord, tailWord_3162677, baseEnd_3162677] using wordTrace_append hprefix tailTrace_3162677
  have hstable : (prefixWord ++ tailWord_3162677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162677).length < 2 ^ (prefixWord ++ tailWord_3162677).sum := by decide
  have hdescent : baseEnd_3162677 < baseStart_3162677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162721 : List Nat := [1, 2, 3, 1, 1, 6, 1, 1, 3, 4]
def baseStart_3162721 : Nat := 118140960795 + 3162721 * 2 ^ 59
def prefixEnd_3162721 : Nat := 4983230072969 + 3 ^ 40 * 3162721 * 2
def baseEnd_3162721 : Nat := 541332016356208524414139

theorem tailTrace_3162721 : CollatzResearch.WordTrace tailWord_3162721 prefixEnd_3162721 541332016356208524414139 := by
  unfold tailWord_3162721
  simp only [CollatzResearch.WordTrace]
  refine ⟨115353911575009441588392017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76902607716672961058928011 115353911575009441588392017)
  ·
    refine ⟨86515433681257081191294013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115353911575009441588392017 86515433681257081191294013)
    ·
      refine ⟨32443287630471405446735255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86515433681257081191294013 32443287630471405446735255)
      ·
        refine ⟨48664931445707108170102883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32443287630471405446735255 48664931445707108170102883)
        ·
          refine ⟨72997397168560662255154325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48664931445707108170102883 72997397168560662255154325)
          ·
            refine ⟨3421752992276281043210359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 72997397168560662255154325 3421752992276281043210359)
            ·
              refine ⟨5132629488414421564815539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421752992276281043210359 5132629488414421564815539)
              ·
                refine ⟨7698944232621632347223309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5132629488414421564815539 7698944232621632347223309)
                ·
                  refine ⟨2887104087233112130208741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7698944232621632347223309 2887104087233112130208741)
                  ·
                    refine ⟨541332016356208524414139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887104087233112130208741 541332016356208524414139)
                    ·
                      rfl

theorem cell23_3162721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_3162721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162721 prefixEnd_3162721 := by exact prefixLift 3162721
  have htrace : WordTrace (prefixWord ++ tailWord_3162721) baseStart_3162721 baseEnd_3162721 := by
    simpa [prefixWord, tailWord_3162721, baseEnd_3162721] using wordTrace_append hprefix tailTrace_3162721
  have hstable : (prefixWord ++ tailWord_3162721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162721).length < 2 ^ (prefixWord ++ tailWord_3162721).sum := by decide
  have hdescent : baseEnd_3162721 < baseStart_3162721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162772 : List Nat := [2, 4, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_3162772 : Nat := 118140960795 + 3162772 * 2 ^ 59
def prefixEnd_3162772 : Nat := 4983230072969 + 3 ^ 40 * 3162772 * 2
def baseEnd_3162772 : Nat := 541340745527334957901561

theorem tailTrace_3162772 : CollatzResearch.WordTrace tailWord_3162772 prefixEnd_3162772 541340745527334957901561 := by
  unfold tailWord_3162772
  simp only [CollatzResearch.WordTrace]
  refine ⟨57677885848912338649249285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76903847798549784865665713 57677885848912338649249285)
  ·
    refine ⟨10814603596671063496734241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57677885848912338649249285 10814603596671063496734241)
    ·
      refine ⟨8110952697503297622550681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10814603596671063496734241 8110952697503297622550681)
      ·
        refine ⟨6083214523127473216913011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8110952697503297622550681 6083214523127473216913011)
        ·
          refine ⟨9124821784691209825369517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083214523127473216913011 9124821784691209825369517)
          ·
            refine ⟨3421808169259203684513569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9124821784691209825369517 3421808169259203684513569)
            ·
              refine ⟨2566356126944402763385177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421808169259203684513569 2566356126944402763385177)
              ·
                refine ⟨1924767095208302072538883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566356126944402763385177 1924767095208302072538883)
                ·
                  refine ⟨2887150642812453108808325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924767095208302072538883 2887150642812453108808325)
                  ·
                    refine ⟨541340745527334957901561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887150642812453108808325 541340745527334957901561)
                    ·
                      rfl

theorem cell23_3162772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_3162772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162772 prefixEnd_3162772 := by exact prefixLift 3162772
  have htrace : WordTrace (prefixWord ++ tailWord_3162772) baseStart_3162772 baseEnd_3162772 := by
    simpa [prefixWord, tailWord_3162772, baseEnd_3162772] using wordTrace_append hprefix tailTrace_3162772
  have hstable : (prefixWord ++ tailWord_3162772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162772).length < 2 ^ (prefixWord ++ tailWord_3162772).sum := by decide
  have hdescent : baseEnd_3162772 < baseStart_3162772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162777 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 3, 6]
def baseStart_3162777 : Nat := 118140960795 + 3162777 * 2 ^ 59
def prefixEnd_3162777 : Nat := 4983230072969 + 3 ^ 40 * 3162777 * 2
def baseEnd_3162777 : Nat := 541341601328425784714053

theorem tailTrace_3162777 : CollatzResearch.WordTrace tailWord_3162777 prefixEnd_3162777 541341601328425784714053 := by
  unfold tailWord_3162777
  simp only [CollatzResearch.WordTrace]
  refine ⟨115355954062806563152430585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76903969375204375434953723 115355954062806563152430585)
  ·
    refine ⟨86516965547104922364322939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115355954062806563152430585 86516965547104922364322939)
    ·
      refine ⟨129775448320657383546484409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86516965547104922364322939 129775448320657383546484409)
      ·
        refine ⟨97331586240493037659863307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129775448320657383546484409 97331586240493037659863307)
        ·
          refine ⟨145997379360739556489794961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97331586240493037659863307 145997379360739556489794961)
          ·
            refine ⟨109498034520554667367346221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145997379360739556489794961 109498034520554667367346221)
            ·
              refine ⟨41061762945208000262754833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109498034520554667367346221 41061762945208000262754833)
              ·
                refine ⟨30796322208906000197066125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41061762945208000262754833 30796322208906000197066125)
                ·
                  refine ⟨11548620828339750073899797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30796322208906000197066125 11548620828339750073899797)
                  ·
                    refine ⟨541341601328425784714053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11548620828339750073899797 541341601328425784714053)
                    ·
                      rfl

theorem cell23_3162777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 6].length) (baseStart_3162777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162777 prefixEnd_3162777 := by exact prefixLift 3162777
  have htrace : WordTrace (prefixWord ++ tailWord_3162777) baseStart_3162777 baseEnd_3162777 := by
    simpa [prefixWord, tailWord_3162777, baseEnd_3162777] using wordTrace_append hprefix tailTrace_3162777
  have hstable : (prefixWord ++ tailWord_3162777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162777).length < 2 ^ (prefixWord ++ tailWord_3162777).sum := by decide
  have hdescent : baseEnd_3162777 < baseStart_3162777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162805 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 2, 3, 2]
def baseStart_3162805 : Nat := 118140960795 + 3162805 * 2 ^ 59
def prefixEnd_3162805 : Nat := 4983230072969 + 3 ^ 40 * 3162805 * 2
def baseEnd_3162805 : Nat := 1624039181443603244592031

theorem tailTrace_3162805 : CollatzResearch.WordTrace tailWord_3162805 prefixEnd_3162805 1624039181443603244592031 := by
  unfold tailWord_3162805
  simp only [CollatzResearch.WordTrace]
  refine ⟨115356975306705123934449869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76904650204470082622966579 115356975306705123934449869)
  ·
    refine ⟨43258865740014421475418701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115356975306705123934449869 43258865740014421475418701)
    ·
      refine ⟨16222074652505408053282013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43258865740014421475418701 16222074652505408053282013)
      ·
        refine ⟨6083277994689528019980755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16222074652505408053282013 6083277994689528019980755)
        ·
          refine ⟨9124916992034292029971133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083277994689528019980755 9124916992034292029971133)
          ·
            refine ⟨3421843872012859511239175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9124916992034292029971133 3421843872012859511239175)
            ·
              refine ⟨5132765808019289266858763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421843872012859511239175 5132765808019289266858763)
              ·
                refine ⟨7699148712028933900288145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5132765808019289266858763 7699148712028933900288145)
                ·
                  refine ⟨5774361534021700425216109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7699148712028933900288145 5774361534021700425216109)
                  ·
                    refine ⟨2165385575258137659456041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5774361534021700425216109 2165385575258137659456041)
                    ·
                      refine ⟨1624039181443603244592031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165385575258137659456041 1624039181443603244592031)
                      ·
                        rfl

theorem cell23_3162805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_3162805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162805 prefixEnd_3162805 := by exact prefixLift 3162805
  have htrace : WordTrace (prefixWord ++ tailWord_3162805) baseStart_3162805 baseEnd_3162805 := by
    simpa [prefixWord, tailWord_3162805, baseEnd_3162805] using wordTrace_append hprefix tailTrace_3162805
  have hstable : (prefixWord ++ tailWord_3162805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162805).length < 2 ^ (prefixWord ++ tailWord_3162805).sum := by decide
  have hdescent : baseEnd_3162805 < baseStart_3162805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162827 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_3162827 : Nat := 118140960795 + 3162827 * 2 ^ 59
def prefixEnd_3162827 : Nat := 4983230072969 + 3 ^ 40 * 3162827 * 2
def baseEnd_3162827 : Nat := 1624050478018002158516929

theorem tailTrace_3162827 : CollatzResearch.WordTrace tailWord_3162827 prefixEnd_3162827 1624050478018002158516929 := by
  unfold tailWord_3162827
  simp only [CollatzResearch.WordTrace]
  refine ⟨115357777712625421691750735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76905185141750281127833823 115357777712625421691750735)
  ·
    refine ⟨173036666568938132537626103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115357777712625421691750735 173036666568938132537626103)
    ·
      refine ⟨259554999853407198806439155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173036666568938132537626103 259554999853407198806439155)
      ·
        refine ⟨389332499780110798209658733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259554999853407198806439155 389332499780110798209658733)
        ·
          refine ⟨145999687417541549328622025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389332499780110798209658733 145999687417541549328622025)
          ·
            refine ⟨109499765563156161996466519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145999687417541549328622025 109499765563156161996466519)
            ·
              refine ⟨164249648344734242994699779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109499765563156161996466519 164249648344734242994699779)
              ·
                refine ⟨246374472517101364492049669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164249648344734242994699779 246374472517101364492049669)
                ·
                  refine ⟨46195213596956505842259313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 246374472517101364492049669 46195213596956505842259313)
                  ·
                    refine ⟨34646410197717379381694485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46195213596956505842259313 34646410197717379381694485)
                    ·
                      refine ⟨1624050478018002158516929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34646410197717379381694485 1624050478018002158516929)
                      ·
                        rfl

theorem cell23_3162827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_3162827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162827 prefixEnd_3162827 := by exact prefixLift 3162827
  have htrace : WordTrace (prefixWord ++ tailWord_3162827) baseStart_3162827 baseEnd_3162827 := by
    simpa [prefixWord, tailWord_3162827, baseEnd_3162827] using wordTrace_append hprefix tailTrace_3162827
  have hstable : (prefixWord ++ tailWord_3162827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162827).length < 2 ^ (prefixWord ++ tailWord_3162827).sum := by decide
  have hdescent : baseEnd_3162827 < baseStart_3162827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162828 : List Nat := [2, 2, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_3162828 : Nat := 118140960795 + 3162828 * 2 ^ 59
def prefixEnd_3162828 : Nat := 4983230072969 + 3 ^ 40 * 3162828 * 2
def baseEnd_3162828 : Nat := 541350330499552218201475

theorem tailTrace_3162828 : CollatzResearch.WordTrace tailWord_3162828 prefixEnd_3162828 541350330499552218201475 := by
  unfold tailWord_3162828
  simp only [CollatzResearch.WordTrace]
  refine ⟨57678907092810899431268569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76905209457081199241691425 57678907092810899431268569)
  ·
    refine ⟨43259180319608174573451427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57678907092810899431268569 43259180319608174573451427)
    ·
      refine ⟨64888770479412261860177141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43259180319608174573451427 64888770479412261860177141)
      ·
        refine ⟨6083322232444899549391607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64888770479412261860177141 6083322232444899549391607)
        ·
          refine ⟨9124983348667349324087411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083322232444899549391607 9124983348667349324087411)
          ·
            refine ⟨13687475023001023986131117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9124983348667349324087411 13687475023001023986131117)
            ·
              refine ⟨5132803133625383994799169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13687475023001023986131117 5132803133625383994799169)
              ·
                refine ⟨3849602350219037996099377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5132803133625383994799169 3849602350219037996099377)
                ·
                  refine ⟨2887201762664278497074533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3849602350219037996099377 2887201762664278497074533)
                  ·
                    refine ⟨541350330499552218201475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887201762664278497074533 541350330499552218201475)
                    ·
                      rfl

theorem cell23_3162828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_3162828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162828 prefixEnd_3162828 := by exact prefixLift 3162828
  have htrace : WordTrace (prefixWord ++ tailWord_3162828) baseStart_3162828 baseEnd_3162828 := by
    simpa [prefixWord, tailWord_3162828, baseEnd_3162828] using wordTrace_append hprefix tailTrace_3162828
  have hstable : (prefixWord ++ tailWord_3162828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162828).length < 2 ^ (prefixWord ++ tailWord_3162828).sum := by decide
  have hdescent : baseEnd_3162828 < baseStart_3162828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162894 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_3162894 : Nat := 118140960795 + 3162894 * 2 ^ 59
def prefixEnd_3162894 : Nat := 4983230072969 + 3 ^ 40 * 3162894 * 2
def baseEnd_3162894 : Nat := 1624084881221853396379121

theorem tailTrace_3162894 : CollatzResearch.WordTrace tailWord_3162894 prefixEnd_3162894 1624084881221853396379121 := by
  unfold tailWord_3162894
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420027675422836516804967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76906814268921794756293157 14420027675422836516804967)
  ·
    refine ⟨21630041513134254775207451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14420027675422836516804967 21630041513134254775207451)
    ·
      refine ⟨32445062269701382162811177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21630041513134254775207451 32445062269701382162811177)
      ·
        refine ⟨24333796702276036622108383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32445062269701382162811177 24333796702276036622108383)
        ·
          refine ⟨36500695053414054933162575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24333796702276036622108383 36500695053414054933162575)
          ·
            refine ⟨54751042580121082399743863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36500695053414054933162575 54751042580121082399743863)
            ·
              refine ⟨82126563870181623599615795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54751042580121082399743863 82126563870181623599615795)
              ·
                refine ⟨123189845805272435399423693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82126563870181623599615795 123189845805272435399423693)
                ·
                  refine ⟨46196192176977163274783885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 123189845805272435399423693 46196192176977163274783885)
                  ·
                    refine ⟨17323572066366436228043957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46196192176977163274783885 17323572066366436228043957)
                    ·
                      refine ⟨1624084881221853396379121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17323572066366436228043957 1624084881221853396379121)
                      ·
                        rfl

theorem cell23_3162894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_3162894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162894 prefixEnd_3162894 := by exact prefixLift 3162894
  have htrace : WordTrace (prefixWord ++ tailWord_3162894) baseStart_3162894 baseEnd_3162894 := by
    simpa [prefixWord, tailWord_3162894, baseEnd_3162894] using wordTrace_append hprefix tailTrace_3162894
  have hstable : (prefixWord ++ tailWord_3162894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162894).length < 2 ^ (prefixWord ++ tailWord_3162894).sum := by decide
  have hdescent : baseEnd_3162894 < baseStart_3162894 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162904 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3162904 : Nat := 118140960795 + 3162904 * 2 ^ 59
def prefixEnd_3162904 : Nat := 4983230072969 + 3 ^ 40 * 3162904 * 2
def baseEnd_3162904 : Nat := 1624090016028398357254075

theorem tailTrace_3162904 : CollatzResearch.WordTrace tailWord_3162904 prefixEnd_3162904 1624090016028398357254075 := by
  unfold tailWord_3162904
  simp only [CollatzResearch.WordTrace]
  refine ⟨57680293066673231921151883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76907057422230975894869177 57680293066673231921151883)
  ·
    refine ⟨86520439600009847881727825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57680293066673231921151883 86520439600009847881727825)
    ·
      refine ⟨64890329700007385911295869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86520439600009847881727825 64890329700007385911295869)
      ·
        refine ⟨24333873637502769716735951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64890329700007385911295869 24333873637502769716735951)
        ·
          refine ⟨36500810456254154575103927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24333873637502769716735951 36500810456254154575103927)
          ·
            refine ⟨54751215684381231862655891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36500810456254154575103927 54751215684381231862655891)
            ·
              refine ⟨82126823526571847793983837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54751215684381231862655891 82126823526571847793983837)
              ·
                refine ⟨30797558822464442922743939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82126823526571847793983837 30797558822464442922743939)
                ·
                  refine ⟨46196338233696664384115909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30797558822464442922743939 46196338233696664384115909)
                  ·
                    refine ⟨8661813418818124572021733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46196338233696664384115909 8661813418818124572021733)
                    ·
                      refine ⟨1624090016028398357254075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8661813418818124572021733 1624090016028398357254075)
                      ·
                        rfl

theorem cell23_3162904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3162904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162904 prefixEnd_3162904 := by exact prefixLift 3162904
  have htrace : WordTrace (prefixWord ++ tailWord_3162904) baseStart_3162904 baseEnd_3162904 := by
    simpa [prefixWord, tailWord_3162904, baseEnd_3162904] using wordTrace_append hprefix tailTrace_3162904
  have hstable : (prefixWord ++ tailWord_3162904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162904).length < 2 ^ (prefixWord ++ tailWord_3162904).sum := by decide
  have hdescent : baseEnd_3162904 < baseStart_3162904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162954 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3162954 : Nat := 118140960795 + 3162954 * 2 ^ 59
def prefixEnd_3162954 : Nat := 4983230072969 + 3 ^ 40 * 3162954 * 2
def baseEnd_3162954 : Nat := 1624115690061123161628845

theorem tailTrace_3162954 : CollatzResearch.WordTrace tailWord_3162954 prefixEnd_3162954 1624115690061123161628845 := by
  unfold tailWord_3162954
  simp only [CollatzResearch.WordTrace]
  refine ⟨28840602445791330595405979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76908273188776881587749277 28840602445791330595405979)
  ·
    refine ⟨43260903668686995893108969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28840602445791330595405979 43260903668686995893108969)
    ·
      refine ⟨32445677751515246919831727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43260903668686995893108969 32445677751515246919831727)
      ·
        refine ⟨48668516627272870379747591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32445677751515246919831727 48668516627272870379747591)
        ·
          refine ⟨73002774940909305569621387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48668516627272870379747591 73002774940909305569621387)
          ·
            refine ⟨109504162411363958354432081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73002774940909305569621387 109504162411363958354432081)
            ·
              refine ⟨82128121808522968765824061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109504162411363958354432081 82128121808522968765824061)
              ·
                refine ⟨30798045678196113287184023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82128121808522968765824061 30798045678196113287184023)
                ·
                  refine ⟨46197068517294169930776035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30798045678196113287184023 46197068517294169930776035)
                  ·
                    refine ⟨69295602775941254896164053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46197068517294169930776035 69295602775941254896164053)
                    ·
                      refine ⟨1624115690061123161628845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69295602775941254896164053 1624115690061123161628845)
                      ·
                        rfl

theorem cell23_3162954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3162954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162954 prefixEnd_3162954 := by exact prefixLift 3162954
  have htrace : WordTrace (prefixWord ++ tailWord_3162954) baseStart_3162954 baseEnd_3162954 := by
    simpa [prefixWord, tailWord_3162954, baseEnd_3162954] using wordTrace_append hprefix tailTrace_3162954
  have hstable : (prefixWord ++ tailWord_3162954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162954).length < 2 ^ (prefixWord ++ tailWord_3162954).sum := by decide
  have hdescent : baseEnd_3162954 < baseStart_3162954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3162978 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3162978 : Nat := 118140960795 + 3162978 * 2 ^ 59
def prefixEnd_3162978 : Nat := 4983230072969 + 3 ^ 40 * 3162978 * 2
def baseEnd_3162978 : Nat := 541376004532277022576245

theorem tailTrace_3162978 : CollatzResearch.WordTrace tailWord_3162978 prefixEnd_3162978 541376004532277022576245 := by
  unfold tailWord_3162978
  simp only [CollatzResearch.WordTrace]
  refine ⟨28840821283769593620124397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76908856756718916320331725 28840821283769593620124397)
  ·
    refine ⟨10815307981413597607546649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28840821283769593620124397 10815307981413597607546649)
    ·
      refine ⟨8111480986060198205659987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10815307981413597607546649 8111480986060198205659987)
      ·
        refine ⟨12167221479090297308489981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8111480986060198205659987 12167221479090297308489981)
        ·
          refine ⟨4562708054658861490683743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12167221479090297308489981 4562708054658861490683743)
          ·
            refine ⟨6844062081988292236025615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4562708054658861490683743 6844062081988292236025615)
            ·
              refine ⟨10266093122982438354038423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844062081988292236025615 10266093122982438354038423)
              ·
                refine ⟨15399139684473657531057635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10266093122982438354038423 15399139684473657531057635)
                ·
                  refine ⟨23098709526710486296586453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15399139684473657531057635 23098709526710486296586453)
                  ·
                    refine ⟨541376004532277022576245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23098709526710486296586453 541376004532277022576245)
                    ·
                      rfl

theorem cell23_3162978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3162978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3162978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3162978 prefixEnd_3162978 := by exact prefixLift 3162978
  have htrace : WordTrace (prefixWord ++ tailWord_3162978) baseStart_3162978 baseEnd_3162978 := by
    simpa [prefixWord, tailWord_3162978, baseEnd_3162978] using wordTrace_append hprefix tailTrace_3162978
  have hstable : (prefixWord ++ tailWord_3162978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3162978).length < 2 ^ (prefixWord ++ tailWord_3162978).sum := by decide
  have hdescent : baseEnd_3162978 < baseStart_3162978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3162978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163018 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3163018 : Nat := 118140960795 + 3163018 * 2 ^ 59
def prefixEnd_3163018 : Nat := 4983230072969 + 3 ^ 40 * 3163018 * 2
def baseEnd_3163018 : Nat := 1624148552823010911228551

theorem tailTrace_3163018 : CollatzResearch.WordTrace tailWord_3163018 prefixEnd_3163018 1624148552823010911228551 := by
  unfold tailWord_3163018
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841186013733365327988427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76909829369955640874635805 28841186013733365327988427)
  ·
    refine ⟨43261779020600047991982641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28841186013733365327988427 43261779020600047991982641)
    ·
      refine ⟨32446334265450035993986981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43261779020600047991982641 32446334265450035993986981)
      ·
        refine ⟨6083687674771881748872559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32446334265450035993986981 6083687674771881748872559)
        ·
          refine ⟨9125531512157822623308839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083687674771881748872559 9125531512157822623308839)
          ·
            refine ⟨13688297268236733934963259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9125531512157822623308839 13688297268236733934963259)
            ·
              refine ⟨20532445902355100902444889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13688297268236733934963259 20532445902355100902444889)
              ·
                refine ⟨15399334426766325676833667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20532445902355100902444889 15399334426766325676833667)
                ·
                  refine ⟨23099001640149488515250501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15399334426766325676833667 23099001640149488515250501)
                  ·
                    refine ⟨4331062807528029096609469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23099001640149488515250501 4331062807528029096609469)
                    ·
                      refine ⟨1624148552823010911228551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331062807528029096609469 1624148552823010911228551)
                      ·
                        rfl

theorem cell23_3163018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3163018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163018 prefixEnd_3163018 := by exact prefixLift 3163018
  have htrace : WordTrace (prefixWord ++ tailWord_3163018) baseStart_3163018 baseEnd_3163018 := by
    simpa [prefixWord, tailWord_3163018, baseEnd_3163018] using wordTrace_append hprefix tailTrace_3163018
  have hstable : (prefixWord ++ tailWord_3163018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163018).length < 2 ^ (prefixWord ++ tailWord_3163018).sum := by decide
  have hdescent : baseEnd_3163018 < baseStart_3163018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163024 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8]
def baseStart_3163024 : Nat := 118140960795 + 3163024 * 2 ^ 59
def prefixEnd_3163024 : Nat := 4983230072969 + 3 ^ 40 * 3163024 * 2
def baseEnd_3163024 : Nat := 1624151633706937887753523

theorem tailTrace_3163024 : CollatzResearch.WordTrace tailWord_3163024 prefixEnd_3163024 1624151633706937887753523 := by
  unfold tailWord_3163024
  simp only [CollatzResearch.WordTrace]
  refine ⟨57682481446455862168336063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76909975261941149557781417 57682481446455862168336063)
  ·
    refine ⟨86523722169683793252504095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57682481446455862168336063 86523722169683793252504095)
    ·
      refine ⟨129785583254525689878756143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86523722169683793252504095 129785583254525689878756143)
      ·
        refine ⟨194678374881788534818134215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129785583254525689878756143 194678374881788534818134215)
        ·
          refine ⟨292017562322682802227201323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194678374881788534818134215 292017562322682802227201323)
          ·
            refine ⟨438026343484024203340801985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292017562322682802227201323 438026343484024203340801985)
            ·
              refine ⟨328519757613018152505601489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438026343484024203340801985 328519757613018152505601489)
              ·
                refine ⟨246389818209763614379201117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 328519757613018152505601489 246389818209763614379201117)
                ·
                  refine ⟨92396181828661355392200419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246389818209763614379201117 92396181828661355392200419)
                  ·
                    refine ⟨138594272742992033088300629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92396181828661355392200419 138594272742992033088300629)
                    ·
                      refine ⟨1624151633706937887753523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 138594272742992033088300629 1624151633706937887753523)
                      ·
                        rfl

theorem cell23_3163024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 8].length) (baseStart_3163024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163024 prefixEnd_3163024 := by exact prefixLift 3163024
  have htrace : WordTrace (prefixWord ++ tailWord_3163024) baseStart_3163024 baseEnd_3163024 := by
    simpa [prefixWord, tailWord_3163024, baseEnd_3163024] using wordTrace_append hprefix tailTrace_3163024
  have hstable : (prefixWord ++ tailWord_3163024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163024).length < 2 ^ (prefixWord ++ tailWord_3163024).sum := by decide
  have hdescent : baseEnd_3163024 < baseStart_3163024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163031 : List Nat := [1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 3]
def baseStart_3163031 : Nat := 118140960795 + 3163031 * 2 ^ 59
def prefixEnd_3163031 : Nat := 4983230072969 + 3 ^ 40 * 3163031 * 2
def baseEnd_3163031 : Nat := 1624155228071519360365991

theorem tailTrace_3163031 : CollatzResearch.WordTrace tailWord_3163031 prefixEnd_3163031 1624155228071519360365991 := by
  unfold tailWord_3163031
  simp only [CollatzResearch.WordTrace]
  refine ⟨115365218203886364532176947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76910145469257576354784631 115365218203886364532176947)
  ·
    refine ⟨173047827305829546798265421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115365218203886364532176947 173047827305829546798265421)
    ·
      refine ⟨64892935239686080049349533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173047827305829546798265421 64892935239686080049349533)
      ·
        refine ⟨24334850714882280018506075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64892935239686080049349533 24334850714882280018506075)
        ·
          refine ⟨36502276072323420027759113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24334850714882280018506075 36502276072323420027759113)
          ·
            refine ⟨27376707054242565020819335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36502276072323420027759113 27376707054242565020819335)
            ·
              refine ⟨41065060581363847531229003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27376707054242565020819335 41065060581363847531229003)
              ·
                refine ⟨61597590872045771296843505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41065060581363847531229003 61597590872045771296843505)
                ·
                  refine ⟨46198193154034328472632629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61597590872045771296843505 46198193154034328472632629)
                  ·
                    refine ⟨4331080608190718294309309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46198193154034328472632629 4331080608190718294309309)
                    ·
                      refine ⟨1624155228071519360365991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331080608190718294309309 1624155228071519360365991)
                      ·
                        rfl

theorem cell23_3163031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_3163031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163031 prefixEnd_3163031 := by exact prefixLift 3163031
  have htrace : WordTrace (prefixWord ++ tailWord_3163031) baseStart_3163031 baseEnd_3163031 := by
    simpa [prefixWord, tailWord_3163031, baseEnd_3163031] using wordTrace_append hprefix tailTrace_3163031
  have hstable : (prefixWord ++ tailWord_3163031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163031).length < 2 ^ (prefixWord ++ tailWord_3163031).sum := by decide
  have hdescent : baseEnd_3163031 < baseStart_3163031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163042 : List Nat := [3, 3, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3163042 : Nat := 118140960795 + 3163042 * 2 ^ 59
def prefixEnd_3163042 : Nat := 4983230072969 + 3 ^ 40 * 3163042 * 2
def baseEnd_3163042 : Nat := 541386958786239605776147

theorem tailTrace_3163042 : CollatzResearch.WordTrace tailWord_3163042 prefixEnd_3163042 541386958786239605776147 := by
  unfold tailWord_3163042
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841404851711628352706845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76910412937897675607218253 28841404851711628352706845)
  ·
    refine ⟨10815526819391860632265067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28841404851711628352706845 10815526819391860632265067)
    ·
      refine ⟨16223290229087790948397601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10815526819391860632265067 16223290229087790948397601)
      ·
        refine ⟨12167467671815843211298201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16223290229087790948397601 12167467671815843211298201)
        ·
          refine ⟨9125600753861882408473651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12167467671815843211298201 9125600753861882408473651)
          ·
            refine ⟨13688401130792823612710477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9125600753861882408473651 13688401130792823612710477)
            ·
              refine ⟨5133150424047308854766429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13688401130792823612710477 5133150424047308854766429)
              ·
                refine ⟨1924931409017740820537411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5133150424047308854766429 1924931409017740820537411)
                ·
                  refine ⟨2887397113526611230806117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1924931409017740820537411 2887397113526611230806117)
                  ·
                    refine ⟨541386958786239605776147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887397113526611230806117 541386958786239605776147)
                    ·
                      rfl

theorem cell23_3163042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3163042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163042 prefixEnd_3163042 := by exact prefixLift 3163042
  have htrace : WordTrace (prefixWord ++ tailWord_3163042) baseStart_3163042 baseEnd_3163042 := by
    simpa [prefixWord, tailWord_3163042, baseEnd_3163042] using wordTrace_append hprefix tailTrace_3163042
  have hstable : (prefixWord ++ tailWord_3163042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163042).length < 2 ^ (prefixWord ++ tailWord_3163042).sum := by decide
  have hdescent : baseEnd_3163042 < baseStart_3163042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163065 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 3]
def baseStart_3163065 : Nat := 118140960795 + 3163065 * 2 ^ 59
def prefixEnd_3163065 : Nat := 4983230072969 + 3 ^ 40 * 3163065 * 2
def baseEnd_3163065 : Nat := 1624172686413772227340835

theorem tailTrace_3163065 : CollatzResearch.WordTrace tailWord_3163065 prefixEnd_3163065 1624172686413772227340835 := by
  unfold tailWord_3163065
  simp only [CollatzResearch.WordTrace]
  refine ⟨115366458285763188338914649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76910972190508792225943099 115366458285763188338914649)
  ·
    refine ⟨86524843714322391254185987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115366458285763188338914649 86524843714322391254185987)
    ·
      refine ⟨129787265571483586881278981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86524843714322391254185987 129787265571483586881278981)
      ·
        refine ⟨24335112294653172540239809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129787265571483586881278981 24335112294653172540239809)
        ·
          refine ⟨18251334220989879405179857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24335112294653172540239809 18251334220989879405179857)
          ·
            refine ⟨13688500665742409553884893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18251334220989879405179857 13688500665742409553884893)
            ·
              refine ⟨5133187749653403582706835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13688500665742409553884893 5133187749653403582706835)
              ·
                refine ⟨7699781624480105374060253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5133187749653403582706835 7699781624480105374060253)
                ·
                  refine ⟨2887418109180039515272595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7699781624480105374060253 2887418109180039515272595)
                  ·
                    refine ⟨4331127163770059272908893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2887418109180039515272595 4331127163770059272908893)
                    ·
                      refine ⟨1624172686413772227340835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331127163770059272908893 1624172686413772227340835)
                      ·
                        rfl

theorem cell23_3163065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 3, 1, 3].length) (baseStart_3163065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163065 prefixEnd_3163065 := by exact prefixLift 3163065
  have htrace : WordTrace (prefixWord ++ tailWord_3163065) baseStart_3163065 baseEnd_3163065 := by
    simpa [prefixWord, tailWord_3163065, baseEnd_3163065] using wordTrace_append hprefix tailTrace_3163065
  have hstable : (prefixWord ++ tailWord_3163065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163065).length < 2 ^ (prefixWord ++ tailWord_3163065).sum := by decide
  have hdescent : baseEnd_3163065 < baseStart_3163065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163092 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_3163092 : Nat := 118140960795 + 3163092 * 2 ^ 59
def prefixEnd_3163092 : Nat := 4983230072969 + 3 ^ 40 * 3163092 * 2
def baseEnd_3163092 : Nat := 1624186550391443621703211

theorem tailTrace_3163092 : CollatzResearch.WordTrace tailWord_3163092 prefixEnd_3163092 1624186550391443621703211 := by
  unfold tailWord_3163092
  simp only [CollatzResearch.WordTrace]
  refine ⟨57683721528332685975073765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76911628704443581300098353 57683721528332685975073765)
  ·
    refine ⟨10815697786562378620326331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57683721528332685975073765 10815697786562378620326331)
    ·
      refine ⟨16223546679843567930489497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10815697786562378620326331 16223546679843567930489497)
      ·
        refine ⟨12167660009882675947867123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16223546679843567930489497 12167660009882675947867123)
        ·
          refine ⟨18251490014824013921800685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12167660009882675947867123 18251490014824013921800685)
          ·
            refine ⟨6844308755559005220675257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18251490014824013921800685 6844308755559005220675257)
            ·
              refine ⟨5133231566669253915506443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844308755559005220675257 5133231566669253915506443)
              ·
                refine ⟨7699847350003880873259665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5133231566669253915506443 7699847350003880873259665)
                ·
                  refine ⟨5774885512502910654944749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7699847350003880873259665 5774885512502910654944749)
                  ·
                    refine ⟨2165582067188591495604281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5774885512502910654944749 2165582067188591495604281)
                    ·
                      refine ⟨1624186550391443621703211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165582067188591495604281 1624186550391443621703211)
                      ·
                        rfl

theorem cell23_3163092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_3163092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163092 prefixEnd_3163092 := by exact prefixLift 3163092
  have htrace : WordTrace (prefixWord ++ tailWord_3163092) baseStart_3163092 baseEnd_3163092 := by
    simpa [prefixWord, tailWord_3163092, baseEnd_3163092] using wordTrace_append hprefix tailTrace_3163092
  have hstable : (prefixWord ++ tailWord_3163092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163092).length < 2 ^ (prefixWord ++ tailWord_3163092).sum := by decide
  have hdescent : baseEnd_3163092 < baseStart_3163092 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163098 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_3163098 : Nat := 118140960795 + 3163098 * 2 ^ 59
def prefixEnd_3163098 : Nat := 4983230072969 + 3 ^ 40 * 3163098 * 2
def baseEnd_3163098 : Nat := 541396543758456866076061

theorem tailTrace_3163098 : CollatzResearch.WordTrace tailWord_3163098 prefixEnd_3163098 541396543758456866076061 := by
  unfold tailWord_3163098
  simp only [CollatzResearch.WordTrace]
  refine ⟨28841915473660908743716487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 76911774596429089983243965 28841915473660908743716487)
  ·
    refine ⟨43262873210491363115574731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28841915473660908743716487 43262873210491363115574731)
    ·
      refine ⟨64894309815737044673362097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43262873210491363115574731 64894309815737044673362097)
      ·
        refine ⟨48670732361802783505021573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64894309815737044673362097 48670732361802783505021573)
        ·
          refine ⟨9125762317838021907191545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48670732361802783505021573 9125762317838021907191545)
          ·
            refine ⟨6844321738378516430393659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9125762317838021907191545 6844321738378516430393659)
            ·
              refine ⟨10266482607567774645590489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844321738378516430393659 10266482607567774645590489)
              ·
                refine ⟨7699861955675830984192867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10266482607567774645590489 7699861955675830984192867)
                ·
                  refine ⟨11549792933513746476289301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7699861955675830984192867 11549792933513746476289301)
                  ·
                    refine ⟨541396543758456866076061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11549792933513746476289301 541396543758456866076061)
                    ·
                      rfl

theorem cell23_3163098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_3163098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163098 prefixEnd_3163098 := by exact prefixLift 3163098
  have htrace : WordTrace (prefixWord ++ tailWord_3163098) baseStart_3163098 baseEnd_3163098 := by
    simpa [prefixWord, tailWord_3163098, baseEnd_3163098] using wordTrace_append hprefix tailTrace_3163098
  have hstable : (prefixWord ++ tailWord_3163098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163098).length < 2 ^ (prefixWord ++ tailWord_3163098).sum := by decide
  have hdescent : baseEnd_3163098 < baseStart_3163098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163111 : List Nat := [1, 1, 5, 2, 2, 12]
def baseStart_3163111 : Nat := 118140960795 + 3163111 * 2 ^ 59
def prefixEnd_3163111 : Nat := 4983230072969 + 3 ^ 40 * 3163111 * 2
def baseEnd_3163111 : Nat := 6683935417793740935661

theorem tailTrace_3163111 : CollatzResearch.WordTrace tailWord_3163111 prefixEnd_3163111 6683935417793740935661 := by
  unfold tailWord_3163111
  simp only [CollatzResearch.WordTrace]
  refine ⟨115368136043596538195089187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76912090695731025463392791 115368136043596538195089187)
  ·
    refine ⟨173052204065394807292633781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115368136043596538195089187 173052204065394807292633781)
    ·
      refine ⟨16223644131130763183684417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 173052204065394807292633781 16223644131130763183684417)
      ·
        refine ⟨12167733098348072387763313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16223644131130763183684417 12167733098348072387763313)
        ·
          refine ⟨9125799823761054290822485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12167733098348072387763313 9125799823761054290822485)
          ·
            refine ⟨6683935417793740935661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9125799823761054290822485 6683935417793740935661)
            ·
              rfl

theorem cell23_3163111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 12].length) (baseStart_3163111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163111 prefixEnd_3163111 := by exact prefixLift 3163111
  have htrace : WordTrace (prefixWord ++ tailWord_3163111) baseStart_3163111 baseEnd_3163111 := by
    simpa [prefixWord, tailWord_3163111, baseEnd_3163111] using wordTrace_append hprefix tailTrace_3163111
  have hstable : (prefixWord ++ tailWord_3163111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163111).length < 2 ^ (prefixWord ++ tailWord_3163111).sum := by decide
  have hdescent : baseEnd_3163111 < baseStart_3163111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163141 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 2, 7]
def baseStart_3163141 : Nat := 118140960795 + 3163141 * 2 ^ 59
def prefixEnd_3163141 : Nat := 4983230072969 + 3 ^ 40 * 3163141 * 2
def baseEnd_3163141 : Nat := 541403903647837976663495

theorem tailTrace_3163141 : CollatzResearch.WordTrace tailWord_3163141 prefixEnd_3163141 541403903647837976663495 := by
  unfold tailWord_3163141
  simp only [CollatzResearch.WordTrace]
  refine ⟨115369230233487853318681277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76912820155658568879120851 115369230233487853318681277)
  ·
    refine ⟨43263461337557944994505479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 115369230233487853318681277 43263461337557944994505479)
    ·
      refine ⟨64895192006336917491758219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43263461337557944994505479 64895192006336917491758219)
      ·
        refine ⟨97342788009505376237637329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64895192006336917491758219 97342788009505376237637329)
        ·
          refine ⟨73007091007129032178227997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97342788009505376237637329 73007091007129032178227997)
          ·
            refine ⟨27377659127673387066835499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73007091007129032178227997 27377659127673387066835499)
            ·
              refine ⟨41066488691510080600253249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27377659127673387066835499 41066488691510080600253249)
              ·
                refine ⟨30799866518632560450189937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41066488691510080600253249 30799866518632560450189937)
                ·
                  refine ⟨23099899888974420337642453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30799866518632560450189937 23099899888974420337642453)
                  ·
                    refine ⟨541403903647837976663495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23099899888974420337642453 541403903647837976663495)
                    ·
                      rfl

theorem cell23_3163141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 7].length) (baseStart_3163141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163141 prefixEnd_3163141 := by exact prefixLift 3163141
  have htrace : WordTrace (prefixWord ++ tailWord_3163141) baseStart_3163141 baseEnd_3163141 := by
    simpa [prefixWord, tailWord_3163141, baseEnd_3163141] using wordTrace_append hprefix tailTrace_3163141
  have hstable : (prefixWord ++ tailWord_3163141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163141).length < 2 ^ (prefixWord ++ tailWord_3163141).sum := by decide
  have hdescent : baseEnd_3163141 < baseStart_3163141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163159 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 1, 2, 3]
def baseStart_3163159 : Nat := 118140960795 + 3163159 * 2 ^ 59
def prefixEnd_3163159 : Nat := 4983230072969 + 3 ^ 40 * 3163159 * 2
def baseEnd_3163159 : Nat := 1624220953595294859565403

theorem tailTrace_3163159 : CollatzResearch.WordTrace tailWord_3163159 prefixEnd_3163159 1624220953595294859565403 := by
  unfold tailWord_3163159
  simp only [CollatzResearch.WordTrace]
  refine ⟨115369886747422642392836531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76913257831615094928557687 115369886747422642392836531)
  ·
    refine ⟨173054830121133963589254797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115369886747422642392836531 173054830121133963589254797)
    ·
      refine ⟨64895561295425236345970549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 173054830121133963589254797 64895561295425236345970549)
      ·
        refine ⟨6083958871446115907434739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64895561295425236345970549 6083958871446115907434739)
        ·
          refine ⟨9125938307169173861152109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083958871446115907434739 9125938307169173861152109)
          ·
            refine ⟨3422226865188440197932041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9125938307169173861152109 3422226865188440197932041)
            ·
              refine ⟨2566670148891330148449031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3422226865188440197932041 2566670148891330148449031)
              ·
                refine ⟨3850005223336995222673547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566670148891330148449031 3850005223336995222673547)
                ·
                  refine ⟨5775007835005492834010321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850005223336995222673547 5775007835005492834010321)
                  ·
                    refine ⟨4331255876254119625507741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5775007835005492834010321 4331255876254119625507741)
                    ·
                      refine ⟨1624220953595294859565403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331255876254119625507741 1624220953595294859565403)
                      ·
                        rfl

theorem cell23_3163159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_3163159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163159 prefixEnd_3163159 := by exact prefixLift 3163159
  have htrace : WordTrace (prefixWord ++ tailWord_3163159) baseStart_3163159 baseEnd_3163159 := by
    simpa [prefixWord, tailWord_3163159, baseEnd_3163159] using wordTrace_append hprefix tailTrace_3163159
  have hstable : (prefixWord ++ tailWord_3163159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163159).length < 2 ^ (prefixWord ++ tailWord_3163159).sum := by decide
  have hdescent : baseEnd_3163159 < baseStart_3163159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163172 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3163172 : Nat := 118140960795 + 3163172 * 2 ^ 59
def prefixEnd_3163172 : Nat := 4983230072969 + 3 ^ 40 * 3163172 * 2
def baseEnd_3163172 : Nat := 1624227628843803308702843

theorem tailTrace_3163172 : CollatzResearch.WordTrace tailWord_3163172 prefixEnd_3163172 1624227628843803308702843 := by
  unfold tailWord_3163172
  simp only [CollatzResearch.WordTrace]
  refine ⟨57685180448187772806529885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76913573930917030408706513 57685180448187772806529885)
  ·
    refine ⟨21631942668070414802448707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57685180448187772806529885 21631942668070414802448707)
    ·
      refine ⟨32447914002105622203673061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21631942668070414802448707 32447914002105622203673061)
      ·
        refine ⟨6083983875394804163188699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32447914002105622203673061 6083983875394804163188699)
        ·
          refine ⟨9125975813092206244783049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083983875394804163188699 9125975813092206244783049)
          ·
            refine ⟨6844481859819154683587287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9125975813092206244783049 6844481859819154683587287)
            ·
              refine ⟨10266722789728732025380931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6844481859819154683587287 10266722789728732025380931)
              ·
                refine ⟨15400084184593098038071397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10266722789728732025380931 15400084184593098038071397)
                ·
                  refine ⟨2887515784611205882138387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15400084184593098038071397 2887515784611205882138387)
                  ·
                    refine ⟨4331273676916808823207581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2887515784611205882138387 4331273676916808823207581)
                    ·
                      refine ⟨1624227628843803308702843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4331273676916808823207581 1624227628843803308702843)
                      ·
                        rfl

theorem cell23_3163172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3163172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163172 prefixEnd_3163172 := by exact prefixLift 3163172
  have htrace : WordTrace (prefixWord ++ tailWord_3163172) baseStart_3163172 baseEnd_3163172 := by
    simpa [prefixWord, tailWord_3163172, baseEnd_3163172] using wordTrace_append hprefix tailTrace_3163172
  have hstable : (prefixWord ++ tailWord_3163172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163172).length < 2 ^ (prefixWord ++ tailWord_3163172).sum := by decide
  have hdescent : baseEnd_3163172 < baseStart_3163172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163195 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 8, 2, 2]
def baseStart_3163195 : Nat := 118140960795 + 3163195 * 2 ^ 59
def prefixEnd_3163195 : Nat := 4983230072969 + 3 ^ 40 * 3163195 * 2
def baseEnd_3163195 : Nat := 1624239438898856718715237

theorem tailTrace_3163195 : CollatzResearch.WordTrace tailWord_3163195 prefixEnd_3163195 1624239438898856718715237 := by
  unfold tailWord_3163195
  simp only [CollatzResearch.WordTrace]
  refine ⟨115371199775292220541147039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76914133183528147027431359 115371199775292220541147039)
  ·
    refine ⟨173056799662938330811720559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115371199775292220541147039 173056799662938330811720559)
    ·
      refine ⟨259585199494407496217580839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173056799662938330811720559 259585199494407496217580839)
      ·
        refine ⟨389377799241611244326371259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259585199494407496217580839 389377799241611244326371259)
        ·
          refine ⟨584066698862416866489556889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389377799241611244326371259 584066698862416866489556889)
          ·
            refine ⟨438050024146812649867167667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 584066698862416866489556889 438050024146812649867167667)
            ·
              refine ⟨657075036220218974800751501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438050024146812649867167667 657075036220218974800751501)
              ·
                refine ⟨246403138582582115550281813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 657075036220218974800751501 246403138582582115550281813)
                ·
                  refine ⟨2887536780264634166604865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 246403138582582115550281813 2887536780264634166604865)
                  ·
                    refine ⟨2165652585198475624953649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2887536780264634166604865 2165652585198475624953649)
                    ·
                      refine ⟨1624239438898856718715237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165652585198475624953649 1624239438898856718715237)
                      ·
                        rfl

theorem cell23_3163195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 8, 2, 2].length) (baseStart_3163195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163195 prefixEnd_3163195 := by exact prefixLift 3163195
  have htrace : WordTrace (prefixWord ++ tailWord_3163195) baseStart_3163195 baseEnd_3163195 := by
    simpa [prefixWord, tailWord_3163195, baseEnd_3163195] using wordTrace_append hprefix tailTrace_3163195
  have hstable : (prefixWord ++ tailWord_3163195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163195).length < 2 ^ (prefixWord ++ tailWord_3163195).sum := by decide
  have hdescent : baseEnd_3163195 < baseStart_3163195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163211 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_3163211 : Nat := 118140960795 + 3163211 * 2 ^ 59
def prefixEnd_3163211 : Nat := 4983230072969 + 3 ^ 40 * 3163211 * 2
def baseEnd_3163211 : Nat := 1624247654589328656115163

theorem tailTrace_3163211 : CollatzResearch.WordTrace tailWord_3163211 prefixEnd_3163211 1624247654589328656115163 := by
  unfold tailWord_3163211
  simp only [CollatzResearch.WordTrace]
  refine ⟨115371783343234255273729487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76914522228822836849152991 115371783343234255273729487)
  ·
    refine ⟨173057675014851382910594231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 115371783343234255273729487 173057675014851382910594231)
    ·
      refine ⟨259586512522277074365891347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 173057675014851382910594231 259586512522277074365891347)
      ·
        refine ⟨389379768783415611548837021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 259586512522277074365891347 389379768783415611548837021)
        ·
          refine ⟨146017413293780854330813883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 389379768783415611548837021 146017413293780854330813883)
          ·
            refine ⟨219026119940671281496220825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 146017413293780854330813883 219026119940671281496220825)
            ·
              refine ⟨164269589955503461122165619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 219026119940671281496220825 164269589955503461122165619)
              ·
                refine ⟨246404384933255191683248429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 164269589955503461122165619 246404384933255191683248429)
                ·
                  refine ⟨92401644349970696881218161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 246404384933255191683248429 92401644349970696881218161)
                  ·
                    refine ⟨69301233262478022660913621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92401644349970696881218161 69301233262478022660913621)
                    ·
                      refine ⟨1624247654589328656115163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69301233262478022660913621 1624247654589328656115163)
                      ·
                        rfl

theorem cell23_3163211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_3163211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163211 prefixEnd_3163211 := by exact prefixLift 3163211
  have htrace : WordTrace (prefixWord ++ tailWord_3163211) baseStart_3163211 baseEnd_3163211 := by
    simpa [prefixWord, tailWord_3163211, baseEnd_3163211] using wordTrace_append hprefix tailTrace_3163211
  have hstable : (prefixWord ++ tailWord_3163211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163211).length < 2 ^ (prefixWord ++ tailWord_3163211).sum := by decide
  have hdescent : baseEnd_3163211 < baseStart_3163211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163228 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3163228 : Nat := 118140960795 + 3163228 * 2 ^ 59
def prefixEnd_3163228 : Nat := 4983230072969 + 3 ^ 40 * 3163228 * 2
def baseEnd_3163228 : Nat := 1624256383760455089602585

theorem tailTrace_3163228 : CollatzResearch.WordTrace tailWord_3163228 prefixEnd_3163228 1624256383760455089602585 := by
  unfold tailWord_3163228
  simp only [CollatzResearch.WordTrace]
  refine ⟨57686201692086333588549169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76914935589448444784732225 57686201692086333588549169)
  ·
    refine ⟨43264651269064750191411877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57686201692086333588549169 43264651269064750191411877)
    ·
      refine ⟨8112122112949640660889727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43264651269064750191411877 8112122112949640660889727)
      ·
        refine ⟨12168183169424460991334591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8112122112949640660889727 12168183169424460991334591)
        ·
          refine ⟨18252274754136691487001887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168183169424460991334591 18252274754136691487001887)
          ·
            refine ⟨27378412131205037230502831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18252274754136691487001887 27378412131205037230502831)
            ·
              refine ⟨41067618196807555845754247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27378412131205037230502831 41067618196807555845754247)
              ·
                refine ⟨61601427295211333768631371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41067618196807555845754247 61601427295211333768631371)
                ·
                  refine ⟨92402140942817000652947057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61601427295211333768631371 92402140942817000652947057)
                  ·
                    refine ⟨69301605707112750489710293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 92402140942817000652947057 69301605707112750489710293)
                    ·
                      refine ⟨1624256383760455089602585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69301605707112750489710293 1624256383760455089602585)
                      ·
                        rfl

theorem cell23_3163228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3163228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163228 prefixEnd_3163228 := by exact prefixLift 3163228
  have htrace : WordTrace (prefixWord ++ tailWord_3163228) baseStart_3163228 baseEnd_3163228 := by
    simpa [prefixWord, tailWord_3163228, baseEnd_3163228] using wordTrace_append hprefix tailTrace_3163228
  have hstable : (prefixWord ++ tailWord_3163228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163228).length < 2 ^ (prefixWord ++ tailWord_3163228).sum := by decide
  have hdescent : baseEnd_3163228 < baseStart_3163228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163246 : List Nat := [4, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_3163246 : Nat := 118140960795 + 3163246 * 2 ^ 59
def prefixEnd_3163246 : Nat := 4983230072969 + 3 ^ 40 * 3163246 * 2
def baseEnd_3163246 : Nat := 1624265626412236019177503

theorem tailTrace_3163246 : CollatzResearch.WordTrace tailWord_3163246 prefixEnd_3163246 1624265626412236019177503 := by
  unfold tailWord_3163246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421632487263432031406699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 76915373265404970834169061 14421632487263432031406699)
  ·
    refine ⟨21632448730895148047110049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14421632487263432031406699 21632448730895148047110049)
    ·
      refine ⟨16224336548171361035332537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21632448730895148047110049 16224336548171361035332537)
      ·
        refine ⟨12168252411128520776499403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16224336548171361035332537 12168252411128520776499403)
        ·
          refine ⟨18252378616692781164749105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12168252411128520776499403 18252378616692781164749105)
          ·
            refine ⟨13689283962519585873561829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18252378616692781164749105 13689283962519585873561829)
            ·
              refine ⟨2566740742972422351292843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13689283962519585873561829 2566740742972422351292843)
              ·
                refine ⟨3850111114458633526939265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2566740742972422351292843 3850111114458633526939265)
                ·
                  refine ⟨2887583335843975145204449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3850111114458633526939265 2887583335843975145204449)
                  ·
                    refine ⟨2165687501882981358903337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2887583335843975145204449 2165687501882981358903337)
                    ·
                      refine ⟨1624265626412236019177503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2165687501882981358903337 1624265626412236019177503)
                      ·
                        rfl

theorem cell23_3163246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_3163246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163246 prefixEnd_3163246 := by exact prefixLift 3163246
  have htrace : WordTrace (prefixWord ++ tailWord_3163246) baseStart_3163246 baseEnd_3163246 := by
    simpa [prefixWord, tailWord_3163246, baseEnd_3163246] using wordTrace_append hprefix tailTrace_3163246
  have hstable : (prefixWord ++ tailWord_3163246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163246).length < 2 ^ (prefixWord ++ tailWord_3163246).sum := by decide
  have hdescent : baseEnd_3163246 < baseStart_3163246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163248 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 4, 5]
def baseStart_3163248 : Nat := 118140960795 + 3163248 * 2 ^ 59
def prefixEnd_3163248 : Nat := 4983230072969 + 3 ^ 40 * 3163248 * 2
def baseEnd_3163248 : Nat := 541422217791181670450831

theorem tailTrace_3163248 : CollatzResearch.WordTrace tailWord_3163248 prefixEnd_3163248 541422217791181670450831 := by
  unfold tailWord_3163248
  simp only [CollatzResearch.WordTrace]
  refine ⟨57686566422050105296413199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76915421896066807061884265 57686566422050105296413199)
  ·
    refine ⟨86529849633075157944619799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57686566422050105296413199 86529849633075157944619799)
    ·
      refine ⟨129794774449612736916929699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86529849633075157944619799 129794774449612736916929699)
      ·
        refine ⟨194692161674419105375394549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129794774449612736916929699 194692161674419105375394549)
        ·
          refine ⟨18252390156976791128943239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 194692161674419105375394549 18252390156976791128943239)
          ·
            refine ⟨27378585235465186693414859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18252390156976791128943239 27378585235465186693414859)
            ·
              refine ⟨41067877853197780040122289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27378585235465186693414859 41067877853197780040122289)
              ·
                refine ⟨30800908389898335030091717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41067877853197780040122289 30800908389898335030091717)
                ·
                  refine ⟨5775170323105937818142197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30800908389898335030091717 5775170323105937818142197)
                  ·
                    refine ⟨541422217791181670450831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5775170323105937818142197 541422217791181670450831)
                    ·
                      rfl

theorem cell23_3163248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 4, 5].length) (baseStart_3163248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163248 prefixEnd_3163248 := by exact prefixLift 3163248
  have htrace : WordTrace (prefixWord ++ tailWord_3163248) baseStart_3163248 baseEnd_3163248 := by
    simpa [prefixWord, tailWord_3163248, baseEnd_3163248] using wordTrace_append hprefix tailTrace_3163248
  have hstable : (prefixWord ++ tailWord_3163248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163248).length < 2 ^ (prefixWord ++ tailWord_3163248).sum := by decide
  have hdescent : baseEnd_3163248 < baseStart_3163248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163265 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3163265 : Nat := 118140960795 + 3163265 * 2 ^ 59
def prefixEnd_3163265 : Nat := 4983230072969 + 3 ^ 40 * 3163265 * 2
def baseEnd_3163265 : Nat := 541425127514890481613305

theorem tailTrace_3163265 : CollatzResearch.WordTrace tailWord_3163265 prefixEnd_3163265 541425127514890481613305 := by
  unfold tailWord_3163265
  simp only [CollatzResearch.WordTrace]
  refine ⟨115373752885038622496195249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76915835256692414997463499 115373752885038622496195249)
  ·
    refine ⟨86530314663778966872146437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115373752885038622496195249 86530314663778966872146437)
    ·
      refine ⟨16224433999458556288527457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86530314663778966872146437 16224433999458556288527457)
      ·
        refine ⟨12168325499593917216395593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16224433999458556288527457 12168325499593917216395593)
        ·
          refine ⟨9126244124695437912296695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12168325499593917216395593 9126244124695437912296695)
          ·
            refine ⟨13689366187043156868445043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9126244124695437912296695 13689366187043156868445043)
            ·
              refine ⟨20534049280564735302667565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13689366187043156868445043 20534049280564735302667565)
              ·
                refine ⟨7700268480211775738500337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20534049280564735302667565 7700268480211775738500337)
                ·
                  refine ⟨5775201360158831803875253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7700268480211775738500337 5775201360158831803875253)
                  ·
                    refine ⟨541425127514890481613305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5775201360158831803875253 541425127514890481613305)
                    ·
                      rfl

theorem cell23_3163265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3163265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163265 prefixEnd_3163265 := by exact prefixLift 3163265
  have htrace : WordTrace (prefixWord ++ tailWord_3163265) baseStart_3163265 baseEnd_3163265 := by
    simpa [prefixWord, tailWord_3163265, baseEnd_3163265] using wordTrace_append hprefix tailTrace_3163265
  have hstable : (prefixWord ++ tailWord_3163265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163265).length < 2 ^ (prefixWord ++ tailWord_3163265).sum := by decide
  have hdescent : baseEnd_3163265 < baseStart_3163265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163372 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 1, 5]
def baseStart_3163372 : Nat := 118140960795 + 3163372 * 2 ^ 59
def prefixEnd_3163372 : Nat := 4983230072969 + 3 ^ 40 * 3163372 * 2
def baseEnd_3163372 : Nat := 541443441658234175400641

theorem tailTrace_3163372 : CollatzResearch.WordTrace tailWord_3163372 prefixEnd_3163372 541443441658234175400641 := by
  unfold tailWord_3163372
  simp only [CollatzResearch.WordTrace]
  refine ⟨57688827747825489885170185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 76918436997100653180226913 57688827747825489885170185)
  ·
    refine ⟨43266620810869117413877639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57688827747825489885170185 43266620810869117413877639)
    ·
      refine ⟨64899931216303676120816459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43266620810869117413877639 64899931216303676120816459)
      ·
        refine ⟨97349896824455514181224689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64899931216303676120816459 97349896824455514181224689)
        ·
          refine ⟨73012422618341635635918517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 97349896824455514181224689 73012422618341635635918517)
          ·
            refine ⟨6844914620469528340867361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73012422618341635635918517 6844914620469528340867361)
            ·
              refine ⟨5133685965352146255650521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6844914620469528340867361 5133685965352146255650521)
              ·
                refine ⟨3850264474014109691737891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5133685965352146255650521 3850264474014109691737891)
                ·
                  refine ⟨5775396711021164537606837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3850264474014109691737891 5775396711021164537606837)
                  ·
                    refine ⟨541443441658234175400641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5775396711021164537606837 541443441658234175400641)
                    ·
                      rfl

theorem cell23_3163372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_3163372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163372 prefixEnd_3163372 := by exact prefixLift 3163372
  have htrace : WordTrace (prefixWord ++ tailWord_3163372) baseStart_3163372 baseEnd_3163372 := by
    simpa [prefixWord, tailWord_3163372, baseEnd_3163372] using wordTrace_append hprefix tailTrace_3163372
  have hstable : (prefixWord ++ tailWord_3163372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163372).length < 2 ^ (prefixWord ++ tailWord_3163372).sum := by decide
  have hdescent : baseEnd_3163372 < baseStart_3163372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3163385 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 6, 4]
def baseStart_3163385 : Nat := 118140960795 + 3163385 * 2 ^ 59
def prefixEnd_3163385 : Nat := 4983230072969 + 3 ^ 40 * 3163385 * 2
def baseEnd_3163385 : Nat := 541445666741070325113121

theorem tailTrace_3163385 : CollatzResearch.WordTrace tailWord_3163385 prefixEnd_3163385 541445666741070325113121 := by
  unfold tailWord_3163385
  simp only [CollatzResearch.WordTrace]
  refine ⟨115378129644603882990563609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 76918753096402588660375739 115378129644603882990563609)
  ·
    refine ⟨86533597233452912242922707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 115378129644603882990563609 86533597233452912242922707)
    ·
      refine ⟨129800395850179368364384061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86533597233452912242922707 129800395850179368364384061)
      ·
        refine ⟨48675148443817263136644023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129800395850179368364384061 48675148443817263136644023)
        ·
          refine ⟨73012722665725894704966035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48675148443817263136644023 73012722665725894704966035)
          ·
            refine ⟨109519083998588842057449053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73012722665725894704966035 109519083998588842057449053)
            ·
              refine ⟨41069656499470815771543395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109519083998588842057449053 41069656499470815771543395)
              ·
                refine ⟨61604484749206223657315093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41069656499470815771543395 61604484749206223657315093)
                ·
                  refine ⟨2887710222619041733936645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61604484749206223657315093 2887710222619041733936645)
                  ·
                    refine ⟨541445666741070325113121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2887710222619041733936645 541445666741070325113121)
                    ·
                      rfl

theorem cell23_3163385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 4].length) (baseStart_3163385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3163385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3163385 prefixEnd_3163385 := by exact prefixLift 3163385
  have htrace : WordTrace (prefixWord ++ tailWord_3163385) baseStart_3163385 baseEnd_3163385 := by
    simpa [prefixWord, tailWord_3163385, baseEnd_3163385] using wordTrace_append hprefix tailTrace_3163385
  have hstable : (prefixWord ++ tailWord_3163385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3163385).length < 2 ^ (prefixWord ++ tailWord_3163385).sum := by decide
  have hdescent : baseEnd_3163385 < baseStart_3163385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3163385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
