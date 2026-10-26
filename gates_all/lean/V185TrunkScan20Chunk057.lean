import V185TrunkScan20Chunk056

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_346056 : List Nat := [2, 1, 3, 1, 4, 1, 4, 2, 2]
def baseStart_346056 : Nat := 118140960795 + 346056 * 2 ^ 59
def prefixEnd_346056 : Nat := 4983230072969 + 3 ^ 40 * 346056 * 2
def baseEnd_346056 : Nat := 157949387886580700452021

theorem tailTrace_346056 : CollatzResearch.WordTrace tailWord_346056 prefixEnd_346056 157949387886580700452021 := by
  unfold tailWord_346056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6310849617152844252293011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8414466156203792336390681 6310849617152844252293011)
  ·
    refine ⟨9466274425729266378439517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6310849617152844252293011 9466274425729266378439517)
    ·
      refine ⟨3549852909648474891914819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9466274425729266378439517 3549852909648474891914819)
      ·
        refine ⟨5324779364472712337872229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3549852909648474891914819 5324779364472712337872229)
        ·
          refine ⟨998396130838633563351043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5324779364472712337872229 998396130838633563351043)
          ·
            refine ⟨1497594196257950345026565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998396130838633563351043 1497594196257950345026565)
            ·
              refine ⟨280798911798365689692481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1497594196257950345026565 280798911798365689692481)
              ·
                refine ⟨210599183848774267269361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280798911798365689692481 210599183848774267269361)
                ·
                  refine ⟨157949387886580700452021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210599183848774267269361 157949387886580700452021)
                  ·
                    rfl

theorem cell20_346056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 2].length) (baseStart_346056 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346056 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346056 prefixEnd_346056 := by exact prefixLift 346056
  have htrace : WordTrace (prefixWord ++ tailWord_346056) baseStart_346056 baseEnd_346056 := by
    simpa [prefixWord, tailWord_346056, baseEnd_346056] using wordTrace_append hprefix tailTrace_346056
  have hstable : (prefixWord ++ tailWord_346056).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346056).length < 2 ^ (prefixWord ++ tailWord_346056).sum := by decide
  have hdescent : baseEnd_346056 < baseStart_346056 := by decide
  rcases family_descends (prefixWord ++ tailWord_346056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346077 : List Nat := [1, 4, 3, 1, 3, 1, 1, 2, 4]
def baseStart_346077 : Nat := 118140960795 + 346077 * 2 ^ 59
def prefixEnd_346077 : Nat := 4983230072969 + 3 ^ 40 * 346077 * 2
def baseEnd_346077 : Nat := 157958972858797960751935

theorem tailTrace_346077 : CollatzResearch.WordTrace tailWord_346077 prefixEnd_346077 157958972858797960751935 := by
  unfold tailWord_346077
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622465167229609091100485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8414976778153072727400323 12622465167229609091100485)
  ·
    refine ⟨2366712218855551704581341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12622465167229609091100485 2366712218855551704581341)
    ·
      refine ⟨887517082070831889218003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2366712218855551704581341 887517082070831889218003)
      ·
        refine ⟨1331275623106247833827005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887517082070831889218003 1331275623106247833827005)
        ·
          refine ⟨499228358664842937685127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1331275623106247833827005 499228358664842937685127)
          ·
            refine ⟨748842537997264406527691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499228358664842937685127 748842537997264406527691)
            ·
              refine ⟨1123263806995896609791537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748842537997264406527691 1123263806995896609791537)
              ·
                refine ⟨842447855246922457343653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123263806995896609791537 842447855246922457343653)
                ·
                  refine ⟨157958972858797960751935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842447855246922457343653 157958972858797960751935)
                  ·
                    rfl

theorem cell20_346077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_346077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346077 prefixEnd_346077 := by exact prefixLift 346077
  have htrace : WordTrace (prefixWord ++ tailWord_346077) baseStart_346077 baseEnd_346077 := by
    simpa [prefixWord, tailWord_346077, baseEnd_346077] using wordTrace_append hprefix tailTrace_346077
  have hstable : (prefixWord ++ tailWord_346077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346077).length < 2 ^ (prefixWord ++ tailWord_346077).sum := by decide
  have hdescent : baseEnd_346077 < baseStart_346077 := by decide
  rcases family_descends (prefixWord ++ tailWord_346077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346081 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_346081 : Nat := 118140960795 + 346081 * 2 ^ 59
def prefixEnd_346081 : Nat := 4983230072969 + 3 ^ 40 * 346081 * 2
def baseEnd_346081 : Nat := 157960798567791724618585

theorem tailTrace_346081 : CollatzResearch.WordTrace tailWord_346081 prefixEnd_346081 157960798567791724618585 := by
  unfold tailWord_346081
  simp only [CollatzResearch.WordTrace]
  refine ⟨12622611059215117774246097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8415074039476745182830731 12622611059215117774246097)
  ·
    refine ⟨9466958294411338330684573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12622611059215117774246097 9466958294411338330684573)
    ·
      refine ⟨3550109360404251874006715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9466958294411338330684573 3550109360404251874006715)
      ·
        refine ⟨5325164040606377811010073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550109360404251874006715 5325164040606377811010073)
        ·
          refine ⟨3993873030454783358257555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5325164040606377811010073 3993873030454783358257555)
          ·
            refine ⟨5990809545682175037386333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3993873030454783358257555 5990809545682175037386333)
            ·
              refine ⟨2246553579630815639019875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5990809545682175037386333 2246553579630815639019875)
              ·
                refine ⟨3369830369446223458529813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2246553579630815639019875 3369830369446223458529813)
                ·
                  refine ⟨157960798567791724618585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3369830369446223458529813 157960798567791724618585)
                  ·
                    rfl

theorem cell20_346081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_346081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346081 prefixEnd_346081 := by exact prefixLift 346081
  have htrace : WordTrace (prefixWord ++ tailWord_346081) baseStart_346081 baseEnd_346081 := by
    simpa [prefixWord, tailWord_346081, baseEnd_346081] using wordTrace_append hprefix tailTrace_346081
  have hstable : (prefixWord ++ tailWord_346081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346081).length < 2 ^ (prefixWord ++ tailWord_346081).sum := by decide
  have hdescent : baseEnd_346081 < baseStart_346081 := by decide
  rcases family_descends (prefixWord ++ tailWord_346081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346094 : List Nat := [4, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_346094 : Nat := 118140960795 + 346094 * 2 ^ 59
def prefixEnd_346094 : Nat := 4983230072969 + 3 ^ 40 * 346094 * 2
def baseEnd_346094 : Nat := 157966732122021457185199

theorem tailTrace_346094 : CollatzResearch.WordTrace tailWord_346094 prefixEnd_346094 157966732122021457185199 := by
  unfold tailWord_346094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1577885651021002624308667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8415390138778680662979557 1577885651021002624308667)
  ·
    refine ⟨2366828476531503936463001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1577885651021002624308667 2366828476531503936463001)
    ·
      refine ⟨1775121357398627952347251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2366828476531503936463001 1775121357398627952347251)
      ·
        refine ⟨2662682036097941928520877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1775121357398627952347251 2662682036097941928520877)
        ·
          refine ⟨998505763536728223195329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2662682036097941928520877 998505763536728223195329)
          ·
            refine ⟨748879322652546167396497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 998505763536728223195329 748879322652546167396497)
            ·
              refine ⟨561659491989409625547373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748879322652546167396497 561659491989409625547373)
              ·
                refine ⟨210622309496028609580265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561659491989409625547373 210622309496028609580265)
                ·
                  refine ⟨157966732122021457185199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210622309496028609580265 157966732122021457185199)
                  ·
                    rfl

theorem cell20_346094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_346094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346094 prefixEnd_346094 := by exact prefixLift 346094
  have htrace : WordTrace (prefixWord ++ tailWord_346094) baseStart_346094 baseEnd_346094 := by
    simpa [prefixWord, tailWord_346094, baseEnd_346094] using wordTrace_append hprefix tailTrace_346094
  have hstable : (prefixWord ++ tailWord_346094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346094).length < 2 ^ (prefixWord ++ tailWord_346094).sum := by decide
  have hdescent : baseEnd_346094 < baseStart_346094 := by decide
  rcases family_descends (prefixWord ++ tailWord_346094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346112 : List Nat := [2, 1, 1, 2, 1, 1, 1, 8, 3]
def baseStart_346112 : Nat := 118140960795 + 346112 * 2 ^ 59
def prefixEnd_346112 : Nat := 4983230072969 + 3 ^ 40 * 346112 * 2
def baseEnd_346112 : Nat := 157974947812493394585125

theorem tailTrace_346112 : CollatzResearch.WordTrace tailWord_346112 prefixEnd_346112 157974947812493394585125 := by
  unfold tailWord_346112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6311870861051405034312295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8415827814735206712416393 6311870861051405034312295)
  ·
    refine ⟨9467806291577107551468443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6311870861051405034312295 9467806291577107551468443)
    ·
      refine ⟨14201709437365661327202665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9467806291577107551468443 14201709437365661327202665)
      ·
        refine ⟨10651282078024245995401999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14201709437365661327202665 10651282078024245995401999)
        ·
          refine ⟨15976923117036368993102999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10651282078024245995401999 15976923117036368993102999)
          ·
            refine ⟨23965384675554553489654499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15976923117036368993102999 23965384675554553489654499)
            ·
              refine ⟨35948077013331830234481749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23965384675554553489654499 35948077013331830234481749)
              ·
                refine ⟨421266527499982385560333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 35948077013331830234481749 421266527499982385560333)
                ·
                  refine ⟨157974947812493394585125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421266527499982385560333 157974947812493394585125)
                  ·
                    rfl

theorem cell20_346112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 8, 3].length) (baseStart_346112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346112 prefixEnd_346112 := by exact prefixLift 346112
  have htrace : WordTrace (prefixWord ++ tailWord_346112) baseStart_346112 baseEnd_346112 := by
    simpa [prefixWord, tailWord_346112, baseEnd_346112] using wordTrace_append hprefix tailTrace_346112
  have hstable : (prefixWord ++ tailWord_346112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346112).length < 2 ^ (prefixWord ++ tailWord_346112).sum := by decide
  have hdescent : baseEnd_346112 < baseStart_346112 := by decide
  rcases family_descends (prefixWord ++ tailWord_346112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346202 : List Nat := [3, 1, 1, 2, 1, 1, 3, 8]
def baseStart_346202 : Nat := 118140960795 + 346202 * 2 ^ 59
def prefixEnd_346202 : Nat := 4983230072969 + 3 ^ 40 * 346202 * 2
def baseEnd_346202 : Nat := 52672008754951027194919

theorem tailTrace_346202 : CollatzResearch.WordTrace tailWord_346202 prefixEnd_346202 52672008754951027194919 := by
  unfold tailWord_346202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156756072944188859850215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8418016194517836959600573 3156756072944188859850215)
  ·
    refine ⟨4735134109416283289775323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3156756072944188859850215 4735134109416283289775323)
    ·
      refine ⟨7102701164124424934662985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4735134109416283289775323 7102701164124424934662985)
      ·
        refine ⟨5327025873093318700997239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7102701164124424934662985 5327025873093318700997239)
        ·
          refine ⟨7990538809639978051495859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5327025873093318700997239 7990538809639978051495859)
          ·
            refine ⟨11985808214459967077243789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7990538809639978051495859 11985808214459967077243789)
            ·
              refine ⟨4494678080422487653966421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11985808214459967077243789 4494678080422487653966421)
              ·
                refine ⟨52672008754951027194919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4494678080422487653966421 52672008754951027194919)
                ·
                  rfl

theorem cell20_346202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_346202 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346202 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346202 prefixEnd_346202 := by exact prefixLift 346202
  have htrace : WordTrace (prefixWord ++ tailWord_346202) baseStart_346202 baseEnd_346202 := by
    simpa [prefixWord, tailWord_346202, baseEnd_346202] using wordTrace_append hprefix tailTrace_346202
  have hstable : (prefixWord ++ tailWord_346202).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346202).length < 2 ^ (prefixWord ++ tailWord_346202).sum := by decide
  have hdescent : baseEnd_346202 < baseStart_346202 := by decide
  rcases family_descends (prefixWord ++ tailWord_346202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346250 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_346250 : Nat := 118140960795 + 346250 * 2 ^ 59
def prefixEnd_346250 : Nat := 4983230072969 + 3 ^ 40 * 346250 * 2
def baseEnd_346250 : Nat := 158037934772778247984561

theorem tailTrace_346250 : CollatzResearch.WordTrace tailWord_346250 prefixEnd_346250 158037934772778247984561 := by
  unfold tailWord_346250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157193748900714909287051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8419183330401906424765469 3157193748900714909287051)
  ·
    refine ⟨4735790623351072363930577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3157193748900714909287051 4735790623351072363930577)
    ·
      refine ⟨3551842967513304272947933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4735790623351072363930577 3551842967513304272947933)
      ·
        refine ⟨1331941112817489102355475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3551842967513304272947933 1331941112817489102355475)
        ·
          refine ⟨1997911669226233653533213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1331941112817489102355475 1997911669226233653533213)
          ·
            refine ⟨749216875959837620074955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1997911669226233653533213 749216875959837620074955)
            ·
              refine ⟨1123825313939756430112433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749216875959837620074955 1123825313939756430112433)
              ·
                refine ⟨842868985454817322584325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1123825313939756430112433 842868985454817322584325)
                ·
                  refine ⟨158037934772778247984561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 842868985454817322584325 158037934772778247984561)
                  ·
                    rfl

theorem cell20_346250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_346250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346250 prefixEnd_346250 := by exact prefixLift 346250
  have htrace : WordTrace (prefixWord ++ tailWord_346250) baseStart_346250 baseEnd_346250 := by
    simpa [prefixWord, tailWord_346250, baseEnd_346250] using wordTrace_append hprefix tailTrace_346250
  have hstable : (prefixWord ++ tailWord_346250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346250).length < 2 ^ (prefixWord ++ tailWord_346250).sum := by decide
  have hdescent : baseEnd_346250 < baseStart_346250 := by decide
  rcases family_descends (prefixWord ++ tailWord_346250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346309 : List Nat := [1, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_346309 : Nat := 118140960795 + 346309 * 2 ^ 59
def prefixEnd_346309 : Nat := 4983230072969 + 3 ^ 40 * 346309 * 2
def baseEnd_346309 : Nat := 158064863980436265017653

theorem tailTrace_346309 : CollatzResearch.WordTrace tailWord_346309 prefixEnd_346309 158064863980436265017653 := by
  unfold tailWord_346309
  simp only [CollatzResearch.WordTrace]
  refine ⟨12630926902389112713545981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8420617934926075142363987 12630926902389112713545981)
  ·
    refine ⟨4736597588395917267579743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12630926902389112713545981 4736597588395917267579743)
    ·
      refine ⟨7104896382593875901369615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4736597588395917267579743 7104896382593875901369615)
      ·
        refine ⟨10657344573890813852054423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7104896382593875901369615 10657344573890813852054423)
        ·
          refine ⟨15986016860836220778081635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10657344573890813852054423 15986016860836220778081635)
          ·
            refine ⟨23979025291254331167122453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15986016860836220778081635 23979025291254331167122453)
            ·
              refine ⟨1124016810527546773458865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 23979025291254331167122453 1124016810527546773458865)
              ·
                refine ⟨843012607895660080094149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124016810527546773458865 843012607895660080094149)
                ·
                  refine ⟨158064863980436265017653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843012607895660080094149 158064863980436265017653)
                  ·
                    rfl

theorem cell20_346309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_346309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346309 prefixEnd_346309 := by exact prefixLift 346309
  have htrace : WordTrace (prefixWord ++ tailWord_346309) baseStart_346309 baseEnd_346309 := by
    simpa [prefixWord, tailWord_346309, baseEnd_346309] using wordTrace_append hprefix tailTrace_346309
  have hstable : (prefixWord ++ tailWord_346309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346309).length < 2 ^ (prefixWord ++ tailWord_346309).sum := by decide
  have hdescent : baseEnd_346309 < baseStart_346309 := by decide
  rcases family_descends (prefixWord ++ tailWord_346309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346322 : List Nat := [3, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_346322 : Nat := 118140960795 + 346322 * 2 ^ 59
def prefixEnd_346322 : Nat := 4983230072969 + 3 ^ 40 * 346322 * 2
def baseEnd_346322 : Nat := 158070797534665997584267

theorem tailTrace_346322 : CollatzResearch.WordTrace tailWord_346322 prefixEnd_346322 158070797534665997584267 := by
  unfold tailWord_346322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157850262835503983442305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8420934034228010622512813 3157850262835503983442305)
  ·
    refine ⟨2368387697126627987581729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3157850262835503983442305 2368387697126627987581729)
    ·
      refine ⟨1776290772844970990686297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2368387697126627987581729 1776290772844970990686297)
      ·
        refine ⟨1332218079633728243014723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1776290772844970990686297 1332218079633728243014723)
        ·
          refine ⟨1998327119450592364522085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332218079633728243014723 1998327119450592364522085)
          ·
            refine ⟨374686334896986068347891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1998327119450592364522085 374686334896986068347891)
            ·
              refine ⟨562029502345479102521837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374686334896986068347891 562029502345479102521837)
              ·
                refine ⟨210761063379554663445689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562029502345479102521837 210761063379554663445689)
                ·
                  refine ⟨158070797534665997584267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210761063379554663445689 158070797534665997584267)
                  ·
                    rfl

theorem cell20_346322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_346322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346322 prefixEnd_346322 := by exact prefixLift 346322
  have htrace : WordTrace (prefixWord ++ tailWord_346322) baseStart_346322 baseEnd_346322 := by
    simpa [prefixWord, tailWord_346322, baseEnd_346322] using wordTrace_append hprefix tailTrace_346322
  have hstable : (prefixWord ++ tailWord_346322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346322).length < 2 ^ (prefixWord ++ tailWord_346322).sum := by decide
  have hdescent : baseEnd_346322 < baseStart_346322 := by decide
  rcases family_descends (prefixWord ++ tailWord_346322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346333 : List Nat := [1, 4, 3, 2, 1, 1, 8]
def baseStart_346333 : Nat := 118140960795 + 346333 * 2 ^ 59
def prefixEnd_346333 : Nat := 4983230072969 + 3 ^ 40 * 346333 * 2
def baseEnd_346333 : Nat := 17563979803822094246395

theorem tailTrace_346333 : CollatzResearch.WordTrace tailWord_346333 prefixEnd_346333 17563979803822094246395 := by
  unfold tailWord_346333
  simp only [CollatzResearch.WordTrace]
  refine ⟨12631802254302164812419653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8421201502868109874946435 12631802254302164812419653)
  ·
    refine ⟨2368462922681655902328685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12631802254302164812419653 2368462922681655902328685)
    ·
      refine ⟨888173596005620963373257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2368462922681655902328685 888173596005620963373257)
      ·
        refine ⟨666130197004215722529943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888173596005620963373257 666130197004215722529943)
        ·
          refine ⟨999195295506323583794915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666130197004215722529943 999195295506323583794915)
          ·
            refine ⟨1498792943259485375692373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999195295506323583794915 1498792943259485375692373)
            ·
              refine ⟨17563979803822094246395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1498792943259485375692373 17563979803822094246395)
              ·
                rfl

theorem cell20_346333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 8].length) (baseStart_346333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346333 prefixEnd_346333 := by exact prefixLift 346333
  have htrace : WordTrace (prefixWord ++ tailWord_346333) baseStart_346333 baseEnd_346333 := by
    simpa [prefixWord, tailWord_346333, baseEnd_346333] using wordTrace_append hprefix tailTrace_346333
  have hstable : (prefixWord ++ tailWord_346333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346333).length < 2 ^ (prefixWord ++ tailWord_346333).sum := by decide
  have hdescent : baseEnd_346333 < baseStart_346333 := by decide
  rcases family_descends (prefixWord ++ tailWord_346333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346339 : List Nat := [1, 1, 1, 8, 1, 1, 3, 2, 2]
def baseStart_346339 : Nat := 118140960795 + 346339 * 2 ^ 59
def prefixEnd_346339 : Nat := 4983230072969 + 3 ^ 40 * 346339 * 2
def baseEnd_346339 : Nat := 158078556797889494017531

theorem tailTrace_346339 : CollatzResearch.WordTrace tailWord_346339 prefixEnd_346339 158078556797889494017531 := by
  unfold tailWord_346339
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632021092280427837138071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8421347394853618558092047 12632021092280427837138071)
  ·
    refine ⟨18948031638420641755707107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12632021092280427837138071 18948031638420641755707107)
    ·
      refine ⟨28422047457630962633560661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18948031638420641755707107 28422047457630962633560661)
      ·
        refine ⟨333070868644112843362039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 28422047457630962633560661 333070868644112843362039)
        ·
          refine ⟨499606302966169265043059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333070868644112843362039 499606302966169265043059)
          ·
            refine ⟨749409454449253897564589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499606302966169265043059 749409454449253897564589)
            ·
              refine ⟨281028545418470211586721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749409454449253897564589 281028545418470211586721)
              ·
                refine ⟨210771409063852658690041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281028545418470211586721 210771409063852658690041)
                ·
                  refine ⟨158078556797889494017531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210771409063852658690041 158078556797889494017531)
                  ·
                    rfl

theorem cell20_346339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 2, 2].length) (baseStart_346339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346339 prefixEnd_346339 := by exact prefixLift 346339
  have htrace : WordTrace (prefixWord ++ tailWord_346339) baseStart_346339 baseEnd_346339 := by
    simpa [prefixWord, tailWord_346339, baseEnd_346339] using wordTrace_append hprefix tailTrace_346339
  have hstable : (prefixWord ++ tailWord_346339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346339).length < 2 ^ (prefixWord ++ tailWord_346339).sum := by decide
  have hdescent : baseEnd_346339 < baseStart_346339 := by decide
  rcases family_descends (prefixWord ++ tailWord_346339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346340 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_346340 : Nat := 118140960795 + 346340 * 2 ^ 59
def prefixEnd_346340 : Nat := 4983230072969 + 3 ^ 40 * 346340 * 2
def baseEnd_346340 : Nat := 158079013225137934984193

theorem tailTrace_346340 : CollatzResearch.WordTrace tailWord_346340 prefixEnd_346340 158079013225137934984193 := by
  unfold tailWord_346340
  simp only [CollatzResearch.WordTrace]
  refine ⟨6316028782638402503962237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8421371710184536671949649 6316028782638402503962237)
  ·
    refine ⟨2368510793489400938985839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6316028782638402503962237 2368510793489400938985839)
    ·
      refine ⟨3552766190234101408478759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368510793489400938985839 3552766190234101408478759)
      ·
        refine ⟨5329149285351152112718139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3552766190234101408478759 5329149285351152112718139)
        ·
          refine ⟨7993723928026728169077209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329149285351152112718139 7993723928026728169077209)
          ·
            refine ⟨5995292946020046126807907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7993723928026728169077209 5995292946020046126807907)
            ·
              refine ⟨8992939419030069190211861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5995292946020046126807907 8992939419030069190211861)
              ·
                refine ⟨421544035267034493291181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8992939419030069190211861 421544035267034493291181)
                ·
                  refine ⟨158079013225137934984193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421544035267034493291181 158079013225137934984193)
                  ·
                    rfl

theorem cell20_346340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_346340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346340 prefixEnd_346340 := by exact prefixLift 346340
  have htrace : WordTrace (prefixWord ++ tailWord_346340) baseStart_346340 baseEnd_346340 := by
    simpa [prefixWord, tailWord_346340, baseEnd_346340] using wordTrace_append hprefix tailTrace_346340
  have hstable : (prefixWord ++ tailWord_346340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346340).length < 2 ^ (prefixWord ++ tailWord_346340).sum := by decide
  have hdescent : baseEnd_346340 < baseStart_346340 := by decide
  rcases family_descends (prefixWord ++ tailWord_346340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346343 : List Nat := [1, 1, 5, 3, 1, 3, 1, 1, 4]
def baseStart_346343 : Nat := 118140960795 + 346343 * 2 ^ 59
def prefixEnd_346343 : Nat := 4983230072969 + 3 ^ 40 * 346343 * 2
def baseEnd_346343 : Nat := 158080382506883257884181

theorem tailTrace_346343 : CollatzResearch.WordTrace tailWord_346343 prefixEnd_346343 158080382506883257884181 := by
  unfold tailWord_346343
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632166984265936520283683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8421444656177291013522455 12632166984265936520283683)
  ·
    refine ⟨18948250476398904780425525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12632166984265936520283683 18948250476398904780425525)
    ·
      refine ⟨1776398482162397323164893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18948250476398904780425525 1776398482162397323164893)
      ·
        refine ⟨666149430810898996186835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1776398482162397323164893 666149430810898996186835)
        ·
          refine ⟨999224146216348494280253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666149430810898996186835 999224146216348494280253)
          ·
            refine ⟨374709054831130685355095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 999224146216348494280253 374709054831130685355095)
            ·
              refine ⟨562063582246696028032643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374709054831130685355095 562063582246696028032643)
              ·
                refine ⟨843095373370044042048965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562063582246696028032643 843095373370044042048965)
                ·
                  refine ⟨158080382506883257884181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 843095373370044042048965 158080382506883257884181)
                  ·
                    rfl

theorem cell20_346343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 1, 4].length) (baseStart_346343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346343 prefixEnd_346343 := by exact prefixLift 346343
  have htrace : WordTrace (prefixWord ++ tailWord_346343) baseStart_346343 baseEnd_346343 := by
    simpa [prefixWord, tailWord_346343, baseEnd_346343] using wordTrace_append hprefix tailTrace_346343
  have hstable : (prefixWord ++ tailWord_346343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346343).length < 2 ^ (prefixWord ++ tailWord_346343).sum := by decide
  have hdescent : baseEnd_346343 < baseStart_346343 := by decide
  rcases family_descends (prefixWord ++ tailWord_346343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346361 : List Nat := [1, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_346361 : Nat := 118140960795 + 346361 * 2 ^ 59
def prefixEnd_346361 : Nat := 4983230072969 + 3 ^ 40 * 346361 * 2
def baseEnd_346361 : Nat := 158088598197355195284107

theorem tailTrace_346361 : CollatzResearch.WordTrace tailWord_346361 prefixEnd_346361 158088598197355195284107 := by
  unfold tailWord_346361
  simp only [CollatzResearch.WordTrace]
  refine ⟨12632823498200725594438937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8421882332133817062959291 12632823498200725594438937)
  ·
    refine ⟨9474617623650544195829203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12632823498200725594438937 9474617623650544195829203)
    ·
      refine ⟨14211926435475816293743805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9474617623650544195829203 14211926435475816293743805)
      ·
        refine ⟨5329472413303431110153927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14211926435475816293743805 5329472413303431110153927)
        ·
          refine ⟨7994208619955146665230891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5329472413303431110153927 7994208619955146665230891)
          ·
            refine ⟨11991312929932719997846337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7994208619955146665230891 11991312929932719997846337)
            ·
              refine ⟨8993484697449539998384753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11991312929932719997846337 8993484697449539998384753)
              ·
                refine ⟨6745113523087154998788565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8993484697449539998384753 6745113523087154998788565)
                ·
                  refine ⟨158088598197355195284107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6745113523087154998788565 158088598197355195284107)
                  ·
                    rfl

theorem cell20_346361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_346361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346361 prefixEnd_346361 := by exact prefixLift 346361
  have htrace : WordTrace (prefixWord ++ tailWord_346361) baseStart_346361 baseEnd_346361 := by
    simpa [prefixWord, tailWord_346361, baseEnd_346361] using wordTrace_append hprefix tailTrace_346361
  have hstable : (prefixWord ++ tailWord_346361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346361).length < 2 ^ (prefixWord ++ tailWord_346361).sum := by decide
  have hdescent : baseEnd_346361 < baseStart_346361 := by decide
  rcases family_descends (prefixWord ++ tailWord_346361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346440 : List Nat := [2, 1, 3, 1, 1, 2, 3, 5, 2]
def baseStart_346440 : Nat := 118140960795 + 346440 * 2 ^ 59
def prefixEnd_346440 : Nat := 4983230072969 + 3 ^ 40 * 346440 * 2
def baseEnd_346440 : Nat := 158124655949982031650451

theorem tailTrace_346440 : CollatzResearch.WordTrace tailWord_346440 prefixEnd_346440 158124655949982031650451 := by
  unfold tailWord_346440
  simp only [CollatzResearch.WordTrace]
  refine ⟨6317852432457261043282387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8423803243276348057709849 6317852432457261043282387)
  ·
    refine ⟨9476778648685891564923581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6317852432457261043282387 9476778648685891564923581)
    ·
      refine ⟨3553791993257209336846343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9476778648685891564923581 3553791993257209336846343)
      ·
        refine ⟨5330687989885814005269515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3553791993257209336846343 5330687989885814005269515)
        ·
          refine ⟨7996031984828721007904273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5330687989885814005269515 7996031984828721007904273)
          ·
            refine ⟨5997023988621540755928205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7996031984828721007904273 5997023988621540755928205)
            ·
              refine ⟨2248883995733077783473077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5997023988621540755928205 2248883995733077783473077)
              ·
                refine ⟨210832874599976042200601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2248883995733077783473077 210832874599976042200601)
                ·
                  refine ⟨158124655949982031650451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210832874599976042200601 158124655949982031650451)
                  ·
                    rfl

theorem cell20_346440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 5, 2].length) (baseStart_346440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346440 prefixEnd_346440 := by exact prefixLift 346440
  have htrace : WordTrace (prefixWord ++ tailWord_346440) baseStart_346440 baseEnd_346440 := by
    simpa [prefixWord, tailWord_346440, baseEnd_346440] using wordTrace_append hprefix tailTrace_346440
  have hstable : (prefixWord ++ tailWord_346440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346440).length < 2 ^ (prefixWord ++ tailWord_346440).sum := by decide
  have hdescent : baseEnd_346440 < baseStart_346440 := by decide
  rcases family_descends (prefixWord ++ tailWord_346440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346468 : List Nat := [2, 3, 1, 1, 3, 1, 2, 7]
def baseStart_346468 : Nat := 118140960795 + 346468 * 2 ^ 59
def prefixEnd_346468 : Nat := 4983230072969 + 3 ^ 40 * 346468 * 2
def baseEnd_346468 : Nat := 52712478637646126239001

theorem tailTrace_346468 : CollatzResearch.WordTrace tailWord_346468 prefixEnd_346468 52712478637646126239001 := by
  unfold tailWord_346468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318363054406541434292029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8424484072542055245722705 6318363054406541434292029)
  ·
    refine ⟨2369386145402453037859511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6318363054406541434292029 2369386145402453037859511)
    ·
      refine ⟨3554079218103679556789267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2369386145402453037859511 3554079218103679556789267)
      ·
        refine ⟨5331118827155519335183901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3554079218103679556789267 5331118827155519335183901)
        ·
          refine ⟨1999169560183319750693963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5331118827155519335183901 1999169560183319750693963)
          ·
            refine ⟨2998754340274979626040945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999169560183319750693963 2998754340274979626040945)
            ·
              refine ⟨2249065755206234719530709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2998754340274979626040945 2249065755206234719530709)
              ·
                refine ⟨52712478637646126239001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2249065755206234719530709 52712478637646126239001)
                ·
                  rfl

theorem cell20_346468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_346468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346468 prefixEnd_346468 := by exact prefixLift 346468
  have htrace : WordTrace (prefixWord ++ tailWord_346468) baseStart_346468 baseEnd_346468 := by
    simpa [prefixWord, tailWord_346468, baseEnd_346468] using wordTrace_append hprefix tailTrace_346468
  have hstable : (prefixWord ++ tailWord_346468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346468).length < 2 ^ (prefixWord ++ tailWord_346468).sum := by decide
  have hdescent : baseEnd_346468 < baseStart_346468 := by decide
  rcases family_descends (prefixWord ++ tailWord_346468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346485 : List Nat := [1, 3, 4, 1, 2, 2, 1, 6]
def baseStart_346485 : Nat := 118140960795 + 346485 * 2 ^ 59
def prefixEnd_346485 : Nat := 4983230072969 + 3 ^ 40 * 346485 * 2
def baseEnd_346485 : Nat := 52715065058720625050089

theorem tailTrace_346485 : CollatzResearch.WordTrace tailWord_346485 prefixEnd_346485 52715065058720625050089 := by
  unfold tailWord_346485
  simp only [CollatzResearch.WordTrace]
  refine ⟨12637346149751494771952909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8424897433167663181301939 12637346149751494771952909)
  ·
    refine ⟨4739004806156810539482341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12637346149751494771952909 4739004806156810539482341)
    ·
      refine ⟨888563401154401976152939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4739004806156810539482341 888563401154401976152939)
      ·
        refine ⟨1332845101731602964229409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888563401154401976152939 1332845101731602964229409)
        ·
          refine ⟨999633826298702223172057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1332845101731602964229409 999633826298702223172057)
          ·
            refine ⟨749725369724026667379043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999633826298702223172057 749725369724026667379043)
            ·
              refine ⟨1124588054586040001068565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749725369724026667379043 1124588054586040001068565)
              ·
                refine ⟨52715065058720625050089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1124588054586040001068565 52715065058720625050089)
                ·
                  rfl

theorem cell20_346485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 6].length) (baseStart_346485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346485 prefixEnd_346485 := by exact prefixLift 346485
  have htrace : WordTrace (prefixWord ++ tailWord_346485) baseStart_346485 baseEnd_346485 := by
    simpa [prefixWord, tailWord_346485, baseEnd_346485] using wordTrace_append hprefix tailTrace_346485
  have hstable : (prefixWord ++ tailWord_346485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346485).length < 2 ^ (prefixWord ++ tailWord_346485).sum := by decide
  have hdescent : baseEnd_346485 < baseStart_346485 := by decide
  rcases family_descends (prefixWord ++ tailWord_346485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346518 : List Nat := [5, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_346518 : Nat := 118140960795 + 346518 * 2 ^ 59
def prefixEnd_346518 : Nat := 4983230072969 + 3 ^ 40 * 346518 * 2
def baseEnd_346518 : Nat := 158160257275360427050133

theorem tailTrace_346518 : CollatzResearch.WordTrace tailWord_346518 prefixEnd_346518 158160257275360427050133 := by
  unfold tailWord_346518
  simp only [CollatzResearch.WordTrace]
  refine ⟨789909359914496337994013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8425699839087960938602805 789909359914496337994013)
  ·
    refine ⟨296216009967936126747755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 789909359914496337994013 296216009967936126747755)
    ·
      refine ⟨444324014951904190121633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296216009967936126747755 444324014951904190121633)
      ·
        refine ⟨333243011213928142591225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444324014951904190121633 333243011213928142591225)
        ·
          refine ⟨249932258410446106943419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333243011213928142591225 249932258410446106943419)
          ·
            refine ⟨374898387615669160415129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249932258410446106943419 374898387615669160415129)
            ·
              refine ⟨281173790711751870311347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374898387615669160415129 281173790711751870311347)
              ·
                refine ⟨421760686067627805467021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281173790711751870311347 421760686067627805467021)
                ·
                  refine ⟨158160257275360427050133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421760686067627805467021 158160257275360427050133)
                  ·
                    rfl

theorem cell20_346518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_346518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346518 prefixEnd_346518 := by exact prefixLift 346518
  have htrace : WordTrace (prefixWord ++ tailWord_346518) baseStart_346518 baseEnd_346518 := by
    simpa [prefixWord, tailWord_346518, baseEnd_346518] using wordTrace_append hprefix tailTrace_346518
  have hstable : (prefixWord ++ tailWord_346518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346518).length < 2 ^ (prefixWord ++ tailWord_346518).sum := by decide
  have hdescent : baseEnd_346518 < baseStart_346518 := by decide
  rcases family_descends (prefixWord ++ tailWord_346518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346526 : List Nat := [4, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_346526 : Nat := 118140960795 + 346526 * 2 ^ 59
def prefixEnd_346526 : Nat := 4983230072969 + 3 ^ 40 * 346526 * 2
def baseEnd_346526 : Nat := 158163908693347954783433

theorem tailTrace_346526 : CollatzResearch.WordTrace tailWord_346526 prefixEnd_346526 158163908693347954783433 := by
  unfold tailWord_346526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579855192825369846774429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8425894361735305849463621 1579855192825369846774429)
  ·
    refine ⟨592445697309513692540411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1579855192825369846774429 592445697309513692540411)
    ·
      refine ⟨888668545964270538810617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592445697309513692540411 888668545964270538810617)
      ·
        refine ⟨666501409473202904107963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888668545964270538810617 666501409473202904107963)
        ·
          refine ⟨999752114209804356161945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666501409473202904107963 999752114209804356161945)
          ·
            refine ⟨749814085657353267121459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 999752114209804356161945 749814085657353267121459)
            ·
              refine ⟨1124721128486029900682189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 749814085657353267121459 1124721128486029900682189)
              ·
                refine ⟨421770423182261212755821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1124721128486029900682189 421770423182261212755821)
                ·
                  refine ⟨158163908693347954783433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421770423182261212755821 158163908693347954783433)
                  ·
                    rfl

theorem cell20_346526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_346526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346526 prefixEnd_346526 := by exact prefixLift 346526
  have htrace : WordTrace (prefixWord ++ tailWord_346526) baseStart_346526 baseEnd_346526 := by
    simpa [prefixWord, tailWord_346526, baseEnd_346526] using wordTrace_append hprefix tailTrace_346526
  have hstable : (prefixWord ++ tailWord_346526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346526).length < 2 ^ (prefixWord ++ tailWord_346526).sum := by decide
  have hdescent : baseEnd_346526 < baseStart_346526 := by decide
  rcases family_descends (prefixWord ++ tailWord_346526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346564 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 3]
def baseStart_346564 : Nat := 118140960795 + 346564 * 2 ^ 59
def prefixEnd_346564 : Nat := 4983230072969 + 3 ^ 40 * 346564 * 2
def baseEnd_346564 : Nat := 158181252928788711516611

theorem tailTrace_346564 : CollatzResearch.WordTrace tailWord_346564 prefixEnd_346564 158181252928788711516611 := by
  unfold tailWord_346564
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320113758232645632039373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8426818344310194176052497 6320113758232645632039373)
  ·
    refine ⟨2370042659337242112014765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6320113758232645632039373 2370042659337242112014765)
    ·
      refine ⟨888765997251465792005537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2370042659337242112014765 888765997251465792005537)
      ·
        refine ⟨666574497938599344004153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 888765997251465792005537 666574497938599344004153)
        ·
          refine ⟨499930873453949508003115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 666574497938599344004153 499930873453949508003115)
          ·
            refine ⟨749896310180924262004673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499930873453949508003115 749896310180924262004673)
            ·
              refine ⟨562422232635693196503505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749896310180924262004673 562422232635693196503505)
              ·
                refine ⟨421816674476769897377629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562422232635693196503505 421816674476769897377629)
                ·
                  refine ⟨158181252928788711516611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421816674476769897377629 158181252928788711516611)
                  ·
                    rfl

theorem cell20_346564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_346564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346564 prefixEnd_346564 := by exact prefixLift 346564
  have htrace : WordTrace (prefixWord ++ tailWord_346564) baseStart_346564 baseEnd_346564 := by
    simpa [prefixWord, tailWord_346564, baseEnd_346564] using wordTrace_append hprefix tailTrace_346564
  have hstable : (prefixWord ++ tailWord_346564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346564).length < 2 ^ (prefixWord ++ tailWord_346564).sum := by decide
  have hdescent : baseEnd_346564 < baseStart_346564 := by decide
  rcases family_descends (prefixWord ++ tailWord_346564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346568 : List Nat := [2, 1, 3, 1, 3, 2, 1, 4, 3]
def baseStart_346568 : Nat := 118140960795 + 346568 * 2 ^ 59
def prefixEnd_346568 : Nat := 4983230072969 + 3 ^ 40 * 346568 * 2
def baseEnd_346568 : Nat := 158183078637782475383261

theorem tailTrace_346568 : CollatzResearch.WordTrace tailWord_346568 prefixEnd_346568 158183078637782475383261 := by
  unfold tailWord_346568
  simp only [CollatzResearch.WordTrace]
  refine ⟨6320186704225399973612179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8426915605633866631482905 6320186704225399973612179)
  ·
    refine ⟨9480280056338099960418269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6320186704225399973612179 9480280056338099960418269)
    ·
      refine ⟨3555105021126787485156851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9480280056338099960418269 3555105021126787485156851)
      ·
        refine ⟨5332657531690181227735277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3555105021126787485156851 5332657531690181227735277)
        ·
          refine ⟨1999746574383817960400729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5332657531690181227735277 1999746574383817960400729)
          ·
            refine ⟨1499809930787863470300547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999746574383817960400729 1499809930787863470300547)
            ·
              refine ⟨2249714896181795205450821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1499809930787863470300547 2249714896181795205450821)
              ·
                refine ⟨421821543034086601022029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2249714896181795205450821 421821543034086601022029)
                ·
                  refine ⟨158183078637782475383261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 421821543034086601022029 158183078637782475383261)
                  ·
                    rfl

theorem cell20_346568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 4, 3].length) (baseStart_346568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346568 prefixEnd_346568 := by exact prefixLift 346568
  have htrace : WordTrace (prefixWord ++ tailWord_346568) baseStart_346568 baseEnd_346568 := by
    simpa [prefixWord, tailWord_346568, baseEnd_346568] using wordTrace_append hprefix tailTrace_346568
  have hstable : (prefixWord ++ tailWord_346568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346568).length < 2 ^ (prefixWord ++ tailWord_346568).sum := by decide
  have hdescent : baseEnd_346568 < baseStart_346568 := by decide
  rcases family_descends (prefixWord ++ tailWord_346568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346599 : List Nat := [1, 1, 5, 2, 1, 1, 5, 4]
def baseStart_346599 : Nat := 118140960795 + 346599 * 2 ^ 59
def prefixEnd_346599 : Nat := 4983230072969 + 3 ^ 40 * 346599 * 2
def baseEnd_346599 : Nat := 52732409294161381783267

theorem tailTrace_346599 : CollatzResearch.WordTrace tailWord_346599 prefixEnd_346599 52732409294161381783267 := by
  unfold tailWord_346599
  simp only [CollatzResearch.WordTrace]
  refine ⟨12641504071338492241602851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8427669380892328161068567 12641504071338492241602851)
  ·
    refine ⟨18962256107007738362404277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12641504071338492241602851 18962256107007738362404277)
    ·
      refine ⟨1777711510031975471475401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18962256107007738362404277 1777711510031975471475401)
      ·
        refine ⟨1333283632523981603606551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1777711510031975471475401 1333283632523981603606551)
        ·
          refine ⟨1999925448785972405409827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333283632523981603606551 1999925448785972405409827)
          ·
            refine ⟨2999888173178958608114741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999925448785972405409827 2999888173178958608114741)
            ·
              refine ⟨281239516235527369510757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2999888173178958608114741 281239516235527369510757)
              ·
                refine ⟨52732409294161381783267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281239516235527369510757 52732409294161381783267)
                ·
                  rfl

theorem cell20_346599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 4].length) (baseStart_346599 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346599 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346599 prefixEnd_346599 := by exact prefixLift 346599
  have htrace : WordTrace (prefixWord ++ tailWord_346599) baseStart_346599 baseEnd_346599 := by
    simpa [prefixWord, tailWord_346599, baseEnd_346599] using wordTrace_append hprefix tailTrace_346599
  have hstable : (prefixWord ++ tailWord_346599).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346599).length < 2 ^ (prefixWord ++ tailWord_346599).sum := by decide
  have hdescent : baseEnd_346599 < baseStart_346599 := by decide
  rcases family_descends (prefixWord ++ tailWord_346599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346627 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_346627 : Nat := 118140960795 + 346627 * 2 ^ 59
def prefixEnd_346627 : Nat := 4983230072969 + 3 ^ 40 * 346627 * 2
def baseEnd_346627 : Nat := 158210007845440492416353

theorem tailTrace_346627 : CollatzResearch.WordTrace tailWord_346627 prefixEnd_346627 158210007845440492416353 := by
  unfold tailWord_346627
  simp only [CollatzResearch.WordTrace]
  refine ⟨12642525315237053023622135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8428350210158035349081423 12642525315237053023622135)
  ·
    refine ⟨18963787972855579535433203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12642525315237053023622135 18963787972855579535433203)
    ·
      refine ⟨28445681959283369303149805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18963787972855579535433203 28445681959283369303149805)
      ·
        refine ⟨10667130734731263488681177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28445681959283369303149805 10667130734731263488681177)
        ·
          refine ⟨8000348051048447616510883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10667130734731263488681177 8000348051048447616510883)
          ·
            refine ⟨12000522076572671424766325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8000348051048447616510883 12000522076572671424766325)
            ·
              refine ⟨1125048944678687946071843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12000522076572671424766325 1125048944678687946071843)
              ·
                refine ⟨1687573417018031919107765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1125048944678687946071843 1687573417018031919107765)
                ·
                  refine ⟨158210007845440492416353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1687573417018031919107765 158210007845440492416353)
                  ·
                    rfl

theorem cell20_346627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_346627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346627 prefixEnd_346627 := by exact prefixLift 346627
  have htrace : WordTrace (prefixWord ++ tailWord_346627) baseStart_346627 baseEnd_346627 := by
    simpa [prefixWord, tailWord_346627, baseEnd_346627] using wordTrace_append hprefix tailTrace_346627
  have hstable : (prefixWord ++ tailWord_346627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346627).length < 2 ^ (prefixWord ++ tailWord_346627).sum := by decide
  have hdescent : baseEnd_346627 < baseStart_346627 := by decide
  rcases family_descends (prefixWord ++ tailWord_346627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346664 : List Nat := [2, 1, 5, 2, 1, 3, 1, 3, 2]
def baseStart_346664 : Nat := 118140960795 + 346664 * 2 ^ 59
def prefixEnd_346664 : Nat := 4983230072969 + 3 ^ 40 * 346664 * 2
def baseEnd_346664 : Nat := 158226895653632808182869

theorem tailTrace_346664 : CollatzResearch.WordTrace tailWord_346664 prefixEnd_346664 158226895653632808182869 := by
  unfold tailWord_346664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6321937408051504171359523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8429249877402005561812697 6321937408051504171359523)
  ·
    refine ⟨9482906112077256257039285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6321937408051504171359523 9482906112077256257039285)
    ·
      refine ⟨889022448007242774097433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9482906112077256257039285 889022448007242774097433)
      ·
        refine ⟨666766836005432080573075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889022448007242774097433 666766836005432080573075)
        ·
          refine ⟨1000150254008148120859613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666766836005432080573075 1000150254008148120859613)
          ·
            refine ⟨375056345253055545322355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1000150254008148120859613 375056345253055545322355)
            ·
              refine ⟨562584517879583317983533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375056345253055545322355 562584517879583317983533)
              ·
                refine ⟨210969194204843744243825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562584517879583317983533 210969194204843744243825)
                ·
                  refine ⟨158226895653632808182869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 210969194204843744243825 158226895653632808182869)
                  ·
                    rfl

theorem cell20_346664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_346664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346664 prefixEnd_346664 := by exact prefixLift 346664
  have htrace : WordTrace (prefixWord ++ tailWord_346664) baseStart_346664 baseEnd_346664 := by
    simpa [prefixWord, tailWord_346664, baseEnd_346664] using wordTrace_append hprefix tailTrace_346664
  have hstable : (prefixWord ++ tailWord_346664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346664).length < 2 ^ (prefixWord ++ tailWord_346664).sum := by decide
  have hdescent : baseEnd_346664 < baseStart_346664 := by decide
  rcases family_descends (prefixWord ++ tailWord_346664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346672 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_346672 : Nat := 118140960795 + 346672 * 2 ^ 59
def prefixEnd_346672 : Nat := 4983230072969 + 3 ^ 40 * 346672 * 2
def baseEnd_346672 : Nat := 158230547071620335916169

theorem tailTrace_346672 : CollatzResearch.WordTrace tailWord_346672 prefixEnd_346672 158230547071620335916169 := by
  unfold tailWord_346672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6322083300037012854505135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8429444400049350472673513 6322083300037012854505135)
  ·
    refine ⟨9483124950055519281757703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6322083300037012854505135 9483124950055519281757703)
    ·
      refine ⟨14224687425083278922636555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9483124950055519281757703 14224687425083278922636555)
      ·
        refine ⟨21337031137624918383954833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14224687425083278922636555 21337031137624918383954833)
        ·
          refine ⟨16002773353218688787966125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21337031137624918383954833 16002773353218688787966125)
          ·
            refine ⟨6001040007457008295487297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16002773353218688787966125 6001040007457008295487297)
            ·
              refine ⟨4500780005592756221615473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6001040007457008295487297 4500780005592756221615473)
              ·
                refine ⟨3375585004194567166211605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4500780005592756221615473 3375585004194567166211605)
                ·
                  refine ⟨158230547071620335916169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3375585004194567166211605 158230547071620335916169)
                  ·
                    rfl

theorem cell20_346672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_346672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346672 prefixEnd_346672 := by exact prefixLift 346672
  have htrace : WordTrace (prefixWord ++ tailWord_346672) baseStart_346672 baseEnd_346672 := by
    simpa [prefixWord, tailWord_346672, baseEnd_346672] using wordTrace_append hprefix tailTrace_346672
  have hstable : (prefixWord ++ tailWord_346672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346672).length < 2 ^ (prefixWord ++ tailWord_346672).sum := by decide
  have hdescent : baseEnd_346672 < baseStart_346672 := by decide
  rcases family_descends (prefixWord ++ tailWord_346672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346734 : List Nat := [4, 1, 2, 2, 2, 9]
def baseStart_346734 : Nat := 118140960795 + 346734 * 2 ^ 59
def prefixEnd_346734 : Nat := 4983230072969 + 3 ^ 40 * 346734 * 2
def baseEnd_346734 : Nat := 5861438724482358364787

theorem tailTrace_346734 : CollatzResearch.WordTrace tailWord_346734 prefixEnd_346734 5861438724482358364787 := by
  unfold tailWord_346734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580803490731176287220907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8430951950566273531844837 1580803490731176287220907)
  ·
    refine ⟨2371205236096764430831361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1580803490731176287220907 2371205236096764430831361)
    ·
      refine ⟨1778403927072573323123521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2371205236096764430831361 1778403927072573323123521)
      ·
        refine ⟨1333802945304429992342641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1778403927072573323123521 1333802945304429992342641)
        ·
          refine ⟨1000352208978322494256981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1333802945304429992342641 1000352208978322494256981)
          ·
            refine ⟨5861438724482358364787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1000352208978322494256981 5861438724482358364787)
            ·
              rfl

theorem cell20_346734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 9].length) (baseStart_346734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346734 prefixEnd_346734 := by exact prefixLift 346734
  have htrace : WordTrace (prefixWord ++ tailWord_346734) baseStart_346734 baseEnd_346734 := by
    simpa [prefixWord, tailWord_346734, baseEnd_346734] using wordTrace_append hprefix tailTrace_346734
  have hstable : (prefixWord ++ tailWord_346734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346734).length < 2 ^ (prefixWord ++ tailWord_346734).sum := by decide
  have hdescent : baseEnd_346734 < baseStart_346734 := by decide
  rcases family_descends (prefixWord ++ tailWord_346734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346778 : List Nat := [3, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_346778 : Nat := 118140960795 + 346778 * 2 ^ 59
def prefixEnd_346778 : Nat := 4983230072969 + 3 ^ 40 * 346778 * 2
def baseEnd_346778 : Nat := 158278928359955078382403

theorem tailTrace_346778 : CollatzResearch.WordTrace tailWord_346778 prefixEnd_346778 158278928359955078382403 := by
  unfold tailWord_346778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162008184422501453092247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8432021825126670541579325 3162008184422501453092247)
  ·
    refine ⟨4743012276633752179638371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162008184422501453092247 4743012276633752179638371)
    ·
      refine ⟨7114518414950628269457557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4743012276633752179638371 7114518414950628269457557)
      ·
        refine ⟨333493050700810700130823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7114518414950628269457557 333493050700810700130823)
        ·
          refine ⟨500239576051216050196235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333493050700810700130823 500239576051216050196235)
          ·
            refine ⟨750359364076824075294353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500239576051216050196235 750359364076824075294353)
            ·
              refine ⟨562769523057618056470765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750359364076824075294353 562769523057618056470765)
              ·
                refine ⟨211038571146606771176537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562769523057618056470765 211038571146606771176537)
                ·
                  refine ⟨158278928359955078382403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211038571146606771176537 158278928359955078382403)
                  ·
                    rfl

theorem cell20_346778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_346778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346778 prefixEnd_346778 := by exact prefixLift 346778
  have htrace : WordTrace (prefixWord ++ tailWord_346778) baseStart_346778 baseEnd_346778 := by
    simpa [prefixWord, tailWord_346778, baseEnd_346778] using wordTrace_append hprefix tailTrace_346778
  have hstable : (prefixWord ++ tailWord_346778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346778).length < 2 ^ (prefixWord ++ tailWord_346778).sum := by decide
  have hdescent : baseEnd_346778 < baseStart_346778 := by decide
  rcases family_descends (prefixWord ++ tailWord_346778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346803 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 4]
def baseStart_346803 : Nat := 118140960795 + 346803 * 2 ^ 59
def prefixEnd_346803 : Nat := 4983230072969 + 3 ^ 40 * 346803 * 2
def baseEnd_346803 : Nat := 158290339041166102548967

theorem tailTrace_346803 : CollatzResearch.WordTrace tailWord_346803 prefixEnd_346803 158290339041166102548967 := by
  unfold tailWord_346803
  simp only [CollatzResearch.WordTrace]
  refine ⟨12648944562599435082029063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8432629708399623388019375 12648944562599435082029063)
  ·
    refine ⟨18973416843899152623043595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12648944562599435082029063 18973416843899152623043595)
    ·
      refine ⟨28460125265848728934565393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18973416843899152623043595 28460125265848728934565393)
      ·
        refine ⟨21345093949386546700924045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28460125265848728934565393 21345093949386546700924045)
        ·
          refine ⟨8004410231019955012846517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21345093949386546700924045 8004410231019955012846517)
          ·
            refine ⟨750413459158120782454361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8004410231019955012846517 750413459158120782454361)
            ·
              refine ⟨562810094368590586840771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750413459158120782454361 562810094368590586840771)
              ·
                refine ⟨844215141552885880261157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 562810094368590586840771 844215141552885880261157)
                ·
                  refine ⟨158290339041166102548967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 844215141552885880261157 158290339041166102548967)
                  ·
                    rfl

theorem cell20_346803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_346803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346803 prefixEnd_346803 := by exact prefixLift 346803
  have htrace : WordTrace (prefixWord ++ tailWord_346803) baseStart_346803 baseEnd_346803 := by
    simpa [prefixWord, tailWord_346803, baseEnd_346803] using wordTrace_append hprefix tailTrace_346803
  have hstable : (prefixWord ++ tailWord_346803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346803).length < 2 ^ (prefixWord ++ tailWord_346803).sum := by decide
  have hdescent : baseEnd_346803 < baseStart_346803 := by decide
  rcases family_descends (prefixWord ++ tailWord_346803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346813 : List Nat := [1, 4, 1, 2, 1, 4, 3, 1, 3]
def baseStart_346813 : Nat := 118140960795 + 346813 * 2 ^ 59
def prefixEnd_346813 : Nat := 4983230072969 + 3 ^ 40 * 346813 * 2
def baseEnd_346813 : Nat := 158294903313650512215593

theorem tailTrace_346813 : CollatzResearch.WordTrace tailWord_346813 prefixEnd_346813 158294903313650512215593 := by
  unfold tailWord_346813
  simp only [CollatzResearch.WordTrace]
  refine ⟨12649309292563206789893093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8432872861708804526595395 12649309292563206789893093)
  ·
    refine ⟨2371745492355601273104955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12649309292563206789893093 2371745492355601273104955)
    ·
      refine ⟨3557618238533401909657433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2371745492355601273104955 3557618238533401909657433)
      ·
        refine ⟨2668213678900051432243075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3557618238533401909657433 2668213678900051432243075)
        ·
          refine ⟨4002320518350077148364613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668213678900051432243075 4002320518350077148364613)
          ·
            refine ⟨750435097190639465318365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4002320518350077148364613 750435097190639465318365)
            ·
              refine ⟨281413161446489799494387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 750435097190639465318365 281413161446489799494387)
              ·
                refine ⟨422119742169734699241581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281413161446489799494387 422119742169734699241581)
                ·
                  refine ⟨158294903313650512215593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422119742169734699241581 158294903313650512215593)
                  ·
                    rfl

theorem cell20_346813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_346813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346813 prefixEnd_346813 := by exact prefixLift 346813
  have htrace : WordTrace (prefixWord ++ tailWord_346813) baseStart_346813 baseEnd_346813 := by
    simpa [prefixWord, tailWord_346813, baseEnd_346813] using wordTrace_append hprefix tailTrace_346813
  have hstable : (prefixWord ++ tailWord_346813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346813).length < 2 ^ (prefixWord ++ tailWord_346813).sum := by decide
  have hdescent : baseEnd_346813 < baseStart_346813 := by decide
  rcases family_descends (prefixWord ++ tailWord_346813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346909 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 2]
def baseStart_346909 : Nat := 118140960795 + 346909 * 2 ^ 59
def prefixEnd_346909 : Nat := 4983230072969 + 3 ^ 40 * 346909 * 2
def baseEnd_346909 : Nat := 158338720329500845015201

theorem tailTrace_346909 : CollatzResearch.WordTrace tailWord_346909 prefixEnd_346909 158338720329500845015201 := by
  unfold tailWord_346909
  simp only [CollatzResearch.WordTrace]
  refine ⟨12652810700215415185387781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8435207133476943456925187 12652810700215415185387781)
  ·
    refine ⟨2372402006290390347260209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12652810700215415185387781 2372402006290390347260209)
    ·
      refine ⟨1779301504717792760445157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2372402006290390347260209 1779301504717792760445157)
      ·
        refine ⟨333619032134586142583467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1779301504717792760445157 333619032134586142583467)
        ·
          refine ⟨500428548201879213875201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333619032134586142583467 500428548201879213875201)
          ·
            refine ⟨375321411151409410406401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500428548201879213875201 375321411151409410406401)
            ·
              refine ⟨281491058363557057804801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375321411151409410406401 281491058363557057804801)
              ·
                refine ⟨211118293772667793353601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281491058363557057804801 211118293772667793353601)
                ·
                  refine ⟨158338720329500845015201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211118293772667793353601 158338720329500845015201)
                  ·
                    rfl

theorem cell20_346909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_346909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346909 prefixEnd_346909 := by exact prefixLift 346909
  have htrace : WordTrace (prefixWord ++ tailWord_346909) baseStart_346909 baseEnd_346909 := by
    simpa [prefixWord, tailWord_346909, baseEnd_346909] using wordTrace_append hprefix tailTrace_346909
  have hstable : (prefixWord ++ tailWord_346909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346909).length < 2 ^ (prefixWord ++ tailWord_346909).sum := by decide
  have hdescent : baseEnd_346909 < baseStart_346909 := by decide
  rcases family_descends (prefixWord ++ tailWord_346909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346969 : List Nat := [1, 2, 1, 2, 2, 5, 1, 1, 5]
def baseStart_346969 : Nat := 118140960795 + 346969 * 2 ^ 59
def prefixEnd_346969 : Nat := 4983230072969 + 3 ^ 40 * 346969 * 2
def baseEnd_346969 : Nat := 158366105964407303014955

theorem tailTrace_346969 : CollatzResearch.WordTrace tailWord_346969 prefixEnd_346969 158366105964407303014955 := by
  unfold tailWord_346969
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654999079998045432571961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8436666053332030288381307 12654999079998045432571961)
  ·
    refine ⟨9491249309998534074428971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12654999079998045432571961 9491249309998534074428971)
    ·
      refine ⟨14236873964997801111643457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9491249309998534074428971 14236873964997801111643457)
      ·
        refine ⟨10677655473748350833732593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14236873964997801111643457 10677655473748350833732593)
        ·
          refine ⟨8008241605311263125299445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10677655473748350833732593 8008241605311263125299445)
          ·
            refine ⟨750772650497930917996823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8008241605311263125299445 750772650497930917996823)
            ·
              refine ⟨1126158975746896376995235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750772650497930917996823 1126158975746896376995235)
              ·
                refine ⟨1689238463620344565492853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126158975746896376995235 1689238463620344565492853)
                ·
                  refine ⟨158366105964407303014955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1689238463620344565492853 158366105964407303014955)
                  ·
                    rfl

theorem cell20_346969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_346969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346969 prefixEnd_346969 := by exact prefixLift 346969
  have htrace : WordTrace (prefixWord ++ tailWord_346969) baseStart_346969 baseEnd_346969 := by
    simpa [prefixWord, tailWord_346969, baseEnd_346969] using wordTrace_append hprefix tailTrace_346969
  have hstable : (prefixWord ++ tailWord_346969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346969).length < 2 ^ (prefixWord ++ tailWord_346969).sum := by decide
  have hdescent : baseEnd_346969 < baseStart_346969 := by decide
  rcases family_descends (prefixWord ++ tailWord_346969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346972 : List Nat := [2, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_346972 : Nat := 118140960795 + 346972 * 2 ^ 59
def prefixEnd_346972 : Nat := 4983230072969 + 3 ^ 40 * 346972 * 2
def baseEnd_346972 : Nat := 158367475246152625914943

theorem tailTrace_346972 : CollatzResearch.WordTrace tailWord_346972 prefixEnd_346972 158367475246152625914943 := by
  unfold tailWord_346972
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327554249493588472465585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8436738999324784629954113 6327554249493588472465585)
  ·
    refine ⟨4745665687120191354349189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6327554249493588472465585 4745665687120191354349189)
    ·
      refine ⟨889812316335035878940473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4745665687120191354349189 889812316335035878940473)
      ·
        refine ⟨667359237251276909205355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 889812316335035878940473 667359237251276909205355)
        ·
          refine ⟨1001038855876915363808033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667359237251276909205355 1001038855876915363808033)
          ·
            refine ⟨750779141907686522856025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001038855876915363808033 750779141907686522856025)
            ·
              refine ⟨563084356430764892142019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750779141907686522856025 563084356430764892142019)
              ·
                refine ⟨844626534646147338213029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563084356430764892142019 844626534646147338213029)
                ·
                  refine ⟨158367475246152625914943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 844626534646147338213029 158367475246152625914943)
                  ·
                    rfl

theorem cell20_346972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_346972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_346972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_346972 prefixEnd_346972 := by exact prefixLift 346972
  have htrace : WordTrace (prefixWord ++ tailWord_346972) baseStart_346972 baseEnd_346972 := by
    simpa [prefixWord, tailWord_346972, baseEnd_346972] using wordTrace_append hprefix tailTrace_346972
  have hstable : (prefixWord ++ tailWord_346972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346972).length < 2 ^ (prefixWord ++ tailWord_346972).sum := by decide
  have hdescent : baseEnd_346972 < baseStart_346972 := by decide
  rcases family_descends (prefixWord ++ tailWord_346972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347041 : List Nat := [1, 2, 3, 4, 1, 1, 4, 1, 3]
def baseStart_347041 : Nat := 118140960795 + 347041 * 2 ^ 59
def prefixEnd_347041 : Nat := 4983230072969 + 3 ^ 40 * 347041 * 2
def baseEnd_347041 : Nat := 158398968726295052614661

theorem tailTrace_347041 : CollatzResearch.WordTrace tailWord_347041 prefixEnd_347041 158398968726295052614661 := by
  unfold tailWord_347041
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657625135737201729192977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8438416757158134486128651 12657625135737201729192977)
  ·
    refine ⟨9493218851802901296894733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12657625135737201729192977 9493218851802901296894733)
    ·
      refine ⟨3559957069426087986335525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9493218851802901296894733 3559957069426087986335525)
      ·
        refine ⟨667491950517391497437911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3559957069426087986335525 667491950517391497437911)
        ·
          refine ⟨1001237925776087246156867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667491950517391497437911 1001237925776087246156867)
          ·
            refine ⟨1501856888664130869235301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001237925776087246156867 1501856888664130869235301)
            ·
              refine ⟨281598166624524537981619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1501856888664130869235301 281598166624524537981619)
              ·
                refine ⟨422397249936786806972429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281598166624524537981619 422397249936786806972429)
                ·
                  refine ⟨158398968726295052614661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422397249936786806972429 158398968726295052614661)
                  ·
                    rfl

theorem cell20_347041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 3].length) (baseStart_347041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347041 prefixEnd_347041 := by exact prefixLift 347041
  have htrace : WordTrace (prefixWord ++ tailWord_347041) baseStart_347041 baseEnd_347041 := by
    simpa [prefixWord, tailWord_347041, baseEnd_347041] using wordTrace_append hprefix tailTrace_347041
  have hstable : (prefixWord ++ tailWord_347041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347041).length < 2 ^ (prefixWord ++ tailWord_347041).sum := by decide
  have hdescent : baseEnd_347041 < baseStart_347041 := by decide
  rcases family_descends (prefixWord ++ tailWord_347041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347076 : List Nat := [2, 3, 3, 3, 9]
def baseStart_347076 : Nat := 118140960795 + 347076 * 2 ^ 59
def prefixEnd_347076 : Nat := 4983230072969 + 3 ^ 40 * 347076 * 2
def baseEnd_347076 : Nat := 1955740045431981314171

theorem tailTrace_347076 : CollatzResearch.WordTrace tailWord_347076 prefixEnd_347076 1955740045431981314171 := by
  unfold tailWord_347076
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329450845305201353358541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8439267793740268471144721 6329450845305201353358541)
  ·
    refine ⟨2373544066989450507509453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6329450845305201353358541 2373544066989450507509453)
    ·
      refine ⟨890079025121043940316045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2373544066989450507509453 890079025121043940316045)
      ·
        refine ⟨333779634420391477618517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 890079025121043940316045 333779634420391477618517)
        ·
          refine ⟨1955740045431981314171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 333779634420391477618517 1955740045431981314171)
          ·
            rfl

theorem cell20_347076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 9].length) (baseStart_347076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347076 prefixEnd_347076 := by exact prefixLift 347076
  have htrace : WordTrace (prefixWord ++ tailWord_347076) baseStart_347076 baseEnd_347076 := by
    simpa [prefixWord, tailWord_347076, baseEnd_347076] using wordTrace_append hprefix tailTrace_347076
  have hstable : (prefixWord ++ tailWord_347076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347076).length < 2 ^ (prefixWord ++ tailWord_347076).sum := by decide
  have hdescent : baseEnd_347076 < baseStart_347076 := by decide
  rcases family_descends (prefixWord ++ tailWord_347076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347078 : List Nat := [6, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_347078 : Nat := 118140960795 + 347078 * 2 ^ 59
def prefixEnd_347078 : Nat := 4983230072969 + 3 ^ 40 * 347078 * 2
def baseEnd_347078 : Nat := 158415856534487368381177

theorem tailTrace_347078 : CollatzResearch.WordTrace tailWord_347078 prefixEnd_347078 158415856534487368381177 := by
  unfold tailWord_347078
  simp only [CollatzResearch.WordTrace]
  refine ⟨395592957393848657759059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8439316424402104698859925 395592957393848657759059)
  ·
    refine ⟨593389436090772986638589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395592957393848657759059 593389436090772986638589)
    ·
      refine ⟨222521038534039869989471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 593389436090772986638589 222521038534039869989471)
      ·
        refine ⟨333781557801059804984207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222521038534039869989471 333781557801059804984207)
        ·
          refine ⟨500672336701589707476311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333781557801059804984207 500672336701589707476311)
          ·
            refine ⟨751008505052384561214467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500672336701589707476311 751008505052384561214467)
            ·
              refine ⟨1126512757578576841821701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751008505052384561214467 1126512757578576841821701)
              ·
                refine ⟨211221142045983157841569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1126512757578576841821701 211221142045983157841569)
                ·
                  refine ⟨158415856534487368381177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211221142045983157841569 158415856534487368381177)
                  ·
                    rfl

theorem cell20_347078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_347078 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347078 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347078 prefixEnd_347078 := by exact prefixLift 347078
  have htrace : WordTrace (prefixWord ++ tailWord_347078) baseStart_347078 baseEnd_347078 := by
    simpa [prefixWord, tailWord_347078, baseEnd_347078] using wordTrace_append hprefix tailTrace_347078
  have hstable : (prefixWord ++ tailWord_347078).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347078).length < 2 ^ (prefixWord ++ tailWord_347078).sum := by decide
  have hdescent : baseEnd_347078 < baseStart_347078 := by decide
  rcases family_descends (prefixWord ++ tailWord_347078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347083 : List Nat := [1, 1, 1, 1, 3, 5, 1, 4, 3]
def baseStart_347083 : Nat := 118140960795 + 347083 * 2 ^ 59
def prefixEnd_347083 : Nat := 4983230072969 + 3 ^ 40 * 347083 * 2
def baseEnd_347083 : Nat := 158418138670729573214489

theorem tailTrace_347083 : CollatzResearch.WordTrace tailWord_347083 prefixEnd_347083 158418138670729573214489 := by
  unfold tailWord_347083
  simp only [CollatzResearch.WordTrace]
  refine ⟨12659157001585042902221903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8439438001056695268147935 12659157001585042902221903)
  ·
    refine ⟨18988735502377564353332855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12659157001585042902221903 18988735502377564353332855)
    ·
      refine ⟨28483103253566346529999283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18988735502377564353332855 28483103253566346529999283)
      ·
        refine ⟨42724654880349519794998925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28483103253566346529999283 42724654880349519794998925)
        ·
          refine ⟨16021745580131069923124597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42724654880349519794998925 16021745580131069923124597)
          ·
            refine ⟨1502038648137287805292931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16021745580131069923124597 1502038648137287805292931)
            ·
              refine ⟨2253057972205931707939397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502038648137287805292931 2253057972205931707939397)
              ·
                refine ⟨422448369788612195238637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2253057972205931707939397 422448369788612195238637)
                ·
                  refine ⟨158418138670729573214489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422448369788612195238637 158418138670729573214489)
                  ·
                    rfl

theorem cell20_347083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_347083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347083 prefixEnd_347083 := by exact prefixLift 347083
  have htrace : WordTrace (prefixWord ++ tailWord_347083) baseStart_347083 baseEnd_347083 := by
    simpa [prefixWord, tailWord_347083, baseEnd_347083] using wordTrace_append hprefix tailTrace_347083
  have hstable : (prefixWord ++ tailWord_347083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347083).length < 2 ^ (prefixWord ++ tailWord_347083).sum := by decide
  have hdescent : baseEnd_347083 < baseStart_347083 := by decide
  rcases family_descends (prefixWord ++ tailWord_347083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347086 : List Nat := [4, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_347086 : Nat := 118140960795 + 347086 * 2 ^ 59
def prefixEnd_347086 : Nat := 4983230072969 + 3 ^ 40 * 347086 * 2
def baseEnd_347086 : Nat := 158419507952474896114477

theorem tailTrace_347086 : CollatzResearch.WordTrace tailWord_347086 prefixEnd_347086 158419507952474896114477 := by
  unfold tailWord_347086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582408302571771801822639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8439510947049449609720741 1582408302571771801822639)
  ·
    refine ⟨2373612453857657702733959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1582408302571771801822639 2373612453857657702733959)
    ·
      refine ⟨3560418680786486554100939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2373612453857657702733959 3560418680786486554100939)
      ·
        refine ⟨5340628021179729831151409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560418680786486554100939 5340628021179729831151409)
        ·
          refine ⟨4005471015884797373363557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5340628021179729831151409 4005471015884797373363557)
          ·
            refine ⟨751025815478399507505667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4005471015884797373363557 751025815478399507505667)
            ·
              refine ⟨1126538723217599261258501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751025815478399507505667 1126538723217599261258501)
              ·
                refine ⟨211226010603299861485969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1126538723217599261258501 211226010603299861485969)
                ·
                  refine ⟨158419507952474896114477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211226010603299861485969 158419507952474896114477)
                  ·
                    rfl

theorem cell20_347086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_347086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347086 prefixEnd_347086 := by exact prefixLift 347086
  have htrace : WordTrace (prefixWord ++ tailWord_347086) baseStart_347086 baseEnd_347086 := by
    simpa [prefixWord, tailWord_347086, baseEnd_347086] using wordTrace_append hprefix tailTrace_347086
  have hstable : (prefixWord ++ tailWord_347086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347086).length < 2 ^ (prefixWord ++ tailWord_347086).sum := by decide
  have hdescent : baseEnd_347086 < baseStart_347086 := by decide
  rcases family_descends (prefixWord ++ tailWord_347086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347093 : List Nat := [1, 3, 2, 3, 3, 2, 1, 5]
def baseStart_347093 : Nat := 118140960795 + 347093 * 2 ^ 59
def prefixEnd_347093 : Nat := 4983230072969 + 3 ^ 40 * 347093 * 2
def baseEnd_347093 : Nat := 52807567647737994293705

theorem tailTrace_347093 : CollatzResearch.WordTrace tailWord_347093 prefixEnd_347093 52807567647737994293705 := by
  unfold tailWord_347093
  simp only [CollatzResearch.WordTrace]
  refine ⟨12659521731548814610085933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8439681154365876406723955 12659521731548814610085933)
  ·
    refine ⟨4747320649330805478782225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12659521731548814610085933 4747320649330805478782225)
    ·
      refine ⟨3560490486998104109086669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4747320649330805478782225 3560490486998104109086669)
      ·
        refine ⟨1335183932624289040907501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3560490486998104109086669 1335183932624289040907501)
        ·
          refine ⟨500693974734108390340313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1335183932624289040907501 500693974734108390340313)
          ·
            refine ⟨375520481050581292755235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500693974734108390340313 375520481050581292755235)
            ·
              refine ⟨563280721575871939132853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375520481050581292755235 563280721575871939132853)
              ·
                refine ⟨52807567647737994293705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 563280721575871939132853 52807567647737994293705)
                ·
                  rfl

theorem cell20_347093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 5].length) (baseStart_347093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347093 prefixEnd_347093 := by exact prefixLift 347093
  have htrace : WordTrace (prefixWord ++ tailWord_347093) baseStart_347093 baseEnd_347093 := by
    simpa [prefixWord, tailWord_347093, baseEnd_347093] using wordTrace_append hprefix tailTrace_347093
  have hstable : (prefixWord ++ tailWord_347093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347093).length < 2 ^ (prefixWord ++ tailWord_347093).sum := by decide
  have hdescent : baseEnd_347093 < baseStart_347093 := by decide
  rcases family_descends (prefixWord ++ tailWord_347093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347104 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_347104 : Nat := 118140960795 + 347104 * 2 ^ 59
def prefixEnd_347104 : Nat := 4983230072969 + 3 ^ 40 * 347104 * 2
def baseEnd_347104 : Nat := 158427723642946833514403

theorem tailTrace_347104 : CollatzResearch.WordTrace tailWord_347104 prefixEnd_347104 158427723642946833514403 := by
  unfold tailWord_347104
  simp only [CollatzResearch.WordTrace]
  refine ⟨6329961467254481744368183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8439948623005975659157577 6329961467254481744368183)
  ·
    refine ⟨9494942200881722616552275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6329961467254481744368183 9494942200881722616552275)
    ·
      refine ⟨14242413301322583924828413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9494942200881722616552275 14242413301322583924828413)
      ·
        refine ⟨5340904987995968971810655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14242413301322583924828413 5340904987995968971810655)
        ·
          refine ⟨8011357481993953457715983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340904987995968971810655 8011357481993953457715983)
          ·
            refine ⟨12017036222990930186573975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8011357481993953457715983 12017036222990930186573975)
            ·
              refine ⟨18025554334486395279860963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12017036222990930186573975 18025554334486395279860963)
              ·
                refine ⟨27038331501729592919791445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18025554334486395279860963 27038331501729592919791445)
                ·
                  refine ⟨158427723642946833514403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27038331501729592919791445 158427723642946833514403)
                  ·
                    rfl

theorem cell20_347104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_347104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347104 prefixEnd_347104 := by exact prefixLift 347104
  have htrace : WordTrace (prefixWord ++ tailWord_347104) baseStart_347104 baseEnd_347104 := by
    simpa [prefixWord, tailWord_347104, baseEnd_347104] using wordTrace_append hprefix tailTrace_347104
  have hstable : (prefixWord ++ tailWord_347104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347104).length < 2 ^ (prefixWord ++ tailWord_347104).sum := by decide
  have hdescent : baseEnd_347104 < baseStart_347104 := by decide
  rcases family_descends (prefixWord ++ tailWord_347104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347134 : List Nat := [4, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_347134 : Nat := 118140960795 + 347134 * 2 ^ 59
def prefixEnd_347134 : Nat := 4983230072969 + 3 ^ 40 * 347134 * 2
def baseEnd_347134 : Nat := 158441416460400062514281

theorem tailTrace_347134 : CollatzResearch.WordTrace tailWord_347134 prefixEnd_347134 158441416460400062514281 := by
  unfold tailWord_347134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1582627140550034826541057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8440678082933519074885637 1582627140550034826541057)
  ·
    refine ⟨1186970355412526119905793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1582627140550034826541057 1186970355412526119905793)
    ·
      refine ⟨890227766559394589929345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1186970355412526119905793 890227766559394589929345)
      ·
        refine ⟨667670824919545942447009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 890227766559394589929345 667670824919545942447009)
        ·
          refine ⟨500753118689659456835257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 667670824919545942447009 500753118689659456835257)
          ·
            refine ⟨375564839017244592626443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 500753118689659456835257 375564839017244592626443)
            ·
              refine ⟨563347258525866888939665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375564839017244592626443 563347258525866888939665)
              ·
                refine ⟨422510443894400166704749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563347258525866888939665 422510443894400166704749)
                ·
                  refine ⟨158441416460400062514281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422510443894400166704749 158441416460400062514281)
                  ·
                    rfl

theorem cell20_347134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_347134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347134 prefixEnd_347134 := by exact prefixLift 347134
  have htrace : WordTrace (prefixWord ++ tailWord_347134) baseStart_347134 baseEnd_347134 := by
    simpa [prefixWord, tailWord_347134, baseEnd_347134] using wordTrace_append hprefix tailTrace_347134
  have hstable : (prefixWord ++ tailWord_347134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347134).length < 2 ^ (prefixWord ++ tailWord_347134).sum := by decide
  have hdescent : baseEnd_347134 < baseStart_347134 := by decide
  rcases family_descends (prefixWord ++ tailWord_347134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347169 : List Nat := [1, 2, 3, 2, 3, 3, 2, 4]
def baseStart_347169 : Nat := 118140960795 + 347169 * 2 ^ 59
def prefixEnd_347169 : Nat := 4983230072969 + 3 ^ 40 * 347169 * 2
def baseEnd_347169 : Nat := 52819130471365165449157

theorem tailTrace_347169 : CollatzResearch.WordTrace tailWord_347169 prefixEnd_347169 52819130471365165449157 := by
  unfold tailWord_347169
  simp only [CollatzResearch.WordTrace]
  refine ⟨12662293679273479589852561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8441529119515653059901707 12662293679273479589852561)
  ·
    refine ⟨9496720259455109692389421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12662293679273479589852561 9496720259455109692389421)
    ·
      refine ⟨3561270097295666134646033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9496720259455109692389421 3561270097295666134646033)
      ·
        refine ⟨2670952572971749600984525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3561270097295666134646033 2670952572971749600984525)
        ·
          refine ⟨1001607214864406100369197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2670952572971749600984525 1001607214864406100369197)
          ·
            refine ⟨375602705574152287638449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1001607214864406100369197 375602705574152287638449)
            ·
              refine ⟨281702029180614215728837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375602705574152287638449 281702029180614215728837)
              ·
                refine ⟨52819130471365165449157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281702029180614215728837 52819130471365165449157)
                ·
                  rfl

theorem cell20_347169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 4].length) (baseStart_347169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347169 prefixEnd_347169 := by exact prefixLift 347169
  have htrace : WordTrace (prefixWord ++ tailWord_347169) baseStart_347169 baseEnd_347169 := by
    simpa [prefixWord, tailWord_347169, baseEnd_347169] using wordTrace_append hprefix tailTrace_347169
  have hstable : (prefixWord ++ tailWord_347169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347169).length < 2 ^ (prefixWord ++ tailWord_347169).sum := by decide
  have hdescent : baseEnd_347169 < baseStart_347169 := by decide
  rcases family_descends (prefixWord ++ tailWord_347169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347173 : List Nat := [1, 3, 1, 2, 2, 2, 3, 6]
def baseStart_347173 : Nat := 118140960795 + 347173 * 2 ^ 59
def prefixEnd_347173 : Nat := 4983230072969 + 3 ^ 40 * 347173 * 2
def baseEnd_347173 : Nat := 52819739041029753404707

theorem tailTrace_347173 : CollatzResearch.WordTrace tailWord_347173 prefixEnd_347173 52819739041029753404707 := by
  unfold tailWord_347173
  simp only [CollatzResearch.WordTrace]
  refine ⟨12662439571258988272998173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8441626380839325515332115 12662439571258988272998173)
  ·
    refine ⟨4748414839222120602374315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12662439571258988272998173 4748414839222120602374315)
    ·
      refine ⟨7122622258833180903561473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748414839222120602374315 7122622258833180903561473)
      ·
        refine ⟨5341966694124885677671105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7122622258833180903561473 5341966694124885677671105)
        ·
          refine ⟨4006475020593664258253329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5341966694124885677671105 4006475020593664258253329)
          ·
            refine ⟨3004856265445248193689997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4006475020593664258253329 3004856265445248193689997)
            ·
              refine ⟨1126821099541968072633749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3004856265445248193689997 1126821099541968072633749)
              ·
                refine ⟨52819739041029753404707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1126821099541968072633749 52819739041029753404707)
                ·
                  rfl

theorem cell20_347173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_347173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347173 prefixEnd_347173 := by exact prefixLift 347173
  have htrace : WordTrace (prefixWord ++ tailWord_347173) baseStart_347173 baseEnd_347173 := by
    simpa [prefixWord, tailWord_347173, baseEnd_347173] using wordTrace_append hprefix tailTrace_347173
  have hstable : (prefixWord ++ tailWord_347173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347173).length < 2 ^ (prefixWord ++ tailWord_347173).sum := by decide
  have hdescent : baseEnd_347173 < baseStart_347173 := by decide
  rcases family_descends (prefixWord ++ tailWord_347173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347180 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_347180 : Nat := 118140960795 + 347180 * 2 ^ 59
def prefixEnd_347180 : Nat := 4983230072969 + 3 ^ 40 * 347180 * 2
def baseEnd_347180 : Nat := 158462412113828346980759

theorem tailTrace_347180 : CollatzResearch.WordTrace tailWord_347180 prefixEnd_347180 158462412113828346980759 := by
  unfold tailWord_347180
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331347441116814234251497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8441796588155752312335329 6331347441116814234251497)
  ·
    refine ⟨4748510580837610675688623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6331347441116814234251497 4748510580837610675688623)
    ·
      refine ⟨7122765871256416013532935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4748510580837610675688623 7122765871256416013532935)
      ·
        refine ⟨10684148806884624020299403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7122765871256416013532935 10684148806884624020299403)
        ·
          refine ⟨16026223210326936030449105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10684148806884624020299403 16026223210326936030449105)
          ·
            refine ⟨12019667407745202022836829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16026223210326936030449105 12019667407745202022836829)
            ·
              refine ⟨4507375277904450758563811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12019667407745202022836829 4507375277904450758563811)
              ·
                refine ⟨6761062916856676137845717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4507375277904450758563811 6761062916856676137845717)
                ·
                  refine ⟨158462412113828346980759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6761062916856676137845717 158462412113828346980759)
                  ·
                    rfl

theorem cell20_347180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_347180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347180 prefixEnd_347180 := by exact prefixLift 347180
  have htrace : WordTrace (prefixWord ++ tailWord_347180) baseStart_347180 baseEnd_347180 := by
    simpa [prefixWord, tailWord_347180, baseEnd_347180] using wordTrace_append hprefix tailTrace_347180
  have hstable : (prefixWord ++ tailWord_347180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347180).length < 2 ^ (prefixWord ++ tailWord_347180).sum := by decide
  have hdescent : baseEnd_347180 < baseStart_347180 := by decide
  rcases family_descends (prefixWord ++ tailWord_347180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347190 : List Nat := [5, 1, 2, 1, 1, 2, 8]
def baseStart_347190 : Nat := 118140960795 + 347190 * 2 ^ 59
def prefixEnd_347190 : Nat := 4983230072969 + 3 ^ 40 * 347190 * 2
def baseEnd_347190 : Nat := 17607441820701417405265

theorem tailTrace_347190 : CollatzResearch.WordTrace tailWord_347190 prefixEnd_347190 17607441820701417405265 := by
  unfold tailWord_347190
  simp only [CollatzResearch.WordTrace]
  refine ⟨791441225762337511022939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8442039741464933450911349 791441225762337511022939)
  ·
    refine ⟨1187161838643506266534409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 791441225762337511022939 1187161838643506266534409)
    ·
      refine ⟨890371378982629699900807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1187161838643506266534409 890371378982629699900807)
      ·
        refine ⟨1335557068473944549851211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 890371378982629699900807 1335557068473944549851211)
        ·
          refine ⟨2003335602710916824776817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335557068473944549851211 2003335602710916824776817)
          ·
            refine ⟨1502501702033187618582613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003335602710916824776817 1502501702033187618582613)
            ·
              refine ⟨17607441820701417405265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1502501702033187618582613 17607441820701417405265)
              ·
                rfl

theorem cell20_347190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 8].length) (baseStart_347190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347190 prefixEnd_347190 := by exact prefixLift 347190
  have htrace : WordTrace (prefixWord ++ tailWord_347190) baseStart_347190 baseEnd_347190 := by
    simpa [prefixWord, tailWord_347190, baseEnd_347190] using wordTrace_append hprefix tailTrace_347190
  have hstable : (prefixWord ++ tailWord_347190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347190).length < 2 ^ (prefixWord ++ tailWord_347190).sum := by decide
  have hdescent : baseEnd_347190 < baseStart_347190 := by decide
  rcases family_descends (prefixWord ++ tailWord_347190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347197 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_347197 : Nat := 118140960795 + 347197 * 2 ^ 59
def prefixEnd_347197 : Nat := 4983230072969 + 3 ^ 40 * 347197 * 2
def baseEnd_347197 : Nat := 158470171377051843414023

theorem tailTrace_347197 : CollatzResearch.WordTrace tailWord_347197 prefixEnd_347197 158470171377051843414023 := by
  unfold tailWord_347197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663314923172040371871845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8442209948781360247914563 12663314923172040371871845)
  ·
    refine ⟨2374371548094757569725971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12663314923172040371871845 2374371548094757569725971)
    ·
      refine ⟨3561557322142136354588957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374371548094757569725971 3561557322142136354588957)
      ·
        refine ⟨1335583995803301132970859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3561557322142136354588957 1335583995803301132970859)
        ·
          refine ⟨2003375993704951699456289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1335583995803301132970859 2003375993704951699456289)
          ·
            refine ⟨1502531995278713774592217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003375993704951699456289 1502531995278713774592217)
            ·
              refine ⟨1126898996459035330944163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502531995278713774592217 1126898996459035330944163)
              ·
                refine ⟨1690348494688552996416245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1126898996459035330944163 1690348494688552996416245)
                ·
                  refine ⟨158470171377051843414023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690348494688552996416245 158470171377051843414023)
                  ·
                    rfl

theorem cell20_347197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_347197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347197 prefixEnd_347197 := by exact prefixLift 347197
  have htrace : WordTrace (prefixWord ++ tailWord_347197) baseStart_347197 baseEnd_347197 := by
    simpa [prefixWord, tailWord_347197, baseEnd_347197] using wordTrace_append hprefix tailTrace_347197
  have hstable : (prefixWord ++ tailWord_347197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347197).length < 2 ^ (prefixWord ++ tailWord_347197).sum := by decide
  have hdescent : baseEnd_347197 < baseStart_347197 := by decide
  rcases family_descends (prefixWord ++ tailWord_347197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347200 : List Nat := [2, 1, 1, 2, 2, 3, 5, 2, 2]
def baseStart_347200 : Nat := 118140960795 + 347200 * 2 ^ 59
def prefixEnd_347200 : Nat := 4983230072969 + 3 ^ 40 * 347200 * 2
def baseEnd_347200 : Nat := 158471540658797166314011

theorem tailTrace_347200 : CollatzResearch.WordTrace tailWord_347200 prefixEnd_347200 158471540658797166314011 := by
  unfold tailWord_347200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331712171080585942115527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8442282894774114589487369 6331712171080585942115527)
  ·
    refine ⟨9497568256620878913173291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6331712171080585942115527 9497568256620878913173291)
    ·
      refine ⟨14246352384931318369759937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9497568256620878913173291 14246352384931318369759937)
      ·
        refine ⟨10684764288698488777319953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14246352384931318369759937 10684764288698488777319953)
        ·
          refine ⟨8013573216523866582989965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10684764288698488777319953 8013573216523866582989965)
          ·
            refine ⟨3005089956196449968621237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8013573216523866582989965 3005089956196449968621237)
            ·
              refine ⟨281727183393417184558241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3005089956196449968621237 281727183393417184558241)
              ·
                refine ⟨211295387545062888418681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281727183393417184558241 211295387545062888418681)
                ·
                  refine ⟨158471540658797166314011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211295387545062888418681 158471540658797166314011)
                  ·
                    rfl

theorem cell20_347200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_347200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347200 prefixEnd_347200 := by exact prefixLift 347200
  have htrace : WordTrace (prefixWord ++ tailWord_347200) baseStart_347200 baseEnd_347200 := by
    simpa [prefixWord, tailWord_347200, baseEnd_347200] using wordTrace_append hprefix tailTrace_347200
  have hstable : (prefixWord ++ tailWord_347200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347200).length < 2 ^ (prefixWord ++ tailWord_347200).sum := by decide
  have hdescent : baseEnd_347200 < baseStart_347200 := by decide
  rcases family_descends (prefixWord ++ tailWord_347200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347256 : List Nat := [2, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_347256 : Nat := 118140960795 + 347256 * 2 ^ 59
def prefixEnd_347256 : Nat := 4983230072969 + 3 ^ 40 * 347256 * 2
def baseEnd_347256 : Nat := 158497100584709860447115

theorem tailTrace_347256 : CollatzResearch.WordTrace tailWord_347256 prefixEnd_347256 158497100584709860447115 := by
  unfold tailWord_347256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332733414979146724134811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8443644553305528965513081 6332733414979146724134811)
  ·
    refine ⟨9499100122468720086202217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6332733414979146724134811 9499100122468720086202217)
    ·
      refine ⟨7124325091851540064651663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9499100122468720086202217 7124325091851540064651663)
      ·
        refine ⟨10686487637777310096977495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7124325091851540064651663 10686487637777310096977495)
        ·
          refine ⟨16029731456665965145466243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10686487637777310096977495 16029731456665965145466243)
          ·
            refine ⟨24044597184998947718199365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16029731456665965145466243 24044597184998947718199365)
            ·
              refine ⟨4508361972187302697162381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24044597184998947718199365 4508361972187302697162381)
              ·
                refine ⟨1690635739570238511435893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4508361972187302697162381 1690635739570238511435893)
                ·
                  refine ⟨158497100584709860447115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690635739570238511435893 158497100584709860447115)
                  ·
                    rfl

theorem cell20_347256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_347256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347256 prefixEnd_347256 := by exact prefixLift 347256
  have htrace : WordTrace (prefixWord ++ tailWord_347256) baseStart_347256 baseEnd_347256 := by
    simpa [prefixWord, tailWord_347256, baseEnd_347256] using wordTrace_append hprefix tailTrace_347256
  have hstable : (prefixWord ++ tailWord_347256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347256).length < 2 ^ (prefixWord ++ tailWord_347256).sum := by decide
  have hdescent : baseEnd_347256 < baseStart_347256 := by decide
  rcases family_descends (prefixWord ++ tailWord_347256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347263 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_347263 : Nat := 118140960795 + 347263 * 2 ^ 59
def prefixEnd_347263 : Nat := 4983230072969 + 3 ^ 40 * 347263 * 2
def baseEnd_347263 : Nat := 158500295575448947213753

theorem tailTrace_347263 : CollatzResearch.WordTrace tailWord_347263 prefixEnd_347263 158500295575448947213753 := by
  unfold tailWord_347263
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665722140932933643774443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8443814760621955762516295 12665722140932933643774443)
  ·
    refine ⟨18998583211399400465661665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12665722140932933643774443 18998583211399400465661665)
    ·
      refine ⟨14248937408549550349246249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18998583211399400465661665 14248937408549550349246249)
      ·
        refine ⟨10686703056412162761934687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14248937408549550349246249 10686703056412162761934687)
        ·
          refine ⟨16030054584618244142902031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10686703056412162761934687 16030054584618244142902031)
          ·
            refine ⟨24045081876927366214353047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16030054584618244142902031 24045081876927366214353047)
            ·
              refine ⟨36067622815391049321529571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24045081876927366214353047 36067622815391049321529571)
              ·
                refine ⟨54101434223086573982294357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36067622815391049321529571 54101434223086573982294357)
                ·
                  refine ⟨158500295575448947213753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 54101434223086573982294357 158500295575448947213753)
                  ·
                    rfl

theorem cell20_347263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_347263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347263 prefixEnd_347263 := by exact prefixLift 347263
  have htrace : WordTrace (prefixWord ++ tailWord_347263) baseStart_347263 baseEnd_347263 := by
    simpa [prefixWord, tailWord_347263, baseEnd_347263] using wordTrace_append hprefix tailTrace_347263
  have hstable : (prefixWord ++ tailWord_347263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347263).length < 2 ^ (prefixWord ++ tailWord_347263).sum := by decide
  have hdescent : baseEnd_347263 < baseStart_347263 := by decide
  rcases family_descends (prefixWord ++ tailWord_347263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347273 : List Nat := [1, 2, 1, 1, 4, 3, 2, 3, 3]
def baseStart_347273 : Nat := 118140960795 + 347273 * 2 ^ 59
def prefixEnd_347273 : Nat := 4983230072969 + 3 ^ 40 * 347273 * 2
def baseEnd_347273 : Nat := 158504859847933356880379

theorem tailTrace_347273 : CollatzResearch.WordTrace tailWord_347273 prefixEnd_347273 158504859847933356880379 := by
  unfold tailWord_347273
  simp only [CollatzResearch.WordTrace]
  refine ⟨12666086870896705351638473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8444057913931136901092315 12666086870896705351638473)
  ·
    refine ⟨9499565153172529013728855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12666086870896705351638473 9499565153172529013728855)
    ·
      refine ⟨14249347729758793520593283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499565153172529013728855 14249347729758793520593283)
      ·
        refine ⟨21374021594638190280889925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14249347729758793520593283 21374021594638190280889925)
        ·
          refine ⟨4007629048994660677666861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21374021594638190280889925 4007629048994660677666861)
          ·
            refine ⟨1502860893372997754125073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4007629048994660677666861 1502860893372997754125073)
            ·
              refine ⟨1127145670029748315593805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1502860893372997754125073 1127145670029748315593805)
              ·
                refine ⟨422679626261155618347677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1127145670029748315593805 422679626261155618347677)
                ·
                  refine ⟨158504859847933356880379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422679626261155618347677 158504859847933356880379)
                  ·
                    rfl

theorem cell20_347273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_347273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347273 prefixEnd_347273 := by exact prefixLift 347273
  have htrace : WordTrace (prefixWord ++ tailWord_347273) baseStart_347273 baseEnd_347273 := by
    simpa [prefixWord, tailWord_347273, baseEnd_347273] using wordTrace_append hprefix tailTrace_347273
  have hstable : (prefixWord ++ tailWord_347273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347273).length < 2 ^ (prefixWord ++ tailWord_347273).sum := by decide
  have hdescent : baseEnd_347273 < baseStart_347273 := by decide
  rcases family_descends (prefixWord ++ tailWord_347273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347311 : List Nat := [1, 1, 2, 1, 2, 3, 5, 2, 3]
def baseStart_347311 : Nat := 118140960795 + 347311 * 2 ^ 59
def prefixEnd_347311 : Nat := 4983230072969 + 3 ^ 40 * 347311 * 2
def baseEnd_347311 : Nat := 158522204083374113613557

theorem tailTrace_347311 : CollatzResearch.WordTrace tailWord_347311 prefixEnd_347311 158522204083374113613557 := by
  unfold tailWord_347311
  simp only [CollatzResearch.WordTrace]
  refine ⟨12667472844759037841521787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8444981896506025227681191 12667472844759037841521787)
  ·
    refine ⟨19001209267138556762282681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12667472844759037841521787 19001209267138556762282681)
    ·
      refine ⟨14250906950353917571712011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19001209267138556762282681 14250906950353917571712011)
      ·
        refine ⟨21376360425530876357568017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14250906950353917571712011 21376360425530876357568017)
        ·
          refine ⟨16032270319148157268176013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21376360425530876357568017 16032270319148157268176013)
          ·
            refine ⟨6012101369680558975566005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16032270319148157268176013 6012101369680558975566005)
            ·
              refine ⟨563634503407552403959313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6012101369680558975566005 563634503407552403959313)
              ·
                refine ⟨422725877555664302969485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563634503407552403959313 422725877555664302969485)
                ·
                  refine ⟨158522204083374113613557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422725877555664302969485 158522204083374113613557)
                  ·
                    rfl

theorem cell20_347311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_347311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347311 prefixEnd_347311 := by exact prefixLift 347311
  have htrace : WordTrace (prefixWord ++ tailWord_347311) baseStart_347311 baseEnd_347311 := by
    simpa [prefixWord, tailWord_347311, baseEnd_347311] using wordTrace_append hprefix tailTrace_347311
  have hstable : (prefixWord ++ tailWord_347311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347311).length < 2 ^ (prefixWord ++ tailWord_347311).sum := by decide
  have hdescent : baseEnd_347311 < baseStart_347311 := by decide
  rcases family_descends (prefixWord ++ tailWord_347311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347334 : List Nat := [6, 1, 2, 2, 1, 2, 2, 4]
def baseStart_347334 : Nat := 118140960795 + 347334 * 2 ^ 59
def prefixEnd_347334 : Nat := 4983230072969 + 3 ^ 40 * 347334 * 2
def baseEnd_347334 : Nat := 52844233970029418615599

theorem tailTrace_347334 : CollatzResearch.WordTrace tailWord_347334 prefixEnd_347334 52844233970029418615599 := by
  unfold tailWord_347334
  simp only [CollatzResearch.WordTrace]
  refine ⟨395884741364866024050283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8445541149117141846406037 395884741364866024050283)
  ·
    refine ⟨593827112047299036075425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395884741364866024050283 593827112047299036075425)
    ·
      refine ⟨445370334035474277056569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 593827112047299036075425 445370334035474277056569)
      ·
        refine ⟨334027750526605707792427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445370334035474277056569 334027750526605707792427)
        ·
          refine ⟨501041625789908561688641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334027750526605707792427 501041625789908561688641)
          ·
            refine ⟨375781219342431421266481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501041625789908561688641 375781219342431421266481)
            ·
              refine ⟨281835914506823565949861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375781219342431421266481 281835914506823565949861)
              ·
                refine ⟨52844233970029418615599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281835914506823565949861 52844233970029418615599)
                ·
                  rfl

theorem cell20_347334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_347334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347334 prefixEnd_347334 := by exact prefixLift 347334
  have htrace : WordTrace (prefixWord ++ tailWord_347334) baseStart_347334 baseEnd_347334 := by
    simpa [prefixWord, tailWord_347334, baseEnd_347334] using wordTrace_append hprefix tailTrace_347334
  have hstable : (prefixWord ++ tailWord_347334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347334).length < 2 ^ (prefixWord ++ tailWord_347334).sum := by decide
  have hdescent : baseEnd_347334 < baseStart_347334 := by decide
  rcases family_descends (prefixWord ++ tailWord_347334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347339 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_347339 : Nat := 118140960795 + 347339 * 2 ^ 59
def prefixEnd_347339 : Nat := 4983230072969 + 3 ^ 40 * 347339 * 2
def baseEnd_347339 : Nat := 158534984046330460680109

theorem tailTrace_347339 : CollatzResearch.WordTrace tailWord_347339 prefixEnd_347339 158534984046330460680109 := by
  unfold tailWord_347339
  simp only [CollatzResearch.WordTrace]
  refine ⟨12668494088657598623541071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8445662725771732415694047 12668494088657598623541071)
  ·
    refine ⟨19002741132986397935311607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12668494088657598623541071 19002741132986397935311607)
    ·
      refine ⟨28504111699479596902967411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19002741132986397935311607 28504111699479596902967411)
      ·
        refine ⟨42756167549219395354451117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28504111699479596902967411 42756167549219395354451117)
        ·
          refine ⟨16033562830957273257919169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42756167549219395354451117 16033562830957273257919169)
          ·
            refine ⟨12025172123217954943439377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16033562830957273257919169 12025172123217954943439377)
            ·
              refine ⟨9018879092413466207579533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12025172123217954943439377 9018879092413466207579533)
              ·
                refine ⟨3382079659655049827842325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9018879092413466207579533 3382079659655049827842325)
                ·
                  refine ⟨158534984046330460680109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3382079659655049827842325 158534984046330460680109)
                  ·
                    rfl

theorem cell20_347339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_347339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347339 prefixEnd_347339 := by exact prefixLift 347339
  have htrace : WordTrace (prefixWord ++ tailWord_347339) baseStart_347339 baseEnd_347339 := by
    simpa [prefixWord, tailWord_347339, baseEnd_347339] using wordTrace_append hprefix tailTrace_347339
  have hstable : (prefixWord ++ tailWord_347339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347339).length < 2 ^ (prefixWord ++ tailWord_347339).sum := by decide
  have hdescent : baseEnd_347339 < baseStart_347339 := by decide
  rcases family_descends (prefixWord ++ tailWord_347339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347342 : List Nat := [4, 1, 1, 1, 5, 1, 1, 6]
def baseStart_347342 : Nat := 118140960795 + 347342 * 2 ^ 59
def prefixEnd_347342 : Nat := 4983230072969 + 3 ^ 40 * 347342 * 2
def baseEnd_347342 : Nat := 52845451109358594526699

theorem tailTrace_347342 : CollatzResearch.WordTrace tailWord_347342 prefixEnd_347342 52845451109358594526699 := by
  unfold tailWord_347342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583575438455841266987535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8445735671764486757266853 1583575438455841266987535)
  ·
    refine ⟨2375363157683761900481303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1583575438455841266987535 2375363157683761900481303)
    ·
      refine ⟨3563044736525642850721955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375363157683761900481303 3563044736525642850721955)
      ·
        refine ⟨5344567104788464276082933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563044736525642850721955 5344567104788464276082933)
        ·
          refine ⟨501053166073918525882775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5344567104788464276082933 501053166073918525882775)
          ·
            refine ⟨751579749110877788824163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501053166073918525882775 751579749110877788824163)
            ·
              refine ⟨1127369623666316683236245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751579749110877788824163 1127369623666316683236245)
              ·
                refine ⟨52845451109358594526699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1127369623666316683236245 52845451109358594526699)
                ·
                  rfl

theorem cell20_347342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_347342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347342 prefixEnd_347342 := by exact prefixLift 347342
  have htrace : WordTrace (prefixWord ++ tailWord_347342) baseStart_347342 baseEnd_347342 := by
    simpa [prefixWord, tailWord_347342, baseEnd_347342] using wordTrace_append hprefix tailTrace_347342
  have hstable : (prefixWord ++ tailWord_347342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347342).length < 2 ^ (prefixWord ++ tailWord_347342).sum := by decide
  have hdescent : baseEnd_347342 < baseStart_347342 := by decide
  rcases family_descends (prefixWord ++ tailWord_347342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347348 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 2]
def baseStart_347348 : Nat := 118140960795 + 347348 * 2 ^ 59
def prefixEnd_347348 : Nat := 4983230072969 + 3 ^ 40 * 347348 * 2
def baseEnd_347348 : Nat := 158539091891566429380073

theorem tailTrace_347348 : CollatzResearch.WordTrace tailWord_347348 prefixEnd_347348 158539091891566429380073 := by
  unfold tailWord_347348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334411172812496580309349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8445881563749995440412465 6334411172812496580309349)
  ·
    refine ⟨1187702094902343108808003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6334411172812496580309349 1187702094902343108808003)
    ·
      refine ⟨1781553142353514663212005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187702094902343108808003 1781553142353514663212005)
      ·
        refine ⟨334041214191283999352251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1781553142353514663212005 334041214191283999352251)
        ·
          refine ⟨501061821286925999028377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334041214191283999352251 501061821286925999028377)
          ·
            refine ⟨375796365965194499271283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501061821286925999028377 375796365965194499271283)
            ·
              refine ⟨563694548947791748906925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375796365965194499271283 563694548947791748906925)
              ·
                refine ⟨211385455855421905840097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563694548947791748906925 211385455855421905840097)
                ·
                  refine ⟨158539091891566429380073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211385455855421905840097 158539091891566429380073)
                  ·
                    rfl

theorem cell20_347348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_347348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347348 prefixEnd_347348 := by exact prefixLift 347348
  have htrace : WordTrace (prefixWord ++ tailWord_347348) baseStart_347348 baseEnd_347348 := by
    simpa [prefixWord, tailWord_347348, baseEnd_347348] using wordTrace_append hprefix tailTrace_347348
  have hstable : (prefixWord ++ tailWord_347348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347348).length < 2 ^ (prefixWord ++ tailWord_347348).sum := by decide
  have hdescent : baseEnd_347348 < baseStart_347348 := by decide
  rcases family_descends (prefixWord ++ tailWord_347348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347349 : List Nat := [1, 3, 2, 4, 1, 1, 1, 2, 5]
def baseStart_347349 : Nat := 118140960795 + 347349 * 2 ^ 59
def prefixEnd_347349 : Nat := 4983230072969 + 3 ^ 40 * 347349 * 2
def baseEnd_347349 : Nat := 158539548318814870346735

theorem tailTrace_347349 : CollatzResearch.WordTrace tailWord_347349 prefixEnd_347349 158539548318814870346735 := by
  unfold tailWord_347349
  simp only [CollatzResearch.WordTrace]
  refine ⟨12668858818621370331405101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8445905879080913554270067 12668858818621370331405101)
  ·
    refine ⟨4750822056983013874276913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12668858818621370331405101 4750822056983013874276913)
    ·
      refine ⟨3563116542737260405707685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4750822056983013874276913 3563116542737260405707685)
      ·
        refine ⟨668084351763236326070191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3563116542737260405707685 668084351763236326070191)
        ·
          refine ⟨1002126527644854489105287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668084351763236326070191 1002126527644854489105287)
          ·
            refine ⟨1503189791467281733657931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002126527644854489105287 1503189791467281733657931)
            ·
              refine ⟨2254784687200922600486897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503189791467281733657931 2254784687200922600486897)
              ·
                refine ⟨1691088515400691950365173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254784687200922600486897 1691088515400691950365173)
                ·
                  refine ⟨158539548318814870346735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691088515400691950365173 158539548318814870346735)
                  ·
                    rfl

theorem cell20_347349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_347349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347349 prefixEnd_347349 := by exact prefixLift 347349
  have htrace : WordTrace (prefixWord ++ tailWord_347349) baseStart_347349 baseEnd_347349 := by
    simpa [prefixWord, tailWord_347349, baseEnd_347349] using wordTrace_append hprefix tailTrace_347349
  have hstable : (prefixWord ++ tailWord_347349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347349).length < 2 ^ (prefixWord ++ tailWord_347349).sum := by decide
  have hdescent : baseEnd_347349 < baseStart_347349 := by decide
  rcases family_descends (prefixWord ++ tailWord_347349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347373 : List Nat := [1, 5, 1, 2, 2, 1, 3, 1, 4]
def baseStart_347373 : Nat := 118140960795 + 347373 * 2 ^ 59
def prefixEnd_347373 : Nat := 4983230072969 + 3 ^ 40 * 347373 * 2
def baseEnd_347373 : Nat := 158550502572777453546637

theorem tailTrace_347373 : CollatzResearch.WordTrace tailWord_347373 prefixEnd_347373 158550502572777453546637 := by
  unfold tailWord_347373
  simp only [CollatzResearch.WordTrace]
  refine ⟨12669734170534422430278773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8446489447022948286852515 12669734170534422430278773)
  ·
    refine ⟨1187787578487602102838635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12669734170534422430278773 1187787578487602102838635)
    ·
      refine ⟨1781681367731403154257953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1187787578487602102838635 1781681367731403154257953)
      ·
        refine ⟨1336261025798552365693465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1781681367731403154257953 1336261025798552365693465)
        ·
          refine ⟨1002195769348914274270099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1336261025798552365693465 1002195769348914274270099)
          ·
            refine ⟨1503293654023371411405149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002195769348914274270099 1503293654023371411405149)
            ·
              refine ⟨563735120258764279276931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1503293654023371411405149 563735120258764279276931)
              ·
                refine ⟨845602680388146418915397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563735120258764279276931 845602680388146418915397)
                ·
                  refine ⟨158550502572777453546637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845602680388146418915397 158550502572777453546637)
                  ·
                    rfl

theorem cell20_347373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_347373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347373 prefixEnd_347373 := by exact prefixLift 347373
  have htrace : WordTrace (prefixWord ++ tailWord_347373) baseStart_347373 baseEnd_347373 := by
    simpa [prefixWord, tailWord_347373, baseEnd_347373] using wordTrace_append hprefix tailTrace_347373
  have hstable : (prefixWord ++ tailWord_347373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347373).length < 2 ^ (prefixWord ++ tailWord_347373).sum := by decide
  have hdescent : baseEnd_347373 < baseStart_347373 := by decide
  rcases family_descends (prefixWord ++ tailWord_347373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347424 : List Nat := [2, 1, 1, 5, 4, 1, 2, 2, 2]
def baseStart_347424 : Nat := 118140960795 + 347424 * 2 ^ 59
def prefixEnd_347424 : Nat := 4983230072969 + 3 ^ 40 * 347424 * 2
def baseEnd_347424 : Nat := 158573780362447942846429

theorem tailTrace_347424 : CollatzResearch.WordTrace tailWord_347424 prefixEnd_347424 158573780362447942846429 := by
  unfold tailWord_347424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335797146674829070192663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8447729528899772093590217 6335797146674829070192663)
  ·
    refine ⟨9503695720012243605288995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6335797146674829070192663 9503695720012243605288995)
    ·
      refine ⟨14255543580018365407933493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9503695720012243605288995 14255543580018365407933493)
      ·
        refine ⟨1336457210626721756993765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14255543580018365407933493 1336457210626721756993765)
        ·
          refine ⟨250585726992510329436331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1336457210626721756993765 250585726992510329436331)
          ·
            refine ⟨375878590488765494154497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250585726992510329436331 375878590488765494154497)
            ·
              refine ⟨281908942866574120615873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375878590488765494154497 281908942866574120615873)
              ·
                refine ⟨211431707149930590461905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281908942866574120615873 211431707149930590461905)
                ·
                  refine ⟨158573780362447942846429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211431707149930590461905 158573780362447942846429)
                  ·
                    rfl

theorem cell20_347424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 2].length) (baseStart_347424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347424 prefixEnd_347424 := by exact prefixLift 347424
  have htrace : WordTrace (prefixWord ++ tailWord_347424) baseStart_347424 baseEnd_347424 := by
    simpa [prefixWord, tailWord_347424, baseEnd_347424] using wordTrace_append hprefix tailTrace_347424
  have hstable : (prefixWord ++ tailWord_347424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347424).length < 2 ^ (prefixWord ++ tailWord_347424).sum := by decide
  have hdescent : baseEnd_347424 < baseStart_347424 := by decide
  rcases family_descends (prefixWord ++ tailWord_347424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347449 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 4]
def baseStart_347449 : Nat := 118140960795 + 347449 * 2 ^ 59
def prefixEnd_347449 : Nat := 4983230072969 + 3 ^ 40 * 347449 * 2
def baseEnd_347449 : Nat := 158585191043658967012993

theorem tailTrace_347449 : CollatzResearch.WordTrace tailWord_347449 prefixEnd_347449 158585191043658967012993 := by
  unfold tailWord_347449
  simp only [CollatzResearch.WordTrace]
  refine ⟨12672506118259087410045401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8448337412172724940030267 12672506118259087410045401)
  ·
    refine ⟨9504379588694315557534051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12672506118259087410045401 9504379588694315557534051)
    ·
      refine ⟨14256569383041473336301077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9504379588694315557534051 14256569383041473336301077)
      ·
        refine ⟨668276689830069062639113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14256569383041473336301077 668276689830069062639113)
        ·
          refine ⟨501207517372551796979335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668276689830069062639113 501207517372551796979335)
          ·
            refine ⟨751811276058827695469003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501207517372551796979335 751811276058827695469003)
            ·
              refine ⟨1127716914088241543203505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751811276058827695469003 1127716914088241543203505)
              ·
                refine ⟨845787685566181157402629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1127716914088241543203505 845787685566181157402629)
                ·
                  refine ⟨158585191043658967012993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 845787685566181157402629 158585191043658967012993)
                  ·
                    rfl

theorem cell20_347449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_347449 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347449 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347449 prefixEnd_347449 := by exact prefixLift 347449
  have htrace : WordTrace (prefixWord ++ tailWord_347449) baseStart_347449 baseEnd_347449 := by
    simpa [prefixWord, tailWord_347449, baseEnd_347449] using wordTrace_append hprefix tailTrace_347449
  have hstable : (prefixWord ++ tailWord_347449).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347449).length < 2 ^ (prefixWord ++ tailWord_347449).sum := by decide
  have hdescent : baseEnd_347449 < baseStart_347449 := by decide
  rcases family_descends (prefixWord ++ tailWord_347449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347477 : List Nat := [1, 3, 2, 2, 3, 2, 7]
def baseStart_347477 : Nat := 118140960795 + 347477 * 2 ^ 59
def prefixEnd_347477 : Nat := 4983230072969 + 3 ^ 40 * 347477 * 2
def baseEnd_347477 : Nat := 17621996778512812675505

theorem tailTrace_347477 : CollatzResearch.WordTrace tailWord_347477 prefixEnd_347477 17621996778512812675505 := by
  unfold tailWord_347477
  simp only [CollatzResearch.WordTrace]
  refine ⟨12673527362157648192064685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8449018241438432128043123 12673527362157648192064685)
  ·
    refine ⟨4752572760809118072024257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12673527362157648192064685 4752572760809118072024257)
    ·
      refine ⟨3564429570606838554018193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4752572760809118072024257 3564429570606838554018193)
      ·
        refine ⟨2673322177955128915513645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3564429570606838554018193 2673322177955128915513645)
        ·
          refine ⟨1002495816733173343317617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2673322177955128915513645 1002495816733173343317617)
          ·
            refine ⟨751871862549880007488213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1002495816733173343317617 751871862549880007488213)
            ·
              refine ⟨17621996778512812675505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 751871862549880007488213 17621996778512812675505)
              ·
                rfl

theorem cell20_347477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_347477 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347477 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347477 prefixEnd_347477 := by exact prefixLift 347477
  have htrace : WordTrace (prefixWord ++ tailWord_347477) baseStart_347477 baseEnd_347477 := by
    simpa [prefixWord, tailWord_347477, baseEnd_347477] using wordTrace_append hprefix tailTrace_347477
  have hstable : (prefixWord ++ tailWord_347477).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347477).length < 2 ^ (prefixWord ++ tailWord_347477).sum := by decide
  have hdescent : baseEnd_347477 < baseStart_347477 := by decide
  rcases family_descends (prefixWord ++ tailWord_347477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347521 : List Nat := [1, 2, 4, 3, 2, 2, 1, 3, 2]
def baseStart_347521 : Nat := 118140960795 + 347521 * 2 ^ 59
def prefixEnd_347521 : Nat := 4983230072969 + 3 ^ 40 * 347521 * 2
def baseEnd_347521 : Nat := 158618053805546716612699

theorem tailTrace_347521 : CollatzResearch.WordTrace tailWord_347521 prefixEnd_347521 158618053805546716612699 := by
  unfold tailWord_347521
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675132173998243706666417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8450088115998829137777611 12675132173998243706666417)
  ·
    refine ⟨9506349130498682779999813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12675132173998243706666417 9506349130498682779999813)
    ·
      refine ⟨1782440461968503021249965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9506349130498682779999813 1782440461968503021249965)
      ·
        refine ⟨668415173238188632968737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1782440461968503021249965 668415173238188632968737)
        ·
          refine ⟨501311379928641474726553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668415173238188632968737 501311379928641474726553)
          ·
            refine ⟨375983534946481106044915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501311379928641474726553 375983534946481106044915)
            ·
              refine ⟨563975302419721659067373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375983534946481106044915 563975302419721659067373)
              ·
                refine ⟨211490738407395622150265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563975302419721659067373 211490738407395622150265)
                ·
                  refine ⟨158618053805546716612699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211490738407395622150265 158618053805546716612699)
                  ·
                    rfl

theorem cell20_347521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_347521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347521 prefixEnd_347521 := by exact prefixLift 347521
  have htrace : WordTrace (prefixWord ++ tailWord_347521) baseStart_347521 baseEnd_347521 := by
    simpa [prefixWord, tailWord_347521, baseEnd_347521] using wordTrace_append hprefix tailTrace_347521
  have hstable : (prefixWord ++ tailWord_347521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347521).length < 2 ^ (prefixWord ++ tailWord_347521).sum := by decide
  have hdescent : baseEnd_347521 < baseStart_347521 := by decide
  rcases family_descends (prefixWord ++ tailWord_347521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347525 : List Nat := [1, 3, 1, 1, 3, 1, 5, 3, 2]
def baseStart_347525 : Nat := 118140960795 + 347525 * 2 ^ 59
def prefixEnd_347525 : Nat := 4983230072969 + 3 ^ 40 * 347525 * 2
def baseEnd_347525 : Nat := 158619879514540480479349

theorem tailTrace_347525 : CollatzResearch.WordTrace tailWord_347525 prefixEnd_347525 158619879514540480479349 := by
  unfold tailWord_347525
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675278065983752389812029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8450185377322501593208019 12675278065983752389812029)
  ·
    refine ⟨4753229274743907146179511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12675278065983752389812029 4753229274743907146179511)
    ·
      refine ⟨7129843912115860719269267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4753229274743907146179511 7129843912115860719269267)
      ·
        refine ⟨10694765868173791078903901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7129843912115860719269267 10694765868173791078903901)
        ·
          refine ⟨4010537200565171654588963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10694765868173791078903901 4010537200565171654588963)
          ·
            refine ⟨6015805800847757481883445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4010537200565171654588963 6015805800847757481883445)
            ·
              refine ⟨563981793829477263926573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6015805800847757481883445 563981793829477263926573)
              ·
                refine ⟨211493172686053973972465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563981793829477263926573 211493172686053973972465)
                ·
                  refine ⟨158619879514540480479349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211493172686053973972465 158619879514540480479349)
                  ·
                    rfl

theorem cell20_347525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 3, 2].length) (baseStart_347525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347525 prefixEnd_347525 := by exact prefixLift 347525
  have htrace : WordTrace (prefixWord ++ tailWord_347525) baseStart_347525 baseEnd_347525 := by
    simpa [prefixWord, tailWord_347525, baseEnd_347525] using wordTrace_append hprefix tailTrace_347525
  have hstable : (prefixWord ++ tailWord_347525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347525).length < 2 ^ (prefixWord ++ tailWord_347525).sum := by decide
  have hdescent : baseEnd_347525 < baseStart_347525 := by decide
  rcases family_descends (prefixWord ++ tailWord_347525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347538 : List Nat := [3, 2, 3, 3, 1, 1, 3, 2, 2]
def baseStart_347538 : Nat := 118140960795 + 347538 * 2 ^ 59
def prefixEnd_347538 : Nat := 4983230072969 + 3 ^ 40 * 347538 * 2
def baseEnd_347538 : Nat := 158625813068770213045963

theorem tailTrace_347538 : CollatzResearch.WordTrace tailWord_347538 prefixEnd_347538 158625813068770213045963 := by
  unfold tailWord_347538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168938053734163902508817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8450501476624437073356845 3168938053734163902508817)
  ·
    refine ⟨2376703540300622926881613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3168938053734163902508817 2376703540300622926881613)
    ·
      refine ⟨891263827612733597580605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2376703540300622926881613 891263827612733597580605)
      ·
        refine ⟨334223935354775099092727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 891263827612733597580605 334223935354775099092727)
        ·
          refine ⟨501335903032162648639091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334223935354775099092727 501335903032162648639091)
          ·
            refine ⟨752003854548243972958637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501335903032162648639091 752003854548243972958637)
            ·
              refine ⟨282001445455591489859489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752003854548243972958637 282001445455591489859489)
              ·
                refine ⟨211501084091693617394617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282001445455591489859489 211501084091693617394617)
                ·
                  refine ⟨158625813068770213045963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211501084091693617394617 158625813068770213045963)
                  ·
                    rfl

theorem cell20_347538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_347538 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347538 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347538 prefixEnd_347538 := by exact prefixLift 347538
  have htrace : WordTrace (prefixWord ++ tailWord_347538) baseStart_347538 baseEnd_347538 := by
    simpa [prefixWord, tailWord_347538, baseEnd_347538] using wordTrace_append hprefix tailTrace_347538
  have hstable : (prefixWord ++ tailWord_347538).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347538).length < 2 ^ (prefixWord ++ tailWord_347538).sum := by decide
  have hdescent : baseEnd_347538 < baseStart_347538 := by decide
  rcases family_descends (prefixWord ++ tailWord_347538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347567 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_347567 : Nat := 118140960795 + 347567 * 2 ^ 59
def prefixEnd_347567 : Nat := 4983230072969 + 3 ^ 40 * 347567 * 2
def baseEnd_347567 : Nat := 158639049458975001079177

theorem tailTrace_347567 : CollatzResearch.WordTrace tailWord_347567 prefixEnd_347567 158639049458975001079177 := by
  unfold tailWord_347567
  simp only [CollatzResearch.WordTrace]
  refine ⟨12676809931831593562840955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8451206621221062375227303 12676809931831593562840955)
  ·
    refine ⟨19015214897747390344261433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12676809931831593562840955 19015214897747390344261433)
    ·
      refine ⟨14261411173310542758196075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19015214897747390344261433 14261411173310542758196075)
      ·
        refine ⟨21392116759965814137294113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14261411173310542758196075 21392116759965814137294113)
        ·
          refine ⟨16044087569974360602970585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21392116759965814137294113 16044087569974360602970585)
          ·
            refine ⟨12033065677480770452227939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16044087569974360602970585 12033065677480770452227939)
            ·
              refine ⟨18049598516221155678341909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12033065677480770452227939 18049598516221155678341909)
              ·
                refine ⟨846074930447866672422277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18049598516221155678341909 846074930447866672422277)
                ·
                  refine ⟨158639049458975001079177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846074930447866672422277 158639049458975001079177)
                  ·
                    rfl

theorem cell20_347567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_347567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347567 prefixEnd_347567 := by exact prefixLift 347567
  have htrace : WordTrace (prefixWord ++ tailWord_347567) baseStart_347567 baseEnd_347567 := by
    simpa [prefixWord, tailWord_347567, baseEnd_347567] using wordTrace_append hprefix tailTrace_347567
  have hstable : (prefixWord ++ tailWord_347567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347567).length < 2 ^ (prefixWord ++ tailWord_347567).sum := by decide
  have hdescent : baseEnd_347567 < baseStart_347567 := by decide
  rcases family_descends (prefixWord ++ tailWord_347567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347598 : List Nat := [4, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_347598 : Nat := 118140960795 + 347598 * 2 ^ 59
def prefixEnd_347598 : Nat := 4983230072969 + 3 ^ 40 * 347598 * 2
def baseEnd_347598 : Nat := 158653198703676671045717

theorem tailTrace_347598 : CollatzResearch.WordTrace tailWord_347598 prefixEnd_347598 158653198703676671045717 := by
  unfold tailWord_347598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584742574339910732152431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8451960396479523904812965 1584742574339910732152431)
  ·
    refine ⟨2377113861509866098228647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1584742574339910732152431 2377113861509866098228647)
    ·
      refine ⟨3565670792264799147342971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2377113861509866098228647 3565670792264799147342971)
      ·
        refine ⟨5348506188397198721014457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565670792264799147342971 5348506188397198721014457)
        ·
          refine ⟨4011379641297899040760843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5348506188397198721014457 4011379641297899040760843)
          ·
            refine ⟨6017069461946848561141265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011379641297899040760843 6017069461946848561141265)
            ·
              refine ⟨4512802096460136420855949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6017069461946848561141265 4512802096460136420855949)
              ·
                refine ⟨1692300786172551157820981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4512802096460136420855949 1692300786172551157820981)
                ·
                  refine ⟨158653198703676671045717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1692300786172551157820981 158653198703676671045717)
                  ·
                    rfl

theorem cell20_347598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_347598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347598 prefixEnd_347598 := by exact prefixLift 347598
  have htrace : WordTrace (prefixWord ++ tailWord_347598) baseStart_347598 baseEnd_347598 := by
    simpa [prefixWord, tailWord_347598, baseEnd_347598] using wordTrace_append hprefix tailTrace_347598
  have hstable : (prefixWord ++ tailWord_347598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347598).length < 2 ^ (prefixWord ++ tailWord_347598).sum := by decide
  have hdescent : baseEnd_347598 < baseStart_347598 := by decide
  rcases family_descends (prefixWord ++ tailWord_347598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347649 : List Nat := [1, 2, 4, 1, 5, 1, 1, 2, 3]
def baseStart_347649 : Nat := 118140960795 + 347649 * 2 ^ 59
def prefixEnd_347649 : Nat := 4983230072969 + 3 ^ 40 * 347649 * 2
def baseEnd_347649 : Nat := 158676476493347160345509

theorem tailTrace_347649 : CollatzResearch.WordTrace tailWord_347649 prefixEnd_347649 158676476493347160345509 := by
  unfold tailWord_347649
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679800717534521567326001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8453200478356347711550667 12679800717534521567326001)
  ·
    refine ⟨9509850538150891175494501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12679800717534521567326001 9509850538150891175494501)
    ·
      refine ⟨1783096975903292095405219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9509850538150891175494501 1783096975903292095405219)
      ·
        refine ⟨2674645463854938143107829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1783096975903292095405219 2674645463854938143107829)
        ·
          refine ⟨250748012236400450916359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2674645463854938143107829 250748012236400450916359)
          ·
            refine ⟨376122018354600676374539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250748012236400450916359 376122018354600676374539)
            ·
              refine ⟨564183027531901014561809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376122018354600676374539 564183027531901014561809)
              ·
                refine ⟨423137270648925760921357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564183027531901014561809 423137270648925760921357)
                ·
                  refine ⟨158676476493347160345509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423137270648925760921357 158676476493347160345509)
                  ·
                    rfl

theorem cell20_347649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 3].length) (baseStart_347649 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347649 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347649 prefixEnd_347649 := by exact prefixLift 347649
  have htrace : WordTrace (prefixWord ++ tailWord_347649) baseStart_347649 baseEnd_347649 := by
    simpa [prefixWord, tailWord_347649, baseEnd_347649] using wordTrace_append hprefix tailTrace_347649
  have hstable : (prefixWord ++ tailWord_347649).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347649).length < 2 ^ (prefixWord ++ tailWord_347649).sum := by decide
  have hdescent : baseEnd_347649 < baseStart_347649 := by decide
  rcases family_descends (prefixWord ++ tailWord_347649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347694 : List Nat := [4, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_347694 : Nat := 118140960795 + 347694 * 2 ^ 59
def prefixEnd_347694 : Nat := 4983230072969 + 3 ^ 40 * 347694 * 2
def baseEnd_347694 : Nat := 158697015719527003845325

theorem tailTrace_347694 : CollatzResearch.WordTrace tailWord_347694 prefixEnd_347694 158697015719527003845325 := by
  unfold tailWord_347694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1585180250296436781589267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8454294668247662835142757 1585180250296436781589267)
  ·
    refine ⟨2377770375444655172383901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1585180250296436781589267 2377770375444655172383901)
    ·
      refine ⟨891663890791745689643963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2377770375444655172383901 891663890791745689643963)
      ·
        refine ⟨1337495836187618534465945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891663890791745689643963 1337495836187618534465945)
        ·
          refine ⟨1003121877140713900849459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337495836187618534465945 1003121877140713900849459)
          ·
            refine ⟨1504682815711070851274189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003121877140713900849459 1504682815711070851274189)
            ·
              refine ⟨564256055891651569227821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1504682815711070851274189 564256055891651569227821)
              ·
                refine ⟨211596020959369338460433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 564256055891651569227821 211596020959369338460433)
                ·
                  refine ⟨158697015719527003845325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211596020959369338460433 158697015719527003845325)
                  ·
                    rfl

theorem cell20_347694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_347694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347694 prefixEnd_347694 := by exact prefixLift 347694
  have htrace : WordTrace (prefixWord ++ tailWord_347694) baseStart_347694 baseEnd_347694 := by
    simpa [prefixWord, tailWord_347694, baseEnd_347694] using wordTrace_append hprefix tailTrace_347694
  have hstable : (prefixWord ++ tailWord_347694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347694).length < 2 ^ (prefixWord ++ tailWord_347694).sum := by decide
  have hdescent : baseEnd_347694 < baseStart_347694 := by decide
  rcases family_descends (prefixWord ++ tailWord_347694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347705 : List Nat := [1, 2, 1, 5, 1, 4, 6]
def baseStart_347705 : Nat := 118140960795 + 347705 * 2 ^ 59
def prefixEnd_347705 : Nat := 4983230072969 + 3 ^ 40 * 347705 * 2
def baseEnd_347705 : Nat := 17633559602139983830957

theorem tailTrace_347705 : CollatzResearch.WordTrace tailWord_347705 prefixEnd_347705 17633559602139983830957 := by
  unfold tailWord_347705
  simp only [CollatzResearch.WordTrace]
  refine ⟨12681843205331643131364569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8454562136887762087576379 12681843205331643131364569)
  ·
    refine ⟨9511382403998732348523427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12681843205331643131364569 9511382403998732348523427)
    ·
      refine ⟨14267073605998098522785141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511382403998732348523427 14267073605998098522785141)
      ·
        refine ⟨1337538150562321736511107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14267073605998098522785141 1337538150562321736511107)
        ·
          refine ⟨2006307225843482604766661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337538150562321736511107 2006307225843482604766661)
          ·
            refine ⟨376182604845652988393749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2006307225843482604766661 376182604845652988393749)
            ·
              refine ⟨17633559602139983830957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 376182604845652988393749 17633559602139983830957)
              ·
                rfl

theorem cell20_347705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 6].length) (baseStart_347705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347705 prefixEnd_347705 := by exact prefixLift 347705
  have htrace : WordTrace (prefixWord ++ tailWord_347705) baseStart_347705 baseEnd_347705 := by
    simpa [prefixWord, tailWord_347705, baseEnd_347705] using wordTrace_append hprefix tailTrace_347705
  have hstable : (prefixWord ++ tailWord_347705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347705).length < 2 ^ (prefixWord ++ tailWord_347705).sum := by decide
  have hdescent : baseEnd_347705 < baseStart_347705 := by decide
  rcases family_descends (prefixWord ++ tailWord_347705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347712 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_347712 : Nat := 118140960795 + 347712 * 2 ^ 59
def prefixEnd_347712 : Nat := 4983230072969 + 3 ^ 40 * 347712 * 2
def baseEnd_347712 : Nat := 158705231409998941245251

theorem tailTrace_347712 : CollatzResearch.WordTrace tailWord_347712 prefixEnd_347712 158705231409998941245251 := by
  unfold tailWord_347712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341049258153141663434695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8454732344204188884579593 6341049258153141663434695)
  ·
    refine ⟨9511573887229712495152043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6341049258153141663434695 9511573887229712495152043)
    ·
      refine ⟨14267360830844568742728065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9511573887229712495152043 14267360830844568742728065)
      ·
        refine ⟨10700520623133426557046049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14267360830844568742728065 10700520623133426557046049)
        ·
          refine ⟨8025390467350069917784537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10700520623133426557046049 8025390467350069917784537)
          ·
            refine ⟨6019042850512552438338403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8025390467350069917784537 6019042850512552438338403)
            ·
              refine ⟨9028564275768828657507605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6019042850512552438338403 9028564275768828657507605)
              ·
                refine ⟨423213950426663843320669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9028564275768828657507605 423213950426663843320669)
                ·
                  refine ⟨158705231409998941245251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423213950426663843320669 158705231409998941245251)
                  ·
                    rfl

theorem cell20_347712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_347712 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347712 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347712 prefixEnd_347712 := by exact prefixLift 347712
  have htrace : WordTrace (prefixWord ++ tailWord_347712) baseStart_347712 baseEnd_347712 := by
    simpa [prefixWord, tailWord_347712, baseEnd_347712] using wordTrace_append hprefix tailTrace_347712
  have hstable : (prefixWord ++ tailWord_347712).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347712).length < 2 ^ (prefixWord ++ tailWord_347712).sum := by decide
  have hdescent : baseEnd_347712 < baseStart_347712 := by decide
  rcases family_descends (prefixWord ++ tailWord_347712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347788 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 3]
def baseStart_347788 : Nat := 118140960795 + 347788 * 2 ^ 59
def prefixEnd_347788 : Nat := 4983230072969 + 3 ^ 40 * 347788 * 2
def baseEnd_347788 : Nat := 158739919880880454711607

theorem tailTrace_347788 : CollatzResearch.WordTrace tailWord_347788 prefixEnd_347788 158739919880880454711607 := by
  unfold tailWord_347788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6342435232015474153318009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8456580309353965537757345 6342435232015474153318009)
  ·
    refine ⟨4756826424011605614988507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6342435232015474153318009 4756826424011605614988507)
    ·
      refine ⟨7135239636017408422482761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756826424011605614988507 7135239636017408422482761)
      ·
        refine ⟨5351429727013056316862071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7135239636017408422482761 5351429727013056316862071)
        ·
          refine ⟨8027144590519584475293107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5351429727013056316862071 8027144590519584475293107)
          ·
            refine ⟨12040716885779376712939661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8027144590519584475293107 12040716885779376712939661)
            ·
              refine ⟨4515268832167266267352373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12040716885779376712939661 4515268832167266267352373)
              ·
                refine ⟨423306453015681212564285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4515268832167266267352373 423306453015681212564285)
                ·
                  refine ⟨158739919880880454711607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423306453015681212564285 158739919880880454711607)
                  ·
                    rfl

theorem cell20_347788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_347788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347788 prefixEnd_347788 := by exact prefixLift 347788
  have htrace : WordTrace (prefixWord ++ tailWord_347788) baseStart_347788 baseEnd_347788 := by
    simpa [prefixWord, tailWord_347788, baseEnd_347788] using wordTrace_append hprefix tailTrace_347788
  have hstable : (prefixWord ++ tailWord_347788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347788).length < 2 ^ (prefixWord ++ tailWord_347788).sum := by decide
  have hdescent : baseEnd_347788 < baseStart_347788 := by decide
  rcases family_descends (prefixWord ++ tailWord_347788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347822 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_347822 : Nat := 118140960795 + 347822 * 2 ^ 59
def prefixEnd_347822 : Nat := 4983230072969 + 3 ^ 40 * 347822 * 2
def baseEnd_347822 : Nat := 158755438407327447578135

theorem tailTrace_347822 : CollatzResearch.WordTrace tailWord_347822 prefixEnd_347822 158755438407327447578135 := by
  unfold tailWord_347822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1585763818238471514171715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8457407030605181408915813 1585763818238471514171715)
  ·
    refine ⟨2378645727357707271257573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1585763818238471514171715 2378645727357707271257573)
    ·
      refine ⟨445996073879570113360795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2378645727357707271257573 445996073879570113360795)
      ·
        refine ⟨668994110819355170041193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445996073879570113360795 668994110819355170041193)
        ·
          refine ⟨501745583114516377530895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668994110819355170041193 501745583114516377530895)
          ·
            refine ⟨752618374671774566296343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501745583114516377530895 752618374671774566296343)
            ·
              refine ⟨1128927562007661849444515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752618374671774566296343 1128927562007661849444515)
              ·
                refine ⟨1693391343011492774166773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128927562007661849444515 1693391343011492774166773)
                ·
                  refine ⟨158755438407327447578135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693391343011492774166773 158755438407327447578135)
                  ·
                    rfl

theorem cell20_347822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_347822 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347822 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347822 prefixEnd_347822 := by exact prefixLift 347822
  have htrace : WordTrace (prefixWord ++ tailWord_347822) baseStart_347822 baseEnd_347822 := by
    simpa [prefixWord, tailWord_347822, baseEnd_347822] using wordTrace_append hprefix tailTrace_347822
  have hstable : (prefixWord ++ tailWord_347822).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347822).length < 2 ^ (prefixWord ++ tailWord_347822).sum := by decide
  have hdescent : baseEnd_347822 < baseStart_347822 := by decide
  rcases family_descends (prefixWord ++ tailWord_347822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347829 : List Nat := [1, 3, 3, 3, 2, 1, 2, 1, 4]
def baseStart_347829 : Nat := 118140960795 + 347829 * 2 ^ 59
def prefixEnd_347829 : Nat := 4983230072969 + 3 ^ 40 * 347829 * 2
def baseEnd_347829 : Nat := 158758633398066534344773

theorem tailTrace_347829 : CollatzResearch.WordTrace tailWord_347829 prefixEnd_347829 158758633398066534344773 := by
  unfold tailWord_347829
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686365856882412308878541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8457577237921608205919027 12686365856882412308878541)
  ·
    refine ⟨4757387196330904615829453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12686365856882412308878541 4757387196330904615829453)
    ·
      refine ⟨1784020198624089230936045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4757387196330904615829453 1784020198624089230936045)
      ·
        refine ⟨669007574484033461601017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1784020198624089230936045 669007574484033461601017)
        ·
          refine ⟨501755680863025096200763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669007574484033461601017 501755680863025096200763)
          ·
            refine ⟨752633521294537644301145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501755680863025096200763 752633521294537644301145)
            ·
              refine ⟨564475140970903233225859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752633521294537644301145 564475140970903233225859)
              ·
                refine ⟨846712711456354849838789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564475140970903233225859 846712711456354849838789)
                ·
                  refine ⟨158758633398066534344773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846712711456354849838789 158758633398066534344773)
                  ·
                    rfl

theorem cell20_347829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_347829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347829 prefixEnd_347829 := by exact prefixLift 347829
  have htrace : WordTrace (prefixWord ++ tailWord_347829) baseStart_347829 baseEnd_347829 := by
    simpa [prefixWord, tailWord_347829, baseEnd_347829] using wordTrace_append hprefix tailTrace_347829
  have hstable : (prefixWord ++ tailWord_347829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347829).length < 2 ^ (prefixWord ++ tailWord_347829).sum := by decide
  have hdescent : baseEnd_347829 < baseStart_347829 := by decide
  rcases family_descends (prefixWord ++ tailWord_347829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347833 : List Nat := [1, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_347833 : Nat := 118140960795 + 347833 * 2 ^ 59
def prefixEnd_347833 : Nat := 4983230072969 + 3 ^ 40 * 347833 * 2
def baseEnd_347833 : Nat := 158760459107060298211423

theorem tailTrace_347833 : CollatzResearch.WordTrace tailWord_347833 prefixEnd_347833 158760459107060298211423 := by
  unfold tailWord_347833
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686511748867920992024153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8457674499245280661349435 12686511748867920992024153)
  ·
    refine ⟨9514883811650940744018115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12686511748867920992024153 9514883811650940744018115)
    ·
      refine ⟨14272325717476411116027173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9514883811650940744018115 14272325717476411116027173)
      ·
        refine ⟨2676061072026827084255095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14272325717476411116027173 2676061072026827084255095)
        ·
          refine ⟨4014091608040240626382643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2676061072026827084255095 4014091608040240626382643)
          ·
            refine ⟨6021137412060360939573965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4014091608040240626382643 6021137412060360939573965)
            ·
              refine ⟨2257926529522635352340237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6021137412060360939573965 2257926529522635352340237)
              ·
                refine ⟨846722448570988257127589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2257926529522635352340237 846722448570988257127589)
                ·
                  refine ⟨158760459107060298211423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846722448570988257127589 158760459107060298211423)
                  ·
                    rfl

theorem cell20_347833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_347833 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347833 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347833 prefixEnd_347833 := by exact prefixLift 347833
  have htrace : WordTrace (prefixWord ++ tailWord_347833) baseStart_347833 baseEnd_347833 := by
    simpa [prefixWord, tailWord_347833, baseEnd_347833] using wordTrace_append hprefix tailTrace_347833
  have hstable : (prefixWord ++ tailWord_347833).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347833).length < 2 ^ (prefixWord ++ tailWord_347833).sum := by decide
  have hdescent : baseEnd_347833 < baseStart_347833 := by decide
  rcases family_descends (prefixWord ++ tailWord_347833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347840 : List Nat := [2, 1, 1, 2, 4, 1, 2, 7]
def baseStart_347840 : Nat := 118140960795 + 347840 * 2 ^ 59
def prefixEnd_347840 : Nat := 4983230072969 + 3 ^ 40 * 347840 * 2
def baseEnd_347840 : Nat := 52921218032599794992687

theorem tailTrace_347840 : CollatzResearch.WordTrace tailWord_347840 prefixEnd_347840 52921218032599794992687 := by
  unfold tailWord_347840
  simp only [CollatzResearch.WordTrace]
  refine ⟨6343383529921280593764487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8457844706561707458352649 6343383529921280593764487)
  ·
    refine ⟨9515075294881920890646731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6343383529921280593764487 9515075294881920890646731)
    ·
      refine ⟨14272612942322881335970097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9515075294881920890646731 14272612942322881335970097)
      ·
        refine ⟨10704459706742161001977573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14272612942322881335970097 10704459706742161001977573)
        ·
          refine ⟨2007086195014155187870795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10704459706742161001977573 2007086195014155187870795)
          ·
            refine ⟨3010629292521232781806193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007086195014155187870795 3010629292521232781806193)
            ·
              refine ⟨2257971969390924586354645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3010629292521232781806193 2257971969390924586354645)
              ·
                refine ⟨52921218032599794992687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2257971969390924586354645 52921218032599794992687)
                ·
                  rfl

theorem cell20_347840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_347840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347840 prefixEnd_347840 := by exact prefixLift 347840
  have htrace : WordTrace (prefixWord ++ tailWord_347840) baseStart_347840 baseEnd_347840 := by
    simpa [prefixWord, tailWord_347840, baseEnd_347840] using wordTrace_append hprefix tailTrace_347840
  have hstable : (prefixWord ++ tailWord_347840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347840).length < 2 ^ (prefixWord ++ tailWord_347840).sum := by decide
  have hdescent : baseEnd_347840 < baseStart_347840 := by decide
  rcases family_descends (prefixWord ++ tailWord_347840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347846 : List Nat := [6, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_347846 : Nat := 118140960795 + 347846 * 2 ^ 59
def prefixEnd_347846 : Nat := 4983230072969 + 3 ^ 40 * 347846 * 2
def baseEnd_347846 : Nat := 158766392661290030778037

theorem tailTrace_347846 : CollatzResearch.WordTrace tailWord_347846 prefixEnd_347846 158766392661290030778037 := by
  unfold tailWord_347846
  simp only [CollatzResearch.WordTrace]
  refine ⟨396468309306900756632731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8457990598547216141498261 396468309306900756632731)
  ·
    refine ⟨594702463960351134949097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 396468309306900756632731 594702463960351134949097)
    ·
      refine ⟨446026847970263351211823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 594702463960351134949097 446026847970263351211823)
      ·
        refine ⟨669040271955395026817735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446026847970263351211823 669040271955395026817735)
        ·
          refine ⟨1003560407933092540226603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669040271955395026817735 1003560407933092540226603)
          ·
            refine ⟨1505340611899638810339905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003560407933092540226603 1505340611899638810339905)
            ·
              refine ⟨1129005458924729107754929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505340611899638810339905 1129005458924729107754929)
              ·
                refine ⟨846754094193546830816197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129005458924729107754929 846754094193546830816197)
                ·
                  refine ⟨158766392661290030778037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 846754094193546830816197 158766392661290030778037)
                  ·
                    rfl

theorem cell20_347846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_347846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347846 prefixEnd_347846 := by exact prefixLift 347846
  have htrace : WordTrace (prefixWord ++ tailWord_347846) baseStart_347846 baseEnd_347846 := by
    simpa [prefixWord, tailWord_347846, baseEnd_347846] using wordTrace_append hprefix tailTrace_347846
  have hstable : (prefixWord ++ tailWord_347846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347846).length < 2 ^ (prefixWord ++ tailWord_347846).sum := by decide
  have hdescent : baseEnd_347846 < baseStart_347846 := by decide
  rcases family_descends (prefixWord ++ tailWord_347846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347853 : List Nat := [1, 6, 2, 1, 1, 1, 4, 4]
def baseStart_347853 : Nat := 118140960795 + 347853 * 2 ^ 59
def prefixEnd_347853 : Nat := 4983230072969 + 3 ^ 40 * 347853 * 2
def baseEnd_347853 : Nat := 52923195884009705848225

theorem tailTrace_347853 : CollatzResearch.WordTrace tailWord_347853 prefixEnd_347853 52923195884009705848225 := by
  unfold tailWord_347853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687241208795464407752213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8458160805863642938501475 12687241208795464407752213)
  ·
    refine ⟨594714431662287394113385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12687241208795464407752213 594714431662287394113385)
    ·
      refine ⟨446035823746715545585039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 594714431662287394113385 446035823746715545585039)
      ·
        refine ⟨669053735620073318377559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446035823746715545585039 669053735620073318377559)
        ·
          refine ⟨1003580603430109977566339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669053735620073318377559 1003580603430109977566339)
          ·
            refine ⟨1505370905145164966349509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003580603430109977566339 1505370905145164966349509)
            ·
              refine ⟨282257044714718431190533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1505370905145164966349509 282257044714718431190533)
              ·
                refine ⟨52923195884009705848225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282257044714718431190533 52923195884009705848225)
                ·
                  rfl

theorem cell20_347853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 4].length) (baseStart_347853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347853 prefixEnd_347853 := by exact prefixLift 347853
  have htrace : WordTrace (prefixWord ++ tailWord_347853) baseStart_347853 baseEnd_347853 := by
    simpa [prefixWord, tailWord_347853, baseEnd_347853] using wordTrace_append hprefix tailTrace_347853
  have hstable : (prefixWord ++ tailWord_347853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347853).length < 2 ^ (prefixWord ++ tailWord_347853).sum := by decide
  have hdescent : baseEnd_347853 < baseStart_347853 := by decide
  rcases family_descends (prefixWord ++ tailWord_347853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347857 : List Nat := [1, 2, 2, 1, 2, 4, 4, 4]
def baseStart_347857 : Nat := 118140960795 + 347857 * 2 ^ 59
def prefixEnd_347857 : Nat := 4983230072969 + 3 ^ 40 * 347857 * 2
def baseEnd_347857 : Nat := 52923804453674293803775

theorem tailTrace_347857 : CollatzResearch.WordTrace tailWord_347857 prefixEnd_347857 52923804453674293803775 := by
  unfold tailWord_347857
  simp only [CollatzResearch.WordTrace]
  refine ⟨12687387100780973090897825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8458258067187315393931883 12687387100780973090897825)
  ·
    refine ⟨9515540325585729818173369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12687387100780973090897825 9515540325585729818173369)
    ·
      refine ⟨7136655244189297363630027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9515540325585729818173369 7136655244189297363630027)
      ·
        refine ⟨10704982866283946045445041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136655244189297363630027 10704982866283946045445041)
        ·
          refine ⟨8028737149712959534083781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10704982866283946045445041 8028737149712959534083781)
          ·
            refine ⟨1505388215571179912640709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8028737149712959534083781 1505388215571179912640709)
            ·
              refine ⟨282260290419596233620133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1505388215571179912640709 282260290419596233620133)
              ·
                refine ⟨52923804453674293803775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282260290419596233620133 52923804453674293803775)
                ·
                  rfl

theorem cell20_347857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 4, 4].length) (baseStart_347857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347857 prefixEnd_347857 := by exact prefixLift 347857
  have htrace : WordTrace (prefixWord ++ tailWord_347857) baseStart_347857 baseEnd_347857 := by
    simpa [prefixWord, tailWord_347857, baseEnd_347857] using wordTrace_append hprefix tailTrace_347857
  have hstable : (prefixWord ++ tailWord_347857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347857).length < 2 ^ (prefixWord ++ tailWord_347857).sum := by decide
  have hdescent : baseEnd_347857 < baseStart_347857 := by decide
  rcases family_descends (prefixWord ++ tailWord_347857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347916 : List Nat := [2, 2, 1, 2, 2, 1, 4, 6]
def baseStart_347916 : Nat := 118140960795 + 347916 * 2 ^ 59
def prefixEnd_347916 : Nat := 4983230072969 + 3 ^ 40 * 347916 * 2
def baseEnd_347916 : Nat := 52932780856226966148139

theorem tailTrace_347916 : CollatzResearch.WordTrace tailWord_347916 prefixEnd_347916 52932780856226966148139 := by
  unfold tailWord_347916
  simp only [CollatzResearch.WordTrace]
  refine ⟨6344769503783613083647801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8459692671711484111530401 6344769503783613083647801)
  ·
    refine ⟨4758577127837709812735851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6344769503783613083647801 4758577127837709812735851)
    ·
      refine ⟨7137865691756564719103777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4758577127837709812735851 7137865691756564719103777)
      ·
        refine ⟨5353399268817423539327833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7137865691756564719103777 5353399268817423539327833)
        ·
          refine ⟨4015049451613067654495875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5353399268817423539327833 4015049451613067654495875)
          ·
            refine ⟨6022574177419601481743813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4015049451613067654495875 6022574177419601481743813)
            ·
              refine ⟨1129232658266175277826965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6022574177419601481743813 1129232658266175277826965)
              ·
                refine ⟨52932780856226966148139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1129232658266175277826965 52932780856226966148139)
                ·
                  rfl

theorem cell20_347916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_347916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347916 prefixEnd_347916 := by exact prefixLift 347916
  have htrace : WordTrace (prefixWord ++ tailWord_347916) baseStart_347916 baseEnd_347916 := by
    simpa [prefixWord, tailWord_347916, baseEnd_347916] using wordTrace_append hprefix tailTrace_347916
  have hstable : (prefixWord ++ tailWord_347916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347916).length < 2 ^ (prefixWord ++ tailWord_347916).sum := by decide
  have hdescent : baseEnd_347916 < baseStart_347916 := by decide
  rcases family_descends (prefixWord ++ tailWord_347916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347923 : List Nat := [1, 1, 1, 2, 1, 3, 2, 4, 5]
def baseStart_347923 : Nat := 118140960795 + 347923 * 2 ^ 59
def prefixEnd_347923 : Nat := 4983230072969 + 3 ^ 40 * 347923 * 2
def baseEnd_347923 : Nat := 158801537559419985211055

theorem tailTrace_347923 : CollatzResearch.WordTrace tailWord_347923 prefixEnd_347923 158801537559419985211055 := by
  unfold tailWord_347923
  simp only [CollatzResearch.WordTrace]
  refine ⟨12689794318541866362800423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8459862879027910908533615 12689794318541866362800423)
  ·
    refine ⟨19034691477812799544200635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12689794318541866362800423 19034691477812799544200635)
    ·
      refine ⟨28552037216719199316300953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19034691477812799544200635 28552037216719199316300953)
      ·
        refine ⟨21414027912539399487225715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28552037216719199316300953 21414027912539399487225715)
        ·
          refine ⟨32121041868809099230838573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21414027912539399487225715 32121041868809099230838573)
          ·
            refine ⟨12045390700803412211564465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32121041868809099230838573 12045390700803412211564465)
            ·
              refine ⟨9034043025602559158673349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12045390700803412211564465 9034043025602559158673349)
              ·
                refine ⟨1693883067300479842251253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9034043025602559158673349 1693883067300479842251253)
                ·
                  refine ⟨158801537559419985211055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1693883067300479842251253 158801537559419985211055)
                  ·
                    rfl

theorem cell20_347923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_347923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347923 prefixEnd_347923 := by exact prefixLift 347923
  have htrace : WordTrace (prefixWord ++ tailWord_347923) baseStart_347923 baseEnd_347923 := by
    simpa [prefixWord, tailWord_347923, baseEnd_347923] using wordTrace_append hprefix tailTrace_347923
  have hstable : (prefixWord ++ tailWord_347923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347923).length < 2 ^ (prefixWord ++ tailWord_347923).sum := by decide
  have hdescent : baseEnd_347923 < baseStart_347923 := by decide
  rcases family_descends (prefixWord ++ tailWord_347923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347971 : List Nat := [1, 1, 1, 3, 1, 6, 3, 4]
def baseStart_347971 : Nat := 118140960795 + 347971 * 2 ^ 59
def prefixEnd_347971 : Nat := 4983230072969 + 3 ^ 40 * 347971 * 2
def baseEnd_347971 : Nat := 52941148689115050536953

theorem tailTrace_347971 : CollatzResearch.WordTrace tailWord_347971 prefixEnd_347971 52941148689115050536953 := by
  unfold tailWord_347971
  simp only [CollatzResearch.WordTrace]
  refine ⟨12691545022367970560547767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8461030014911980373698511 12691545022367970560547767)
  ·
    refine ⟨19037317533551955840821651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12691545022367970560547767 19037317533551955840821651)
    ·
      refine ⟨28555976300327933761232477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19037317533551955840821651 28555976300327933761232477)
      ·
        refine ⟨10708491112622975160462179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28555976300327933761232477 10708491112622975160462179)
        ·
          refine ⟨16062736668934462740693269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10708491112622975160462179 16062736668934462740693269)
          ·
            refine ⟨752940781356302940969997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16062736668934462740693269 752940781356302940969997)
            ·
              refine ⟨282352793008613602863749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 752940781356302940969997 282352793008613602863749)
              ·
                refine ⟨52941148689115050536953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282352793008613602863749 52941148689115050536953)
                ·
                  rfl

theorem cell20_347971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 4].length) (baseStart_347971 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_347971 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_347971 prefixEnd_347971 := by exact prefixLift 347971
  have htrace : WordTrace (prefixWord ++ tailWord_347971) baseStart_347971 baseEnd_347971 := by
    simpa [prefixWord, tailWord_347971, baseEnd_347971] using wordTrace_append hprefix tailTrace_347971
  have hstable : (prefixWord ++ tailWord_347971).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347971).length < 2 ^ (prefixWord ++ tailWord_347971).sum := by decide
  have hdescent : baseEnd_347971 < baseStart_347971 := by decide
  rcases family_descends (prefixWord ++ tailWord_347971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348002 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_348002 : Nat := 118140960795 + 348002 * 2 ^ 59
def prefixEnd_348002 : Nat := 4983230072969 + 3 ^ 40 * 348002 * 2
def baseEnd_348002 : Nat := 158837595312046821577399

theorem tailTrace_348002 : CollatzResearch.WordTrace tailWord_348002 prefixEnd_348002 158837595312046821577399 := by
  unfold tailWord_348002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3173168921313915713731565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8461783790170441903284173 3173168921313915713731565)
  ·
    refine ⟨1189938345492718392649337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3173168921313915713731565 1189938345492718392649337)
    ·
      refine ⟨892453759119538794487003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1189938345492718392649337 892453759119538794487003)
      ·
        refine ⟨1338680638679308191730505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892453759119538794487003 1338680638679308191730505)
        ·
          refine ⟨1004010479009481143797879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338680638679308191730505 1004010479009481143797879)
          ·
            refine ⟨1506015718514221715696819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004010479009481143797879 1506015718514221715696819)
            ·
              refine ⟨2259023577771332573545229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506015718514221715696819 2259023577771332573545229)
              ·
                refine ⟨847133841664249715079461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2259023577771332573545229 847133841664249715079461)
                ·
                  refine ⟨158837595312046821577399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 847133841664249715079461 158837595312046821577399)
                  ·
                    rfl

theorem cell20_348002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_348002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348002 prefixEnd_348002 := by exact prefixLift 348002
  have htrace : WordTrace (prefixWord ++ tailWord_348002) baseStart_348002 baseEnd_348002 := by
    simpa [prefixWord, tailWord_348002, baseEnd_348002] using wordTrace_append hprefix tailTrace_348002
  have hstable : (prefixWord ++ tailWord_348002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348002).length < 2 ^ (prefixWord ++ tailWord_348002).sum := by decide
  have hdescent : baseEnd_348002 < baseStart_348002 := by decide
  rcases family_descends (prefixWord ++ tailWord_348002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348022 : List Nat := [5, 1, 1, 3, 3, 1, 2, 4]
def baseStart_348022 : Nat := 118140960795 + 348022 * 2 ^ 59
def prefixEnd_348022 : Nat := 4983230072969 + 3 ^ 40 * 348022 * 2
def baseEnd_348022 : Nat := 52948907952338546970217

theorem tailTrace_348022 : CollatzResearch.WordTrace tailWord_348022 prefixEnd_348022 52948907952338546970217 := by
  unfold tailWord_348022
  simp only [CollatzResearch.WordTrace]
  refine ⟨793337821573950391915895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8462270096788804180436213 793337821573950391915895)
  ·
    refine ⟨1190006732360925587873843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 793337821573950391915895 1190006732360925587873843)
    ·
      refine ⟨1785010098541388381810765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190006732360925587873843 1785010098541388381810765)
      ·
        refine ⟨669378786953020643179037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1785010098541388381810765 669378786953020643179037)
        ·
          refine ⟨251017045107382741192139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 669378786953020643179037 251017045107382741192139)
          ·
            refine ⟨376525567661074111788209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251017045107382741192139 376525567661074111788209)
            ·
              refine ⟨282394175745805583841157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376525567661074111788209 282394175745805583841157)
              ·
                refine ⟨52948907952338546970217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282394175745805583841157 52948907952338546970217)
                ·
                  rfl

theorem cell20_348022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_348022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348022 prefixEnd_348022 := by exact prefixLift 348022
  have htrace : WordTrace (prefixWord ++ tailWord_348022) baseStart_348022 baseEnd_348022 := by
    simpa [prefixWord, tailWord_348022, baseEnd_348022] using wordTrace_append hprefix tailTrace_348022
  have hstable : (prefixWord ++ tailWord_348022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348022).length < 2 ^ (prefixWord ++ tailWord_348022).sum := by decide
  have hdescent : baseEnd_348022 < baseStart_348022 := by decide
  rcases family_descends (prefixWord ++ tailWord_348022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348037 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 7]
def baseStart_348037 : Nat := 118140960795 + 348037 * 2 ^ 59
def prefixEnd_348037 : Nat := 4983230072969 + 3 ^ 40 * 348037 * 2
def baseEnd_348037 : Nat := 158853570265742255410589

theorem tailTrace_348037 : CollatzResearch.WordTrace tailWord_348037 prefixEnd_348037 158853570265742255410589 := by
  unfold tailWord_348037
  simp only [CollatzResearch.WordTrace]
  refine ⟨12693952240128863832450365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8462634826752575888300243 12693952240128863832450365)
  ·
    refine ⟨4760232090048323937168887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12693952240128863832450365 4760232090048323937168887)
    ·
      refine ⟨7140348135072485905753331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4760232090048323937168887 7140348135072485905753331)
      ·
        refine ⟨10710522202608728858629997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7140348135072485905753331 10710522202608728858629997)
        ·
          refine ⟨4016445825978273321986249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10710522202608728858629997 4016445825978273321986249)
          ·
            refine ⟨3012334369483704991489687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4016445825978273321986249 3012334369483704991489687)
            ·
              refine ⟨4518501554225557487234531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3012334369483704991489687 4518501554225557487234531)
              ·
                refine ⟨6777752331338336230851797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4518501554225557487234531 6777752331338336230851797)
                ·
                  refine ⟨158853570265742255410589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6777752331338336230851797 158853570265742255410589)
                  ·
                    rfl

theorem cell20_348037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_348037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348037 prefixEnd_348037 := by exact prefixLift 348037
  have htrace : WordTrace (prefixWord ++ tailWord_348037) baseStart_348037 baseEnd_348037 := by
    simpa [prefixWord, tailWord_348037, baseEnd_348037] using wordTrace_append hprefix tailTrace_348037
  have hstable : (prefixWord ++ tailWord_348037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348037).length < 2 ^ (prefixWord ++ tailWord_348037).sum := by decide
  have hdescent : baseEnd_348037 < baseStart_348037 := by decide
  rcases family_descends (prefixWord ++ tailWord_348037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348068 : List Nat := [2, 3, 1, 2, 1, 3, 1, 7]
def baseStart_348068 : Nat := 118140960795 + 348068 * 2 ^ 59
def prefixEnd_348068 : Nat := 4983230072969 + 3 ^ 40 * 348068 * 2
def baseEnd_348068 : Nat := 52955906503481308459043

theorem tailTrace_348068 : CollatzResearch.WordTrace tailWord_348068 prefixEnd_348068 52955906503481308459043 := by
  unfold tailWord_348068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6347541451508278063414429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8463388602011037417885905 6347541451508278063414429)
  ·
    refine ⟨2380328044315604273780411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6347541451508278063414429 2380328044315604273780411)
    ·
      refine ⟨3570492066473406410670617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2380328044315604273780411 3570492066473406410670617)
      ·
        refine ⟨2677869049855054808002963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3570492066473406410670617 2677869049855054808002963)
        ·
          refine ⟨4016803574782582212004445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2677869049855054808002963 4016803574782582212004445)
          ·
            refine ⟨1506301340543468329501667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4016803574782582212004445 1506301340543468329501667)
            ·
              refine ⟨2259452010815202494252501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506301340543468329501667 2259452010815202494252501)
              ·
                refine ⟨52955906503481308459043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2259452010815202494252501 52955906503481308459043)
                ·
                  rfl

theorem cell20_348068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_348068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348068 prefixEnd_348068 := by exact prefixLift 348068
  have htrace : WordTrace (prefixWord ++ tailWord_348068) baseStart_348068 baseEnd_348068 := by
    simpa [prefixWord, tailWord_348068, baseEnd_348068] using wordTrace_append hprefix tailTrace_348068
  have hstable : (prefixWord ++ tailWord_348068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348068).length < 2 ^ (prefixWord ++ tailWord_348068).sum := by decide
  have hdescent : baseEnd_348068 < baseStart_348068 := by decide
  rcases family_descends (prefixWord ++ tailWord_348068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348071 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 3]
def baseStart_348071 : Nat := 118140960795 + 348071 * 2 ^ 59
def prefixEnd_348071 : Nat := 4983230072969 + 3 ^ 40 * 348071 * 2
def baseEnd_348071 : Nat := 158869088792189248277117

theorem tailTrace_348071 : CollatzResearch.WordTrace tailWord_348071 prefixEnd_348071 158869088792189248277117 := by
  unfold tailWord_348071
  simp only [CollatzResearch.WordTrace]
  refine ⟨12695192322005687639188067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8463461548003791759458711 12695192322005687639188067)
  ·
    refine ⟨19042788483008531458782101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12695192322005687639188067 19042788483008531458782101)
    ·
      refine ⟨892630710141024912130411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19042788483008531458782101 892630710141024912130411)
      ·
        refine ⟨1338946065211537368195617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892630710141024912130411 1338946065211537368195617)
        ·
          refine ⟨1004209548908653026146713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1338946065211537368195617 1004209548908653026146713)
          ·
            refine ⟨753157161681489769610035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1004209548908653026146713 753157161681489769610035)
            ·
              refine ⟨1129735742522234654415053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753157161681489769610035 1129735742522234654415053)
              ·
                refine ⟨423650903445837995405645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1129735742522234654415053 423650903445837995405645)
                ·
                  refine ⟨158869088792189248277117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 423650903445837995405645 158869088792189248277117)
                  ·
                    rfl

theorem cell20_348071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 3].length) (baseStart_348071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348071 prefixEnd_348071 := by exact prefixLift 348071
  have htrace : WordTrace (prefixWord ++ tailWord_348071) baseStart_348071 baseEnd_348071 := by
    simpa [prefixWord, tailWord_348071, baseEnd_348071] using wordTrace_append hprefix tailTrace_348071
  have hstable : (prefixWord ++ tailWord_348071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348071).length < 2 ^ (prefixWord ++ tailWord_348071).sum := by decide
  have hdescent : baseEnd_348071 < baseStart_348071 := by decide
  rcases family_descends (prefixWord ++ tailWord_348071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348102 : List Nat := [6, 1, 3, 10]
def baseStart_348102 : Nat := 118140960795 + 348102 * 2 ^ 59
def prefixEnd_348102 : Nat := 4983230072969 + 3 ^ 40 * 348102 * 2
def baseEnd_348102 : Nat := 653840485748522297299

theorem tailTrace_348102 : CollatzResearch.WordTrace tailWord_348102 prefixEnd_348102 653840485748522297299 := by
  unfold tailWord_348102
  simp only [CollatzResearch.WordTrace]
  refine ⟨396760093277918122923955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8464215323262253289044373 396760093277918122923955)
  ·
    refine ⟨595140139916877184385933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 396760093277918122923955 595140139916877184385933)
    ·
      refine ⟨223177552468828944144725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 595140139916877184385933 223177552468828944144725)
      ·
        refine ⟨653840485748522297299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 223177552468828944144725 653840485748522297299)
        ·
          rfl

theorem cell20_348102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 10].length) (baseStart_348102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348102 prefixEnd_348102 := by exact prefixLift 348102
  have htrace : WordTrace (prefixWord ++ tailWord_348102) baseStart_348102 baseEnd_348102 := by
    simpa [prefixWord, tailWord_348102, baseEnd_348102] using wordTrace_append hprefix tailTrace_348102
  have hstable : (prefixWord ++ tailWord_348102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348102).length < 2 ^ (prefixWord ++ tailWord_348102).sum := by decide
  have hdescent : baseEnd_348102 < baseStart_348102 := by decide
  rcases family_descends (prefixWord ++ tailWord_348102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348150 : List Nat := [5, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_348150 : Nat := 118140960795 + 348150 * 2 ^ 59
def prefixEnd_348150 : Nat := 4983230072969 + 3 ^ 40 * 348150 * 2
def baseEnd_348150 : Nat := 158905146544816084643461

theorem tailTrace_348150 : CollatzResearch.WordTrace tailWord_348150 prefixEnd_348150 158905146544816084643461 := by
  unfold tailWord_348150
  simp only [CollatzResearch.WordTrace]
  refine ⟨793629605544967758207119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8465382459146322754209269 793629605544967758207119)
  ·
    refine ⟨1190444408317451637310679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 793629605544967758207119 1190444408317451637310679)
    ·
      refine ⟨1785666612476177455966019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190444408317451637310679 1785666612476177455966019)
      ·
        refine ⟨2678499918714266183949029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785666612476177455966019 2678499918714266183949029)
        ·
          refine ⟨502218734758924909490443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2678499918714266183949029 502218734758924909490443)
          ·
            refine ⟨753328102138387364235665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502218734758924909490443 753328102138387364235665)
            ·
              refine ⟨564996076603790523176749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753328102138387364235665 564996076603790523176749)
              ·
                refine ⟨211873528726421446191281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 564996076603790523176749 211873528726421446191281)
                ·
                  refine ⟨158905146544816084643461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211873528726421446191281 158905146544816084643461)
                  ·
                    rfl

theorem cell20_348150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_348150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348150 prefixEnd_348150 := by exact prefixLift 348150
  have htrace : WordTrace (prefixWord ++ tailWord_348150) baseStart_348150 baseEnd_348150 := by
    simpa [prefixWord, tailWord_348150, baseEnd_348150] using wordTrace_append hprefix tailTrace_348150
  have hstable : (prefixWord ++ tailWord_348150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348150).length < 2 ^ (prefixWord ++ tailWord_348150).sum := by decide
  have hdescent : baseEnd_348150 < baseStart_348150 := by decide
  rcases family_descends (prefixWord ++ tailWord_348150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348206 : List Nat := [4, 1, 3, 1, 1, 2, 1, 2, 5]
def baseStart_348206 : Nat := 118140960795 + 348206 * 2 ^ 59
def prefixEnd_348206 : Nat := 4983230072969 + 3 ^ 40 * 348206 * 2
def baseEnd_348206 : Nat := 158930706470728778776565

theorem tailTrace_348206 : CollatzResearch.WordTrace tailWord_348206 prefixEnd_348206 158930706470728778776565 := by
  unfold tailWord_348206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587514522064575711919059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8466744117677737130234981 1587514522064575711919059)
  ·
    refine ⟨2381271783096863567878589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587514522064575711919059 2381271783096863567878589)
    ·
      refine ⟨892976918661323837954471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2381271783096863567878589 892976918661323837954471)
      ·
        refine ⟨1339465377991985756931707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 892976918661323837954471 1339465377991985756931707)
        ·
          refine ⟨2009198066987978635397561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339465377991985756931707 2009198066987978635397561)
          ·
            refine ⟨1506898550240983976548171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009198066987978635397561 1506898550240983976548171)
            ·
              refine ⟨2260347825361475964822257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506898550240983976548171 2260347825361475964822257)
              ·
                refine ⟨1695260869021106973616693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260347825361475964822257 1695260869021106973616693)
                ·
                  refine ⟨158930706470728778776565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1695260869021106973616693 158930706470728778776565)
                  ·
                    rfl

theorem cell20_348206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_348206 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348206 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348206 prefixEnd_348206 := by exact prefixLift 348206
  have htrace : WordTrace (prefixWord ++ tailWord_348206) baseStart_348206 baseEnd_348206 := by
    simpa [prefixWord, tailWord_348206, baseEnd_348206] using wordTrace_append hprefix tailTrace_348206
  have hstable : (prefixWord ++ tailWord_348206).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348206).length < 2 ^ (prefixWord ++ tailWord_348206).sum := by decide
  have hdescent : baseEnd_348206 < baseStart_348206 := by decide
  rcases family_descends (prefixWord ++ tailWord_348206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348209 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 2]
def baseStart_348209 : Nat := 118140960795 + 348209 * 2 ^ 59
def prefixEnd_348209 : Nat := 4983230072969 + 3 ^ 40 * 348209 * 2
def baseEnd_348209 : Nat := 158932075752474101676553

theorem tailTrace_348209 : CollatzResearch.WordTrace tailWord_348209 prefixEnd_348209 158932075752474101676553 := by
  unfold tailWord_348209
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700225595505737207711681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8466817063670491471807787 12700225595505737207711681)
  ·
    refine ⟨9525169196629302905783761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12700225595505737207711681 9525169196629302905783761)
    ·
      refine ⟨7143876897471977179337821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9525169196629302905783761 7143876897471977179337821)
      ·
        refine ⟨2678953836551991442251683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7143876897471977179337821 2678953836551991442251683)
        ·
          refine ⟨4018430754827987163377525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678953836551991442251683 4018430754827987163377525)
          ·
            refine ⟨376727883265123796566643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4018430754827987163377525 376727883265123796566643)
            ·
              refine ⟨565091824897685694849965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376727883265123796566643 565091824897685694849965)
              ·
                refine ⟨211909434336632135568737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565091824897685694849965 211909434336632135568737)
                ·
                  refine ⟨158932075752474101676553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211909434336632135568737 158932075752474101676553)
                  ·
                    rfl

theorem cell20_348209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 2].length) (baseStart_348209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348209 prefixEnd_348209 := by exact prefixLift 348209
  have htrace : WordTrace (prefixWord ++ tailWord_348209) baseStart_348209 baseEnd_348209 := by
    simpa [prefixWord, tailWord_348209, baseEnd_348209] using wordTrace_append hprefix tailTrace_348209
  have hstable : (prefixWord ++ tailWord_348209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348209).length < 2 ^ (prefixWord ++ tailWord_348209).sum := by decide
  have hdescent : baseEnd_348209 < baseStart_348209 := by decide
  rcases family_descends (prefixWord ++ tailWord_348209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348237 : List Nat := [1, 6, 1, 1, 1, 1, 4, 5]
def baseStart_348237 : Nat := 118140960795 + 348237 * 2 ^ 59
def prefixEnd_348237 : Nat := 4983230072969 + 3 ^ 40 * 348237 * 2
def baseEnd_348237 : Nat := 52981618571810149581035

theorem tailTrace_348237 : CollatzResearch.WordTrace tailWord_348237 prefixEnd_348237 52981618571810149581035 := by
  unfold tailWord_348237
  simp only [CollatzResearch.WordTrace]
  refine ⟨12701246839404297989730965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8467497892936198659820643 12701246839404297989730965)
  ·
    refine ⟨595370945597076468268639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12701246839404297989730965 595370945597076468268639)
    ·
      refine ⟨893056418395614702402959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595370945597076468268639 893056418395614702402959)
      ·
        refine ⟨1339584627593422053604439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893056418395614702402959 1339584627593422053604439)
        ·
          refine ⟨2009376941390133080406659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1339584627593422053604439 2009376941390133080406659)
          ·
            refine ⟨3014065412085199620609989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2009376941390133080406659 3014065412085199620609989)
            ·
              refine ⟨565137264765974928864373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3014065412085199620609989 565137264765974928864373)
              ·
                refine ⟨52981618571810149581035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565137264765974928864373 52981618571810149581035)
                ·
                  rfl

theorem cell20_348237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 5].length) (baseStart_348237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348237 prefixEnd_348237 := by exact prefixLift 348237
  have htrace : WordTrace (prefixWord ++ tailWord_348237) baseStart_348237 baseEnd_348237 := by
    simpa [prefixWord, tailWord_348237, baseEnd_348237] using wordTrace_append hprefix tailTrace_348237
  have hstable : (prefixWord ++ tailWord_348237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348237).length < 2 ^ (prefixWord ++ tailWord_348237).sum := by decide
  have hdescent : baseEnd_348237 < baseStart_348237 := by decide
  rcases family_descends (prefixWord ++ tailWord_348237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348279 : List Nat := [1, 1, 3, 1, 1, 13]
def baseStart_348279 : Nat := 118140960795 + 348279 * 2 ^ 59
def prefixEnd_348279 : Nat := 4983230072969 + 3 ^ 40 * 348279 * 2
def baseEnd_348279 : Nat := 5887556505920924790479

theorem tailTrace_348279 : CollatzResearch.WordTrace tailWord_348279 prefixEnd_348279 5887556505920924790479 := by
  unfold tailWord_348279
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702778705252139162759891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8468519136834759441839927 12702778705252139162759891)
  ·
    refine ⟨19054168057878208744139837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12702778705252139162759891 19054168057878208744139837)
    ·
      refine ⟨7145313021704328279052439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19054168057878208744139837 7145313021704328279052439)
      ·
        refine ⟨10717969532556492418578659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7145313021704328279052439 10717969532556492418578659)
        ·
          refine ⟨16076954298834738627867989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10717969532556492418578659 16076954298834738627867989)
          ·
            refine ⟨5887556505920924790479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 16076954298834738627867989 5887556505920924790479)
            ·
              rfl

theorem cell20_348279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 13].length) (baseStart_348279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348279 prefixEnd_348279 := by exact prefixLift 348279
  have htrace : WordTrace (prefixWord ++ tailWord_348279) baseStart_348279 baseEnd_348279 := by
    simpa [prefixWord, tailWord_348279, baseEnd_348279] using wordTrace_append hprefix tailTrace_348279
  have hstable : (prefixWord ++ tailWord_348279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348279).length < 2 ^ (prefixWord ++ tailWord_348279).sum := by decide
  have hdescent : baseEnd_348279 < baseStart_348279 := by decide
  rcases family_descends (prefixWord ++ tailWord_348279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348285 : List Nat := [1, 4, 1, 1, 3, 2, 4, 2, 2]
def baseStart_348285 : Nat := 118140960795 + 348285 * 2 ^ 59
def prefixEnd_348285 : Nat := 4983230072969 + 3 ^ 40 * 348285 * 2
def baseEnd_348285 : Nat := 158966764223355615142909

theorem tailTrace_348285 : CollatzResearch.WordTrace tailWord_348285 prefixEnd_348285 158966764223355615142909 := by
  unfold tailWord_348285
  simp only [CollatzResearch.WordTrace]
  refine ⟨12702997543230402187478309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8468665028820268124985539 12702997543230402187478309)
  ·
    refine ⟨2381812039355700410152183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12702997543230402187478309 2381812039355700410152183)
    ·
      refine ⟨3572718059033550615228275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2381812039355700410152183 3572718059033550615228275)
      ·
        refine ⟨5359077088550325922842413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3572718059033550615228275 5359077088550325922842413)
        ·
          refine ⟨2009653908206372221065905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5359077088550325922842413 2009653908206372221065905)
          ·
            refine ⟨1507240431154779165799429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2009653908206372221065905 1507240431154779165799429)
            ·
              refine ⟨282607580841521093587393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1507240431154779165799429 282607580841521093587393)
              ·
                refine ⟨211955685631140820190545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282607580841521093587393 211955685631140820190545)
                ·
                  refine ⟨158966764223355615142909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211955685631140820190545 158966764223355615142909)
                  ·
                    rfl

theorem cell20_348285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 4, 2, 2].length) (baseStart_348285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348285 prefixEnd_348285 := by exact prefixLift 348285
  have htrace : WordTrace (prefixWord ++ tailWord_348285) baseStart_348285 baseEnd_348285 := by
    simpa [prefixWord, tailWord_348285, baseEnd_348285] using wordTrace_append hprefix tailTrace_348285
  have hstable : (prefixWord ++ tailWord_348285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348285).length < 2 ^ (prefixWord ++ tailWord_348285).sum := by decide
  have hdescent : baseEnd_348285 < baseStart_348285 := by decide
  rcases family_descends (prefixWord ++ tailWord_348285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348399 : List Nat := [1, 1, 2, 1, 6, 2, 3, 2, 2]
def baseStart_348399 : Nat := 118140960795 + 348399 * 2 ^ 59
def prefixEnd_348399 : Nat := 4983230072969 + 3 ^ 40 * 348399 * 2
def baseEnd_348399 : Nat := 159018796929677885342443

theorem tailTrace_348399 : CollatzResearch.WordTrace tailWord_348399 prefixEnd_348399 159018796929677885342443 := by
  unfold tailWord_348399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707155464817399657128251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8471436976544933104752167 12707155464817399657128251)
  ·
    refine ⟨19060733197226099485692377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12707155464817399657128251 19060733197226099485692377)
    ·
      refine ⟨14295549897919574614269283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19060733197226099485692377 14295549897919574614269283)
      ·
        refine ⟨21443324846879361921403925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14295549897919574614269283 21443324846879361921403925)
        ·
          refine ⟨1005155852197470090065809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21443324846879361921403925 1005155852197470090065809)
          ·
            refine ⟨753866889148102567549357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005155852197470090065809 753866889148102567549357)
            ·
              refine ⟨282700083430538462831009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753866889148102567549357 282700083430538462831009)
              ·
                refine ⟨212025062572903847123257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282700083430538462831009 212025062572903847123257)
                ·
                  refine ⟨159018796929677885342443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212025062572903847123257 159018796929677885342443)
                  ·
                    rfl

theorem cell20_348399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 2, 2].length) (baseStart_348399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348399 prefixEnd_348399 := by exact prefixLift 348399
  have htrace : WordTrace (prefixWord ++ tailWord_348399) baseStart_348399 baseEnd_348399 := by
    simpa [prefixWord, tailWord_348399, baseEnd_348399] using wordTrace_append hprefix tailTrace_348399
  have hstable : (prefixWord ++ tailWord_348399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348399).length < 2 ^ (prefixWord ++ tailWord_348399).sum := by decide
  have hdescent : baseEnd_348399 < baseStart_348399 := by decide
  rcases family_descends (prefixWord ++ tailWord_348399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348410 : List Nat := [3, 1, 1, 1, 1, 6, 2, 5]
def baseStart_348410 : Nat := 118140960795 + 348410 * 2 ^ 59
def prefixEnd_348410 : Nat := 4983230072969 + 3 ^ 40 * 348410 * 2
def baseEnd_348410 : Nat := 53007939209803578658577

theorem tailTrace_348410 : CollatzResearch.WordTrace tailWord_348410 prefixEnd_348410 53007939209803578658577 := by
  unfold tailWord_348410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3176889166944387133944671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8471704445185032357185789 3176889166944387133944671)
  ·
    refine ⟨4765333750416580700917007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3176889166944387133944671 4765333750416580700917007)
    ·
      refine ⟨7148000625624871051375511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4765333750416580700917007 7148000625624871051375511)
      ·
        refine ⟨10722000938437306577063267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7148000625624871051375511 10722000938437306577063267)
        ·
          refine ⟨16083001407655959865594901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10722000938437306577063267 16083001407655959865594901)
          ·
            refine ⟨753890690983873118699761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16083001407655959865594901 753890690983873118699761)
            ·
              refine ⟨565418018237904839024821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753890690983873118699761 565418018237904839024821)
              ·
                refine ⟨53007939209803578658577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565418018237904839024821 53007939209803578658577)
                ·
                  rfl

theorem cell20_348410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_348410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348410 prefixEnd_348410 := by exact prefixLift 348410
  have htrace : WordTrace (prefixWord ++ tailWord_348410) baseStart_348410 baseEnd_348410 := by
    simpa [prefixWord, tailWord_348410, baseEnd_348410] using wordTrace_append hprefix tailTrace_348410
  have hstable : (prefixWord ++ tailWord_348410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348410).length < 2 ^ (prefixWord ++ tailWord_348410).sum := by decide
  have hdescent : baseEnd_348410 < baseStart_348410 := by decide
  rcases family_descends (prefixWord ++ tailWord_348410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348461 : List Nat := [1, 5, 3, 1, 3, 1, 1, 5]
def baseStart_348461 : Nat := 118140960795 + 348461 * 2 ^ 59
def prefixEnd_348461 : Nat := 4983230072969 + 3 ^ 40 * 348461 * 2
def baseEnd_348461 : Nat := 53015698473027075091841

theorem tailTrace_348461 : CollatzResearch.WordTrace tailWord_348461 prefixEnd_348461 53015698473027075091841 := by
  unfold tailWord_348461
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709416790592784245885237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8472944527061856163923491 12709416790592784245885237)
  ·
    refine ⟨1191507824118073523051741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12709416790592784245885237 1191507824118073523051741)
    ·
      refine ⟨446815434044277571144403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1191507824118073523051741 446815434044277571144403)
      ·
        refine ⟨670223151066416356716605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446815434044277571144403 670223151066416356716605)
        ·
          refine ⟨251333681649906133768727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 670223151066416356716605 251333681649906133768727)
          ·
            refine ⟨377000522474859200653091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251333681649906133768727 377000522474859200653091)
            ·
              refine ⟨565500783712288800979637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377000522474859200653091 565500783712288800979637)
              ·
                refine ⟨53015698473027075091841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565500783712288800979637 53015698473027075091841)
                ·
                  rfl

theorem cell20_348461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 5].length) (baseStart_348461 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348461 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348461 prefixEnd_348461 := by exact prefixLift 348461
  have htrace : WordTrace (prefixWord ++ tailWord_348461) baseStart_348461 baseEnd_348461 := by
    simpa [prefixWord, tailWord_348461, baseEnd_348461] using wordTrace_append hprefix tailTrace_348461
  have hstable : (prefixWord ++ tailWord_348461).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348461).length < 2 ^ (prefixWord ++ tailWord_348461).sum := by decide
  have hdescent : baseEnd_348461 < baseStart_348461 := by decide
  rcases family_descends (prefixWord ++ tailWord_348461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348465 : List Nat := [1, 2, 2, 3, 4, 2, 1, 5]
def baseStart_348465 : Nat := 118140960795 + 348465 * 2 ^ 59
def prefixEnd_348465 : Nat := 4983230072969 + 3 ^ 40 * 348465 * 2
def baseEnd_348465 : Nat := 53016307042691663047391

theorem tailTrace_348465 : CollatzResearch.WordTrace tailWord_348465 prefixEnd_348465 53016307042691663047391 := by
  unfold tailWord_348465
  simp only [CollatzResearch.WordTrace]
  refine ⟨12709562682578292929030849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8473041788385528619353899 12709562682578292929030849)
  ·
    refine ⟨9532172011933719696773137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12709562682578292929030849 9532172011933719696773137)
    ·
      refine ⟨7149129008950289772579853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9532172011933719696773137 7149129008950289772579853)
      ·
        refine ⟨2680923378356358664717445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7149129008950289772579853 2680923378356358664717445)
        ·
          refine ⟨502673133441817249634521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2680923378356358664717445 502673133441817249634521)
          ·
            refine ⟨377004850081362937225891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502673133441817249634521 377004850081362937225891)
            ·
              refine ⟨565507275122044405838837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377004850081362937225891 565507275122044405838837)
              ·
                refine ⟨53016307042691663047391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 565507275122044405838837 53016307042691663047391)
                ·
                  rfl

theorem cell20_348465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 5].length) (baseStart_348465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348465 prefixEnd_348465 := by exact prefixLift 348465
  have htrace : WordTrace (prefixWord ++ tailWord_348465) baseStart_348465 baseEnd_348465 := by
    simpa [prefixWord, tailWord_348465, baseEnd_348465] using wordTrace_append hprefix tailTrace_348465
  have hstable : (prefixWord ++ tailWord_348465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348465).length < 2 ^ (prefixWord ++ tailWord_348465).sum := by decide
  have hdescent : baseEnd_348465 < baseStart_348465 := by decide
  rcases family_descends (prefixWord ++ tailWord_348465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348496 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 2]
def baseStart_348496 : Nat := 118140960795 + 348496 * 2 ^ 59
def prefixEnd_348496 : Nat := 4983230072969 + 3 ^ 40 * 348496 * 2
def baseEnd_348496 : Nat := 159063070372776659108713

theorem tailTrace_348496 : CollatzResearch.WordTrace tailWord_348496 prefixEnd_348496 159063070372776659108713 := by
  unfold tailWord_348496
  simp only [CollatzResearch.WordTrace]
  refine ⟨6355346672732992611704671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8473795563643990148939561 6355346672732992611704671)
  ·
    refine ⟨9533020009099488917557007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6355346672732992611704671 9533020009099488917557007)
    ·
      refine ⟨14299530013649233376335511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9533020009099488917557007 14299530013649233376335511)
      ·
        refine ⟨21449295020473850064503267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14299530013649233376335511 21449295020473850064503267)
        ·
          refine ⟨32173942530710775096754901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21449295020473850064503267 32173942530710775096754901)
          ·
            refine ⟨754076778063533791330193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 32173942530710775096754901 754076778063533791330193)
            ·
              refine ⟨565557583547650343497645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754076778063533791330193 565557583547650343497645)
              ·
                refine ⟨212084093830368878811617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565557583547650343497645 212084093830368878811617)
                ·
                  refine ⟨159063070372776659108713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212084093830368878811617 159063070372776659108713)
                  ·
                    rfl

theorem cell20_348496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_348496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348496 prefixEnd_348496 := by exact prefixLift 348496
  have htrace : WordTrace (prefixWord ++ tailWord_348496) baseStart_348496 baseEnd_348496 := by
    simpa [prefixWord, tailWord_348496, baseEnd_348496] using wordTrace_append hprefix tailTrace_348496
  have hstable : (prefixWord ++ tailWord_348496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348496).length < 2 ^ (prefixWord ++ tailWord_348496).sum := by decide
  have hdescent : baseEnd_348496 < baseStart_348496 := by decide
  rcases family_descends (prefixWord ++ tailWord_348496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348517 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 4]
def baseStart_348517 : Nat := 118140960795 + 348517 * 2 ^ 59
def prefixEnd_348517 : Nat := 4983230072969 + 3 ^ 40 * 348517 * 2
def baseEnd_348517 : Nat := 159072655344993919408627

theorem tailTrace_348517 : CollatzResearch.WordTrace tailWord_348517 prefixEnd_348517 159072655344993919408627 := by
  unfold tailWord_348517
  simp only [CollatzResearch.WordTrace]
  refine ⟨12711459278389905809923805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8474306185593270539949203 12711459278389905809923805)
  ·
    refine ⟨4766797229396214678721427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12711459278389905809923805 4766797229396214678721427)
    ·
      refine ⟨7150195844094322018082141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4766797229396214678721427 7150195844094322018082141)
      ·
        refine ⟨2681323441535370756780803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7150195844094322018082141 2681323441535370756780803)
        ·
          refine ⟨4021985162303056135171205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2681323441535370756780803 4021985162303056135171205)
          ·
            refine ⟨754122217931823025344601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4021985162303056135171205 754122217931823025344601)
            ·
              refine ⟨565591663448867269008451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 754122217931823025344601 565591663448867269008451)
              ·
                refine ⟨848387495173300903512677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565591663448867269008451 848387495173300903512677)
                ·
                  refine ⟨159072655344993919408627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848387495173300903512677 159072655344993919408627)
                  ·
                    rfl

theorem cell20_348517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_348517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348517 prefixEnd_348517 := by exact prefixLift 348517
  have htrace : WordTrace (prefixWord ++ tailWord_348517) baseStart_348517 baseEnd_348517 := by
    simpa [prefixWord, tailWord_348517, baseEnd_348517] using wordTrace_append hprefix tailTrace_348517
  have hstable : (prefixWord ++ tailWord_348517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348517).length < 2 ^ (prefixWord ++ tailWord_348517).sum := by decide
  have hdescent : baseEnd_348517 < baseStart_348517 := by decide
  rcases family_descends (prefixWord ++ tailWord_348517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348541 : List Nat := [1, 4, 1, 1, 2, 5, 2, 4]
def baseStart_348541 : Nat := 118140960795 + 348541 * 2 ^ 59
def prefixEnd_348541 : Nat := 4983230072969 + 3 ^ 40 * 348541 * 2
def baseEnd_348541 : Nat := 53027869866318834202843

theorem tailTrace_348541 : CollatzResearch.WordTrace tailWord_348541 prefixEnd_348541 53027869866318834202843 := by
  unfold tailWord_348541
  simp only [CollatzResearch.WordTrace]
  refine ⟨12712334630302957908797477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8474889753535305272531651 12712334630302957908797477)
  ·
    refine ⟨2383562743181804607899527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12712334630302957908797477 2383562743181804607899527)
    ·
      refine ⟨3575344114772706911849291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2383562743181804607899527 3575344114772706911849291)
      ·
        refine ⟨5363016172159060367773937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3575344114772706911849291 5363016172159060367773937)
        ·
          refine ⟨4022262129119295275830453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5363016172159060367773937 4022262129119295275830453)
          ·
            refine ⟨377087074604933932109105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4022262129119295275830453 377087074604933932109105)
            ·
              refine ⟨282815305953700449081829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377087074604933932109105 282815305953700449081829)
              ·
                refine ⟨53027869866318834202843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282815305953700449081829 53027869866318834202843)
                ·
                  rfl

theorem cell20_348541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 4].length) (baseStart_348541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348541 prefixEnd_348541 := by exact prefixLift 348541
  have htrace : WordTrace (prefixWord ++ tailWord_348541) baseStart_348541 baseEnd_348541 := by
    simpa [prefixWord, tailWord_348541, baseEnd_348541] using wordTrace_append hprefix tailTrace_348541
  have hstable : (prefixWord ++ tailWord_348541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348541).length < 2 ^ (prefixWord ++ tailWord_348541).sum := by decide
  have hdescent : baseEnd_348541 < baseStart_348541 := by decide
  rcases family_descends (prefixWord ++ tailWord_348541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348569 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_348569 : Nat := 118140960795 + 348569 * 2 ^ 59
def prefixEnd_348569 : Nat := 4983230072969 + 3 ^ 40 * 348569 * 2
def baseEnd_348569 : Nat := 159096389561912849675081

theorem tailTrace_348569 : CollatzResearch.WordTrace tailWord_348569 prefixEnd_348569 159096389561912849675081 := by
  unfold tailWord_348569
  simp only [CollatzResearch.WordTrace]
  refine ⟨12713355874201518690816761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8475570582801012460544507 12713355874201518690816761)
  ·
    refine ⟨9535016905651139018112571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12713355874201518690816761 9535016905651139018112571)
    ·
      refine ⟨14302525358476708527168857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9535016905651139018112571 14302525358476708527168857)
      ·
        refine ⟨10726894018857531395376643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14302525358476708527168857 10726894018857531395376643)
        ·
          refine ⟨16090341028286297093064965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10726894018857531395376643 16090341028286297093064965)
          ·
            refine ⟨3016938942803680704949681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16090341028286297093064965 3016938942803680704949681)
            ·
              refine ⟨2262704207102760528712261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3016938942803680704949681 2262704207102760528712261)
              ·
                refine ⟨424257038831767599133549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2262704207102760528712261 424257038831767599133549)
                ·
                  refine ⟨159096389561912849675081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424257038831767599133549 159096389561912849675081)
                  ·
                    rfl

theorem cell20_348569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_348569 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348569 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348569 prefixEnd_348569 := by exact prefixLift 348569
  have htrace : WordTrace (prefixWord ++ tailWord_348569) baseStart_348569 baseEnd_348569 := by
    simpa [prefixWord, tailWord_348569, baseEnd_348569] using wordTrace_append hprefix tailTrace_348569
  have hstable : (prefixWord ++ tailWord_348569).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348569).length < 2 ^ (prefixWord ++ tailWord_348569).sum := by decide
  have hdescent : baseEnd_348569 < baseStart_348569 := by decide
  rcases family_descends (prefixWord ++ tailWord_348569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348621 : List Nat := [1, 6, 13]
def baseStart_348621 : Nat := 118140960795 + 348621 * 2 ^ 59
def prefixEnd_348621 : Nat := 4983230072969 + 3 ^ 40 * 348621 * 2
def baseEnd_348621 : Nat := 218271774730907791415

theorem tailTrace_348621 : CollatzResearch.WordTrace tailWord_348621 prefixEnd_348621 218271774730907791415 := by
  unfold tailWord_348621
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715252470013131571709717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8476834980008754381139811 12715252470013131571709717)
  ·
    refine ⟨596027459531865542423893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12715252470013131571709717 596027459531865542423893)
    ·
      refine ⟨218271774730907791415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 596027459531865542423893 218271774730907791415)
      ·
        rfl

theorem cell20_348621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 13].length) (baseStart_348621 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348621 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348621 prefixEnd_348621 := by exact prefixLift 348621
  have htrace : WordTrace (prefixWord ++ tailWord_348621) baseStart_348621 baseEnd_348621 := by
    simpa [prefixWord, tailWord_348621, baseEnd_348621] using wordTrace_append hprefix tailTrace_348621
  have hstable : (prefixWord ++ tailWord_348621).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348621).length < 2 ^ (prefixWord ++ tailWord_348621).sum := by decide
  have hdescent : baseEnd_348621 < baseStart_348621 := by decide
  rcases family_descends (prefixWord ++ tailWord_348621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348652 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 4]
def baseStart_348652 : Nat := 118140960795 + 348652 * 2 ^ 59
def prefixEnd_348652 : Nat := 4983230072969 + 3 ^ 40 * 348652 * 2
def baseEnd_348652 : Nat := 159134273023533449908075

theorem tailTrace_348652 : CollatzResearch.WordTrace tailWord_348652 prefixEnd_348652 159134273023533449908075 := by
  unfold tailWord_348652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358191566450411933044105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8477588755267215910725473 6358191566450411933044105)
  ·
    refine ⟨4768643674837808949783079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6358191566450411933044105 4768643674837808949783079)
    ·
      refine ⟨7152965512256713424674619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4768643674837808949783079 7152965512256713424674619)
      ·
        refine ⟨10729448268385070137011929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7152965512256713424674619 10729448268385070137011929)
        ·
          refine ⟨8047086201288802602758947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10729448268385070137011929 8047086201288802602758947)
          ·
            refine ⟨12070629301933203904138421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8047086201288802602758947 12070629301933203904138421)
            ·
              refine ⟨1131621497056237866012977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12070629301933203904138421 1131621497056237866012977)
              ·
                refine ⟨848716122792178399509733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131621497056237866012977 848716122792178399509733)
                ·
                  refine ⟨159134273023533449908075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 848716122792178399509733 159134273023533449908075)
                  ·
                    rfl

theorem cell20_348652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_348652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348652 prefixEnd_348652 := by exact prefixLift 348652
  have htrace : WordTrace (prefixWord ++ tailWord_348652) baseStart_348652 baseEnd_348652 := by
    simpa [prefixWord, tailWord_348652, baseEnd_348652] using wordTrace_append hprefix tailTrace_348652
  have hstable : (prefixWord ++ tailWord_348652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348652).length < 2 ^ (prefixWord ++ tailWord_348652).sum := by decide
  have hdescent : baseEnd_348652 < baseStart_348652 := by decide
  rcases family_descends (prefixWord ++ tailWord_348652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348676 : List Nat := [2, 3, 2, 3, 1, 2, 7]
def baseStart_348676 : Nat := 118140960795 + 348676 * 2 ^ 59
def prefixEnd_348676 : Nat := 4983230072969 + 3 ^ 40 * 348676 * 2
def baseEnd_348676 : Nat := 17682803030832892567553

theorem tailTrace_348676 : CollatzResearch.WordTrace tailWord_348676 prefixEnd_348676 17682803030832892567553 := by
  unfold tailWord_348676
  simp only [CollatzResearch.WordTrace]
  refine ⟨6358629242406937982480941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8478172323209250643307921 6358629242406937982480941)
  ·
    refine ⟨2384485965902601743430353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6358629242406937982480941 2384485965902601743430353)
    ·
      refine ⟨1788364474426951307572765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2384485965902601743430353 1788364474426951307572765)
      ·
        refine ⟨670636677910106740339787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1788364474426951307572765 670636677910106740339787)
        ·
          refine ⟨1005955016865160110509681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670636677910106740339787 1005955016865160110509681)
          ·
            refine ⟨754466262648870082882261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005955016865160110509681 754466262648870082882261)
            ·
              refine ⟨17682803030832892567553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 754466262648870082882261 17682803030832892567553)
              ·
                rfl

theorem cell20_348676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 7].length) (baseStart_348676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348676 prefixEnd_348676 := by exact prefixLift 348676
  have htrace : WordTrace (prefixWord ++ tailWord_348676) baseStart_348676 baseEnd_348676 := by
    simpa [prefixWord, tailWord_348676, baseEnd_348676] using wordTrace_append hprefix tailTrace_348676
  have hstable : (prefixWord ++ tailWord_348676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348676).length < 2 ^ (prefixWord ++ tailWord_348676).sum := by decide
  have hdescent : baseEnd_348676 < baseStart_348676 := by decide
  rcases family_descends (prefixWord ++ tailWord_348676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348679 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 3]
def baseStart_348679 : Nat := 118140960795 + 348679 * 2 ^ 59
def prefixEnd_348679 : Nat := 4983230072969 + 3 ^ 40 * 348679 * 2
def baseEnd_348679 : Nat := 159146596559241356007965

theorem tailTrace_348679 : CollatzResearch.WordTrace tailWord_348679 prefixEnd_348679 159146596559241356007965 := by
  unfold tailWord_348679
  simp only [CollatzResearch.WordTrace]
  refine ⟨12717367903803007477321091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8478245269202004984880727 12717367903803007477321091)
  ·
    refine ⟨19076051855704511215981637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12717367903803007477321091 19076051855704511215981637)
    ·
      refine ⟨3576759722944595852996557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19076051855704511215981637 3576759722944595852996557)
      ·
        refine ⟨1341284896104223444873709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3576759722944595852996557 1341284896104223444873709)
        ·
          refine ⟨502981836039083791827641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1341284896104223444873709 502981836039083791827641)
          ·
            refine ⟨377236377029312843870731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502981836039083791827641 377236377029312843870731)
            ·
              refine ⟨565854565543969265806097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377236377029312843870731 565854565543969265806097)
              ·
                refine ⟨424390924157976949354573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 565854565543969265806097 424390924157976949354573)
                ·
                  refine ⟨159146596559241356007965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424390924157976949354573 159146596559241356007965)
                  ·
                    rfl

theorem cell20_348679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 3].length) (baseStart_348679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348679 prefixEnd_348679 := by exact prefixLift 348679
  have htrace : WordTrace (prefixWord ++ tailWord_348679) baseStart_348679 baseEnd_348679 := by
    simpa [prefixWord, tailWord_348679, baseEnd_348679] using wordTrace_append hprefix tailTrace_348679
  have hstable : (prefixWord ++ tailWord_348679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348679).length < 2 ^ (prefixWord ++ tailWord_348679).sum := by decide
  have hdescent : baseEnd_348679 < baseStart_348679 := by decide
  rcases family_descends (prefixWord ++ tailWord_348679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348683 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 5]
def baseStart_348683 : Nat := 118140960795 + 348683 * 2 ^ 59
def prefixEnd_348683 : Nat := 4983230072969 + 3 ^ 40 * 348683 * 2
def baseEnd_348683 : Nat := 159148422268235119874615

theorem tailTrace_348683 : CollatzResearch.WordTrace tailWord_348683 prefixEnd_348683 159148422268235119874615 := by
  unfold tailWord_348683
  simp only [CollatzResearch.WordTrace]
  refine ⟨12717513795788516160466703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8478342530525677440311135 12717513795788516160466703)
  ·
    refine ⟨19076270693682774240700055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12717513795788516160466703 19076270693682774240700055)
    ·
      refine ⟨28614406040524161361050083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19076270693682774240700055 28614406040524161361050083)
      ·
        refine ⟨42921609060786242041575125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28614406040524161361050083 42921609060786242041575125)
        ·
          refine ⟨1005975212362177547849417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 42921609060786242041575125 1005975212362177547849417)
          ·
            refine ⟨754481409271633160887063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005975212362177547849417 754481409271633160887063)
            ·
              refine ⟨1131722113907449741330595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754481409271633160887063 1131722113907449741330595)
              ·
                refine ⟨1697583170861174611995893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1131722113907449741330595 1697583170861174611995893)
                ·
                  refine ⟨159148422268235119874615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1697583170861174611995893 159148422268235119874615)
                  ·
                    rfl

theorem cell20_348683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 5].length) (baseStart_348683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348683 prefixEnd_348683 := by exact prefixLift 348683
  have htrace : WordTrace (prefixWord ++ tailWord_348683) baseStart_348683 baseEnd_348683 := by
    simpa [prefixWord, tailWord_348683, baseEnd_348683] using wordTrace_append hprefix tailTrace_348683
  have hstable : (prefixWord ++ tailWord_348683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348683).length < 2 ^ (prefixWord ++ tailWord_348683).sum := by decide
  have hdescent : baseEnd_348683 < baseStart_348683 := by decide
  rcases family_descends (prefixWord ++ tailWord_348683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348686 : List Nat := [4, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_348686 : Nat := 118140960795 + 348686 * 2 ^ 59
def prefixEnd_348686 : Nat := 4983230072969 + 3 ^ 40 * 348686 * 2
def baseEnd_348686 : Nat := 159149791549980442774603

theorem tailTrace_348686 : CollatzResearch.WordTrace tailWord_348686 prefixEnd_348686 159149791549980442774603 := by
  unfold tailWord_348686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1589702901847205959103239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8478415476518431781883941 1589702901847205959103239)
  ·
    refine ⟨2384554352770808938654859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1589702901847205959103239 2384554352770808938654859)
    ·
      refine ⟨3576831529156213407982289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2384554352770808938654859 3576831529156213407982289)
      ·
        refine ⟨2682623646867160055986717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3576831529156213407982289 2682623646867160055986717)
        ·
          refine ⟨1005983867575185020995019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2682623646867160055986717 1005983867575185020995019)
          ·
            refine ⟨1508975801362777531492529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005983867575185020995019 1508975801362777531492529)
            ·
              refine ⟨1131731851022083148619397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1508975801362777531492529 1131731851022083148619397)
              ·
                refine ⟨212199722066640590366137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1131731851022083148619397 212199722066640590366137)
                ·
                  refine ⟨159149791549980442774603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212199722066640590366137 159149791549980442774603)
                  ·
                    rfl

theorem cell20_348686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_348686 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348686 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348686 prefixEnd_348686 := by exact prefixLift 348686
  have htrace : WordTrace (prefixWord ++ tailWord_348686) baseStart_348686 baseEnd_348686 := by
    simpa [prefixWord, tailWord_348686, baseEnd_348686] using wordTrace_append hprefix tailTrace_348686
  have hstable : (prefixWord ++ tailWord_348686).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348686).length < 2 ^ (prefixWord ++ tailWord_348686).sum := by decide
  have hdescent : baseEnd_348686 < baseStart_348686 := by decide
  rcases family_descends (prefixWord ++ tailWord_348686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348714 : List Nat := [3, 1, 4, 1, 1, 3, 1, 6]
def baseStart_348714 : Nat := 118140960795 + 348714 * 2 ^ 59
def prefixEnd_348714 : Nat := 4983230072969 + 3 ^ 40 * 348714 * 2
def baseEnd_348714 : Nat := 53054190504312263280385

theorem tailTrace_348714 : CollatzResearch.WordTrace tailWord_348714 prefixEnd_348714 53054190504312263280385 := by
  unfold tailWord_348714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179661114669052113711299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8479096305784138969896797 3179661114669052113711299)
  ·
    refine ⟨4769491672003578170566949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3179661114669052113711299 4769491672003578170566949)
    ·
      refine ⟨894279688500670906981303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4769491672003578170566949 894279688500670906981303)
      ·
        refine ⟨1341419532751006360471955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894279688500670906981303 1341419532751006360471955)
        ·
          refine ⟨2012129299126509540707933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1341419532751006360471955 2012129299126509540707933)
          ·
            refine ⟨754548487172441077765475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2012129299126509540707933 754548487172441077765475)
            ·
              refine ⟨1131822730758661616648213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754548487172441077765475 1131822730758661616648213)
              ·
                refine ⟨53054190504312263280385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1131822730758661616648213 53054190504312263280385)
                ·
                  rfl

theorem cell20_348714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_348714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348714 prefixEnd_348714 := by exact prefixLift 348714
  have htrace : WordTrace (prefixWord ++ tailWord_348714) baseStart_348714 baseEnd_348714 := by
    simpa [prefixWord, tailWord_348714, baseEnd_348714] using wordTrace_append hprefix tailTrace_348714
  have hstable : (prefixWord ++ tailWord_348714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348714).length < 2 ^ (prefixWord ++ tailWord_348714).sum := by decide
  have hdescent : baseEnd_348714 < baseStart_348714 := by decide
  rcases family_descends (prefixWord ++ tailWord_348714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348759 : List Nat := [1, 1, 3, 2, 2, 2, 3, 3, 3]
def baseStart_348759 : Nat := 118140960795 + 348759 * 2 ^ 59
def prefixEnd_348759 : Nat := 4983230072969 + 3 ^ 40 * 348759 * 2
def baseEnd_348759 : Nat := 159183110739116633340971

theorem tailTrace_348759 : CollatzResearch.WordTrace tailWord_348759 prefixEnd_348759 159183110739116633340971 := by
  unfold tailWord_348759
  simp only [CollatzResearch.WordTrace]
  refine ⟨12720285743513181140233331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8480190495675454093488887 12720285743513181140233331)
  ·
    refine ⟨19080428615269771710349997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12720285743513181140233331 19080428615269771710349997)
    ·
      refine ⟨7155160730726164391381249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19080428615269771710349997 7155160730726164391381249)
      ·
        refine ⟨5366370548044623293535937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7155160730726164391381249 5366370548044623293535937)
        ·
          refine ⟨4024777911033467470151953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5366370548044623293535937 4024777911033467470151953)
          ·
            refine ⟨3018583433275100602613965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024777911033467470151953 3018583433275100602613965)
            ·
              refine ⟨1131968787478162725980237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3018583433275100602613965 1131968787478162725980237)
              ·
                refine ⟨424488295304311022242589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1131968787478162725980237 424488295304311022242589)
                ·
                  refine ⟨159183110739116633340971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 424488295304311022242589 159183110739116633340971)
                  ·
                    rfl

theorem cell20_348759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 3, 3].length) (baseStart_348759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348759 prefixEnd_348759 := by exact prefixLift 348759
  have htrace : WordTrace (prefixWord ++ tailWord_348759) baseStart_348759 baseEnd_348759 := by
    simpa [prefixWord, tailWord_348759, baseEnd_348759] using wordTrace_append hprefix tailTrace_348759
  have hstable : (prefixWord ++ tailWord_348759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348759).length < 2 ^ (prefixWord ++ tailWord_348759).sum := by decide
  have hdescent : baseEnd_348759 < baseStart_348759 := by decide
  rcases family_descends (prefixWord ++ tailWord_348759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348780 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_348780 : Nat := 118140960795 + 348780 * 2 ^ 59
def prefixEnd_348780 : Nat := 4983230072969 + 3 ^ 40 * 348780 * 2
def baseEnd_348780 : Nat := 159192695711333893640885

theorem tailTrace_348780 : CollatzResearch.WordTrace tailWord_348780 prefixEnd_348780 159192695711333893640885 := by
  unfold tailWord_348780
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360525838218550863373897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8480701117624734484498529 6360525838218550863373897)
  ·
    refine ⟨4770394378663913147530423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6360525838218550863373897 4770394378663913147530423)
    ·
      refine ⟨7155591567995869721295635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4770394378663913147530423 7155591567995869721295635)
      ·
        refine ⟨10733387351993804581943453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7155591567995869721295635 10733387351993804581943453)
        ·
          refine ⟨4025020256997676718228795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10733387351993804581943453 4025020256997676718228795)
          ·
            refine ⟨6037530385496515077343193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4025020256997676718228795 6037530385496515077343193)
            ·
              refine ⟨4528147789122386308007395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6037530385496515077343193 4528147789122386308007395)
              ·
                refine ⟨6792221683683579462011093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4528147789122386308007395 6792221683683579462011093)
                ·
                  refine ⟨159192695711333893640885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6792221683683579462011093 159192695711333893640885)
                  ·
                    rfl

theorem cell20_348780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_348780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348780 prefixEnd_348780 := by exact prefixLift 348780
  have htrace : WordTrace (prefixWord ++ tailWord_348780) baseStart_348780 baseEnd_348780 := by
    simpa [prefixWord, tailWord_348780, baseEnd_348780] using wordTrace_append hprefix tailTrace_348780
  have hstable : (prefixWord ++ tailWord_348780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348780).length < 2 ^ (prefixWord ++ tailWord_348780).sum := by decide
  have hdescent : baseEnd_348780 < baseStart_348780 := by decide
  rcases family_descends (prefixWord ++ tailWord_348780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348787 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 8]
def baseStart_348787 : Nat := 118140960795 + 348787 * 2 ^ 59
def prefixEnd_348787 : Nat := 4983230072969 + 3 ^ 40 * 348787 * 2
def baseEnd_348787 : Nat := 159195890702072980407523

theorem tailTrace_348787 : CollatzResearch.WordTrace tailWord_348787 prefixEnd_348787 159195890702072980407523 := by
  unfold tailWord_348787
  simp only [CollatzResearch.WordTrace]
  refine ⟨12721306987411741922252615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8480871324941161281501743 12721306987411741922252615)
  ·
    refine ⟨19081960481117612883378923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12721306987411741922252615 19081960481117612883378923)
    ·
      refine ⟨28622940721676419325068385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19081960481117612883378923 28622940721676419325068385)
      ·
        refine ⟨21467205541257314493801289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28622940721676419325068385 21467205541257314493801289)
        ·
          refine ⟨16100404155942985870350967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21467205541257314493801289 16100404155942985870350967)
          ·
            refine ⟨24150606233914478805526451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16100404155942985870350967 24150606233914478805526451)
            ·
              refine ⟨36225909350871718208289677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24150606233914478805526451 36225909350871718208289677)
              ·
                refine ⟨13584716006576894328108629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36225909350871718208289677 13584716006576894328108629)
                ·
                  refine ⟨159195890702072980407523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13584716006576894328108629 159195890702072980407523)
                  ·
                    rfl

theorem cell20_348787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_348787 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348787 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348787 prefixEnd_348787 := by exact prefixLift 348787
  have htrace : WordTrace (prefixWord ++ tailWord_348787) baseStart_348787 baseEnd_348787 := by
    simpa [prefixWord, tailWord_348787, baseEnd_348787] using wordTrace_append hprefix tailTrace_348787
  have hstable : (prefixWord ++ tailWord_348787).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348787).length < 2 ^ (prefixWord ++ tailWord_348787).sum := by decide
  have hdescent : baseEnd_348787 < baseStart_348787 := by decide
  rcases family_descends (prefixWord ++ tailWord_348787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348790 : List Nat := [5, 1, 1, 2, 3, 8]
def baseStart_348790 : Nat := 118140960795 + 348790 * 2 ^ 59
def prefixEnd_348790 : Nat := 4983230072969 + 3 ^ 40 * 348790 * 2
def baseEnd_348790 : Nat := 5896194814215492715093

theorem tailTrace_348790 : CollatzResearch.WordTrace tailWord_348790 prefixEnd_348790 5896194814215492715093 := by
  unfold tailWord_348790
  simp only [CollatzResearch.WordTrace]
  refine ⟨795088525400054589663239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8480944270933915623074549 795088525400054589663239)
  ·
    refine ⟨1192632788100081884494859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 795088525400054589663239 1192632788100081884494859)
    ·
      refine ⟨1788949182150122826742289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1192632788100081884494859 1788949182150122826742289)
      ·
        refine ⟨1341711886612592120056717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1788949182150122826742289 1341711886612592120056717)
        ·
          refine ⟨503141957479722045021269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1341711886612592120056717 503141957479722045021269)
          ·
            refine ⟨5896194814215492715093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 503141957479722045021269 5896194814215492715093)
            ·
              rfl

theorem cell20_348790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 8].length) (baseStart_348790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348790 prefixEnd_348790 := by exact prefixLift 348790
  have htrace : WordTrace (prefixWord ++ tailWord_348790) baseStart_348790 baseEnd_348790 := by
    simpa [prefixWord, tailWord_348790, baseEnd_348790] using wordTrace_append hprefix tailTrace_348790
  have hstable : (prefixWord ++ tailWord_348790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348790).length < 2 ^ (prefixWord ++ tailWord_348790).sum := by decide
  have hdescent : baseEnd_348790 < baseStart_348790 := by decide
  rcases family_descends (prefixWord ++ tailWord_348790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348800 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 2]
def baseStart_348800 : Nat := 118140960795 + 348800 * 2 ^ 59
def prefixEnd_348800 : Nat := 4983230072969 + 3 ^ 40 * 348800 * 2
def baseEnd_348800 : Nat := 159201824256302712974137

theorem tailTrace_348800 : CollatzResearch.WordTrace tailWord_348800 prefixEnd_348800 159201824256302712974137 := by
  unfold tailWord_348800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6360890568182322571237927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8481187424243096761650569 6360890568182322571237927)
  ·
    refine ⟨9541335852273483856856891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6360890568182322571237927 9541335852273483856856891)
    ·
      refine ⟨14312003778410225785285337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9541335852273483856856891 14312003778410225785285337)
      ·
        refine ⟨10734002833807669338964003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14312003778410225785285337 10734002833807669338964003)
        ·
          refine ⟨16101004250711504008446005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10734002833807669338964003 16101004250711504008446005)
          ·
            refine ⟨1509469148504203500791813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16101004250711504008446005 1509469148504203500791813)
            ·
              refine ⟨283025465344538156398465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1509469148504203500791813 283025465344538156398465)
              ·
                refine ⟨212269099008403617298849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283025465344538156398465 212269099008403617298849)
                ·
                  refine ⟨159201824256302712974137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212269099008403617298849 159201824256302712974137)
                  ·
                    rfl

theorem cell20_348800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 2].length) (baseStart_348800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348800 prefixEnd_348800 := by exact prefixLift 348800
  have htrace : WordTrace (prefixWord ++ tailWord_348800) baseStart_348800 baseEnd_348800 := by
    simpa [prefixWord, tailWord_348800, baseEnd_348800] using wordTrace_append hprefix tailTrace_348800
  have hstable : (prefixWord ++ tailWord_348800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348800).length < 2 ^ (prefixWord ++ tailWord_348800).sum := by decide
  have hdescent : baseEnd_348800 < baseStart_348800 := by decide
  rcases family_descends (prefixWord ++ tailWord_348800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348887 : List Nat := [1, 1, 3, 2, 1, 5, 1, 6]
def baseStart_348887 : Nat := 118140960795 + 348887 * 2 ^ 59
def prefixEnd_348887 : Nat := 4983230072969 + 3 ^ 40 * 348887 * 2
def baseEnd_348887 : Nat := 53080511142305692357927

theorem tailTrace_348887 : CollatzResearch.WordTrace tailWord_348887 prefixEnd_348887 53080511142305692357927 := by
  unfold tailWord_348887
  simp only [CollatzResearch.WordTrace]
  refine ⟨12724954287049459000892915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8483302858032972667261943 12724954287049459000892915)
  ·
    refine ⟨19087431430574188501339373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12724954287049459000892915 19087431430574188501339373)
    ·
      refine ⟨7157786786465320688002265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19087431430574188501339373 7157786786465320688002265)
      ·
        refine ⟨5368340089848990516001699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7157786786465320688002265 5368340089848990516001699)
        ·
          refine ⟨8052510134773485774002549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368340089848990516001699 8052510134773485774002549)
          ·
            refine ⟨754922825135014291312739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8052510134773485774002549 754922825135014291312739)
            ·
              refine ⟨1132384237702521436969109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754922825135014291312739 1132384237702521436969109)
              ·
                refine ⟨53080511142305692357927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1132384237702521436969109 53080511142305692357927)
                ·
                  rfl

theorem cell20_348887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 6].length) (baseStart_348887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348887 prefixEnd_348887 := by exact prefixLift 348887
  have htrace : WordTrace (prefixWord ++ tailWord_348887) baseStart_348887 baseEnd_348887 := by
    simpa [prefixWord, tailWord_348887, baseEnd_348887] using wordTrace_append hprefix tailTrace_348887
  have hstable : (prefixWord ++ tailWord_348887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348887).length < 2 ^ (prefixWord ++ tailWord_348887).sum := by decide
  have hdescent : baseEnd_348887 < baseStart_348887 := by decide
  rcases family_descends (prefixWord ++ tailWord_348887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348904 : List Nat := [2, 1, 4, 1, 4, 2, 6]
def baseStart_348904 : Nat := 118140960795 + 348904 * 2 ^ 59
def prefixEnd_348904 : Nat := 4983230072969 + 3 ^ 40 * 348904 * 2
def baseEnd_348904 : Nat := 17694365854460063723005

theorem tailTrace_348904 : CollatzResearch.WordTrace tailWord_348904 prefixEnd_348904 17694365854460063723005 := by
  unfold tailWord_348904
  simp only [CollatzResearch.WordTrace]
  refine ⟨6362787163993935452130883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8483716218658580602841177 6362787163993935452130883)
  ·
    refine ⟨9544180745990903178196325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6362787163993935452130883 9544180745990903178196325)
    ·
      refine ⟨1789533889873294345911811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9544180745990903178196325 1789533889873294345911811)
      ·
        refine ⟨2684300834809941518867717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1789533889873294345911811 2684300834809941518867717)
        ·
          refine ⟨503306406526864034787697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2684300834809941518867717 503306406526864034787697)
          ·
            refine ⟨377479804895148026090773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503306406526864034787697 377479804895148026090773)
            ·
              refine ⟨17694365854460063723005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 377479804895148026090773 17694365854460063723005)
              ·
                rfl

theorem cell20_348904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 6].length) (baseStart_348904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348904 prefixEnd_348904 := by exact prefixLift 348904
  have htrace : WordTrace (prefixWord ++ tailWord_348904) baseStart_348904 baseEnd_348904 := by
    simpa [prefixWord, tailWord_348904, baseEnd_348904] using wordTrace_append hprefix tailTrace_348904
  have hstable : (prefixWord ++ tailWord_348904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348904).length < 2 ^ (prefixWord ++ tailWord_348904).sum := by decide
  have hdescent : baseEnd_348904 < baseStart_348904 := by decide
  rcases family_descends (prefixWord ++ tailWord_348904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348925 : List Nat := [1, 4, 1, 1, 1, 1, 6, 5]
def baseStart_348925 : Nat := 118140960795 + 348925 * 2 ^ 59
def prefixEnd_348925 : Nat := 4983230072969 + 3 ^ 40 * 348925 * 2
def baseEnd_348925 : Nat := 53086292554119277935653

theorem tailTrace_348925 : CollatzResearch.WordTrace tailWord_348925 prefixEnd_348925 53086292554119277935653 := by
  unfold tailWord_348925
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726340260911791490776229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8484226840607860993850819 12726340260911791490776229)
  ·
    refine ⟨2386188798920960904520543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12726340260911791490776229 2386188798920960904520543)
    ·
      refine ⟨3579283198381441356780815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2386188798920960904520543 3579283198381441356780815)
      ·
        refine ⟨5368924797572162035171223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3579283198381441356780815 5368924797572162035171223)
        ·
          refine ⟨8053387196358243052756835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5368924797572162035171223 8053387196358243052756835)
          ·
            refine ⟨12080080794537364579135253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8053387196358243052756835 12080080794537364579135253)
            ·
              refine ⟨566253787243938964646965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12080080794537364579135253 566253787243938964646965)
              ·
                refine ⟨53086292554119277935653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 566253787243938964646965 53086292554119277935653)
                ·
                  rfl

theorem cell20_348925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 5].length) (baseStart_348925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348925 prefixEnd_348925 := by exact prefixLift 348925
  have htrace : WordTrace (prefixWord ++ tailWord_348925) baseStart_348925 baseEnd_348925 := by
    simpa [prefixWord, tailWord_348925, baseEnd_348925] using wordTrace_append hprefix tailTrace_348925
  have hstable : (prefixWord ++ tailWord_348925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348925).length < 2 ^ (prefixWord ++ tailWord_348925).sum := by decide
  have hdescent : baseEnd_348925 < baseStart_348925 := by decide
  rcases family_descends (prefixWord ++ tailWord_348925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348939 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 6]
def baseStart_348939 : Nat := 118140960795 + 348939 * 2 ^ 59
def prefixEnd_348939 : Nat := 4983230072969 + 3 ^ 40 * 348939 * 2
def baseEnd_348939 : Nat := 159265267643836007340235

theorem tailTrace_348939 : CollatzResearch.WordTrace tailWord_348939 prefixEnd_348939 159265267643836007340235 := by
  unfold tailWord_348939
  simp only [CollatzResearch.WordTrace]
  refine ⟨12726850882861071881785871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8484567255240714587857247 12726850882861071881785871)
  ·
    refine ⟨19090276324291607822678807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12726850882861071881785871 19090276324291607822678807)
    ·
      refine ⟨28635414486437411734018211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19090276324291607822678807 28635414486437411734018211)
      ·
        refine ⟨42953121729656117601027317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28635414486437411734018211 42953121729656117601027317)
        ·
          refine ⟨4026855162155261025096311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42953121729656117601027317 4026855162155261025096311)
          ·
            refine ⟨6040282743232891537644467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4026855162155261025096311 6040282743232891537644467)
            ·
              refine ⟨9060424114849337306466701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6040282743232891537644467 9060424114849337306466701)
              ·
                refine ⟨3397659043068501489925013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9060424114849337306466701 3397659043068501489925013)
                ·
                  refine ⟨159265267643836007340235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3397659043068501489925013 159265267643836007340235)
                  ·
                    rfl

theorem cell20_348939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_348939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_348939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_348939 prefixEnd_348939 := by exact prefixLift 348939
  have htrace : WordTrace (prefixWord ++ tailWord_348939) baseStart_348939 baseEnd_348939 := by
    simpa [prefixWord, tailWord_348939, baseEnd_348939] using wordTrace_append hprefix tailTrace_348939
  have hstable : (prefixWord ++ tailWord_348939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348939).length < 2 ^ (prefixWord ++ tailWord_348939).sum := by decide
  have hdescent : baseEnd_348939 < baseStart_348939 := by decide
  rcases family_descends (prefixWord ++ tailWord_348939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349032 : List Nat := [2, 1, 4, 2, 1, 2, 1, 3, 4]
def baseStart_349032 : Nat := 118140960795 + 349032 * 2 ^ 59
def prefixEnd_349032 : Nat := 4983230072969 + 3 ^ 40 * 349032 * 2
def baseEnd_349032 : Nat := 159307715377941017239855

theorem tailTrace_349032 : CollatzResearch.WordTrace tailWord_349032 prefixEnd_349032 159307715377941017239855 := by
  unfold tailWord_349032
  simp only [CollatzResearch.WordTrace]
  refine ⟨6365121435762074382460675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8486828581016099176614233 6365121435762074382460675)
  ·
    refine ⟨9547682153643111573691013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6365121435762074382460675 9547682153643111573691013)
    ·
      refine ⟨1790190403808083420067065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9547682153643111573691013 1790190403808083420067065)
      ·
        refine ⟨1342642802856062565050299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1790190403808083420067065 1342642802856062565050299)
        ·
          refine ⟨2013964204284093847575449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1342642802856062565050299 2013964204284093847575449)
          ·
            refine ⟨1510473153213070385681587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2013964204284093847575449 1510473153213070385681587)
            ·
              refine ⟨2265709729819605578522381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1510473153213070385681587 2265709729819605578522381)
              ·
                refine ⟨849641148682352091945893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2265709729819605578522381 849641148682352091945893)
                ·
                  refine ⟨159307715377941017239855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849641148682352091945893 159307715377941017239855)
                  ·
                    rfl

theorem cell20_349032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_349032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349032 prefixEnd_349032 := by exact prefixLift 349032
  have htrace : WordTrace (prefixWord ++ tailWord_349032) baseStart_349032 baseEnd_349032 := by
    simpa [prefixWord, tailWord_349032, baseEnd_349032] using wordTrace_append hprefix tailTrace_349032
  have hstable : (prefixWord ++ tailWord_349032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349032).length < 2 ^ (prefixWord ++ tailWord_349032).sum := by decide
  have hdescent : baseEnd_349032 < baseStart_349032 := by decide
  rcases family_descends (prefixWord ++ tailWord_349032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349066 : List Nat := [3, 1, 2, 4, 1, 1, 3, 3, 2]
def baseStart_349066 : Nat := 118140960795 + 349066 * 2 ^ 59
def prefixEnd_349066 : Nat := 4983230072969 + 3 ^ 40 * 349066 * 2
def baseEnd_349066 : Nat := 159323233904388010106383

theorem tailTrace_349066 : CollatzResearch.WordTrace tailWord_349066 prefixEnd_349066 159323233904388010106383 := by
  unfold tailWord_349066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182870738350243142914763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8487655302267315047772701 3182870738350243142914763)
  ·
    refine ⟨4774306107525364714372145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3182870738350243142914763 4774306107525364714372145)
    ·
      refine ⟨3580729580644023535779109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4774306107525364714372145 3580729580644023535779109)
      ·
        refine ⟨671386796370754412958583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3580729580644023535779109 671386796370754412958583)
        ·
          refine ⟨1007080194556131619437875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671386796370754412958583 1007080194556131619437875)
          ·
            refine ⟨1510620291834197429156813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007080194556131619437875 1510620291834197429156813)
            ·
              refine ⟨566482609437824035933805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1510620291834197429156813 566482609437824035933805)
              ·
                refine ⟨212430978539184013475177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566482609437824035933805 212430978539184013475177)
                ·
                  refine ⟨159323233904388010106383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212430978539184013475177 159323233904388010106383)
                  ·
                    rfl

theorem cell20_349066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 3, 2].length) (baseStart_349066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349066 prefixEnd_349066 := by exact prefixLift 349066
  have htrace : WordTrace (prefixWord ++ tailWord_349066) baseStart_349066 baseEnd_349066 := by
    simpa [prefixWord, tailWord_349066, baseEnd_349066] using wordTrace_append hprefix tailTrace_349066
  have hstable : (prefixWord ++ tailWord_349066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349066).length < 2 ^ (prefixWord ++ tailWord_349066).sum := by decide
  have hdescent : baseEnd_349066 < baseStart_349066 := by decide
  rcases family_descends (prefixWord ++ tailWord_349066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349077 : List Nat := [1, 3, 2, 1, 1, 6, 6]
def baseStart_349077 : Nat := 118140960795 + 349077 * 2 ^ 59
def prefixEnd_349077 : Nat := 4983230072969 + 3 ^ 40 * 349077 * 2
def baseEnd_349077 : Nat := 17703139400457873415519

theorem tailTrace_349077 : CollatzResearch.WordTrace tailWord_349077 prefixEnd_349077 17703139400457873415519 := by
  unfold tailWord_349077
  simp only [CollatzResearch.WordTrace]
  refine ⟨12731884156361121450309485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8487922770907414300206323 12731884156361121450309485)
  ·
    refine ⟨4774456558635420543866057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12731884156361121450309485 4774456558635420543866057)
    ·
      refine ⟨3580842418976565407899543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4774456558635420543866057 3580842418976565407899543)
      ·
        refine ⟨5371263628464848111849315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3580842418976565407899543 5371263628464848111849315)
        ·
          refine ⟨8056895442697272167773973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5371263628464848111849315 8056895442697272167773973)
          ·
            refine ⟨377666973876434632864405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8056895442697272167773973 377666973876434632864405)
            ·
              refine ⟨17703139400457873415519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 377666973876434632864405 17703139400457873415519)
              ·
                rfl

theorem cell20_349077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 6].length) (baseStart_349077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349077 prefixEnd_349077 := by exact prefixLift 349077
  have htrace : WordTrace (prefixWord ++ tailWord_349077) baseStart_349077 baseEnd_349077 := by
    simpa [prefixWord, tailWord_349077, baseEnd_349077] using wordTrace_append hprefix tailTrace_349077
  have hstable : (prefixWord ++ tailWord_349077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349077).length < 2 ^ (prefixWord ++ tailWord_349077).sum := by decide
  have hdescent : baseEnd_349077 < baseStart_349077 := by decide
  rcases family_descends (prefixWord ++ tailWord_349077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349087 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 4]
def baseStart_349087 : Nat := 118140960795 + 349087 * 2 ^ 59
def prefixEnd_349087 : Nat := 4983230072969 + 3 ^ 40 * 349087 * 2
def baseEnd_349087 : Nat := 159332818876605270406297

theorem tailTrace_349087 : CollatzResearch.WordTrace tailWord_349087 prefixEnd_349087 159332818876605270406297 := by
  unfold tailWord_349087
  simp only [CollatzResearch.WordTrace]
  refine ⟨12732248886324893158173515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8488165924216595438782343 12732248886324893158173515)
  ·
    refine ⟨19098373329487339737260273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12732248886324893158173515 19098373329487339737260273)
    ·
      refine ⟨14323779997115504802945205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19098373329487339737260273 14323779997115504802945205)
      ·
        refine ⟨1342854374729578575276113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14323779997115504802945205 1342854374729578575276113)
        ·
          refine ⟨1007140781047183931457085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342854374729578575276113 1007140781047183931457085)
          ·
            refine ⟨377677792892693974296407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1007140781047183931457085 377677792892693974296407)
            ·
              refine ⟨566516689339040961444611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377677792892693974296407 566516689339040961444611)
              ·
                refine ⟨849775034008561442166917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 566516689339040961444611 849775034008561442166917)
                ·
                  refine ⟨159332818876605270406297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 849775034008561442166917 159332818876605270406297)
                  ·
                    rfl

theorem cell20_349087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_349087 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349087 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349087 prefixEnd_349087 := by exact prefixLift 349087
  have htrace : WordTrace (prefixWord ++ tailWord_349087) baseStart_349087 baseEnd_349087 := by
    simpa [prefixWord, tailWord_349087, baseEnd_349087] using wordTrace_append hprefix tailTrace_349087
  have hstable : (prefixWord ++ tailWord_349087).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349087).length < 2 ^ (prefixWord ++ tailWord_349087).sum := by decide
  have hdescent : baseEnd_349087 < baseStart_349087 := by decide
  rcases family_descends (prefixWord ++ tailWord_349087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349167 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 6]
def baseStart_349167 : Nat := 118140960795 + 349167 * 2 ^ 59
def prefixEnd_349167 : Nat := 4983230072969 + 3 ^ 40 * 349167 * 2
def baseEnd_349167 : Nat := 159369333056480547739303

theorem tailTrace_349167 : CollatzResearch.WordTrace tailWord_349167 prefixEnd_349167 159369333056480547739303 := by
  unfold tailWord_349167
  simp only [CollatzResearch.WordTrace]
  refine ⟨12735166726035066821085755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8490111150690044547390503 12735166726035066821085755)
  ·
    refine ⟨19102750089052600231628633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12735166726035066821085755 19102750089052600231628633)
    ·
      refine ⟨14327062566789450173721475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19102750089052600231628633 14327062566789450173721475)
      ·
        refine ⟨21490593850184175260582213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14327062566789450173721475 21490593850184175260582213)
        ·
          refine ⟨4029486346909532861359165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21490593850184175260582213 4029486346909532861359165)
          ·
            refine ⟨1511057380091074823009687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4029486346909532861359165 1511057380091074823009687)
            ·
              refine ⟨2266586070136612234514531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511057380091074823009687 2266586070136612234514531)
              ·
                refine ⟨3399879105204918351771797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2266586070136612234514531 3399879105204918351771797)
                ·
                  refine ⟨159369333056480547739303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3399879105204918351771797 159369333056480547739303)
                  ·
                    rfl

theorem cell20_349167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_349167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349167 prefixEnd_349167 := by exact prefixLift 349167
  have htrace : WordTrace (prefixWord ++ tailWord_349167) baseStart_349167 baseEnd_349167 := by
    simpa [prefixWord, tailWord_349167, baseEnd_349167] using wordTrace_append hprefix tailTrace_349167
  have hstable : (prefixWord ++ tailWord_349167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349167).length < 2 ^ (prefixWord ++ tailWord_349167).sum := by decide
  have hdescent : baseEnd_349167 < baseStart_349167 := by decide
  rcases family_descends (prefixWord ++ tailWord_349167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349194 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 3]
def baseStart_349194 : Nat := 118140960795 + 349194 * 2 ^ 59
def prefixEnd_349194 : Nat := 4983230072969 + 3 ^ 40 * 349194 * 2
def baseEnd_349194 : Nat := 159381656592188453839193

theorem tailTrace_349194 : CollatzResearch.WordTrace tailWord_349194 prefixEnd_349194 159381656592188453839193 := by
  unfold tailWord_349194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3184037874234312608079659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8490767664624833621545757 3184037874234312608079659)
  ·
    refine ⟨4776056811351468912119489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3184037874234312608079659 4776056811351468912119489)
    ·
      refine ⟨3582042608513601684089617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4776056811351468912119489 3582042608513601684089617)
      ·
        refine ⟨2686531956385201263067213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3582042608513601684089617 2686531956385201263067213)
        ·
          refine ⟨1007449483644450473650205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2686531956385201263067213 1007449483644450473650205)
          ·
            refine ⟨377793556366668927618827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1007449483644450473650205 377793556366668927618827)
            ·
              refine ⟨566690334550003391428241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377793556366668927618827 566690334550003391428241)
              ·
                refine ⟨425017750912502543571181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566690334550003391428241 425017750912502543571181)
                ·
                  refine ⟨159381656592188453839193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425017750912502543571181 159381656592188453839193)
                  ·
                    rfl

theorem cell20_349194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_349194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349194 prefixEnd_349194 := by exact prefixLift 349194
  have htrace : WordTrace (prefixWord ++ tailWord_349194) baseStart_349194 baseEnd_349194 := by
    simpa [prefixWord, tailWord_349194, baseEnd_349194] using wordTrace_append hprefix tailTrace_349194
  have hstable : (prefixWord ++ tailWord_349194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349194).length < 2 ^ (prefixWord ++ tailWord_349194).sum := by decide
  have hdescent : baseEnd_349194 < baseStart_349194 := by decide
  rcases family_descends (prefixWord ++ tailWord_349194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349246 : List Nat := [4, 2, 1, 3, 1, 3, 6]
def baseStart_349246 : Nat := 118140960795 + 349246 * 2 ^ 59
def prefixEnd_349246 : Nat := 4983230072969 + 3 ^ 40 * 349246 * 2
def baseEnd_349246 : Nat := 17711710089900820456183

theorem tailTrace_349246 : CollatzResearch.WordTrace tailWord_349246 prefixEnd_349246 17711710089900820456183 := by
  unfold tailWord_349246
  simp only [CollatzResearch.WordTrace]
  refine ⟨1592256011593607914151449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8492032061832575542141061 1592256011593607914151449)
  ·
    refine ⟨1194192008695205935613587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1592256011593607914151449 1194192008695205935613587)
    ·
      refine ⟨1791288013042808903420381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194192008695205935613587 1791288013042808903420381)
      ·
        refine ⟨671733004891053338782643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1791288013042808903420381 671733004891053338782643)
        ·
          refine ⟨1007599507336580008173965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671733004891053338782643 1007599507336580008173965)
          ·
            refine ⟨377849815251217503065237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1007599507336580008173965 377849815251217503065237)
            ·
              refine ⟨17711710089900820456183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 377849815251217503065237 17711710089900820456183)
              ·
                rfl

theorem cell20_349246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 6].length) (baseStart_349246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349246 prefixEnd_349246 := by exact prefixLift 349246
  have htrace : WordTrace (prefixWord ++ tailWord_349246) baseStart_349246 baseEnd_349246 := by
    simpa [prefixWord, tailWord_349246, baseEnd_349246] using wordTrace_append hprefix tailTrace_349246
  have hstable : (prefixWord ++ tailWord_349246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349246).length < 2 ^ (prefixWord ++ tailWord_349246).sum := by decide
  have hdescent : baseEnd_349246 < baseStart_349246 := by decide
  rcases family_descends (prefixWord ++ tailWord_349246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349281 : List Nat := [1, 2, 3, 1, 1, 2, 2, 4, 4]
def baseStart_349281 : Nat := 118140960795 + 349281 * 2 ^ 59
def prefixEnd_349281 : Nat := 4983230072969 + 3 ^ 40 * 349281 * 2
def baseEnd_349281 : Nat := 159421365762802817938837

theorem tailTrace_349281 : CollatzResearch.WordTrace tailWord_349281 prefixEnd_349281 159421365762802817938837 := by
  unfold tailWord_349281
  simp only [CollatzResearch.WordTrace]
  refine ⟨12739324647622064290735697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8492883098414709527157131 12739324647622064290735697)
  ·
    refine ⟨9554493485716548218051773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12739324647622064290735697 9554493485716548218051773)
    ·
      refine ⟨3582935057143705581769415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9554493485716548218051773 3582935057143705581769415)
      ·
        refine ⟨5374402585715558372654123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582935057143705581769415 5374402585715558372654123)
        ·
          refine ⟨8061603878573337558981185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5374402585715558372654123 8061603878573337558981185)
          ·
            refine ⟨6046202908930003169235889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8061603878573337558981185 6046202908930003169235889)
            ·
              refine ⟨4534652181697502376926917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6046202908930003169235889 4534652181697502376926917)
              ·
                refine ⟨850247284068281695673797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4534652181697502376926917 850247284068281695673797)
                ·
                  refine ⟨159421365762802817938837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850247284068281695673797 159421365762802817938837)
                  ·
                    rfl

theorem cell20_349281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_349281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349281 prefixEnd_349281 := by exact prefixLift 349281
  have htrace : WordTrace (prefixWord ++ tailWord_349281) baseStart_349281 baseEnd_349281 := by
    simpa [prefixWord, tailWord_349281, baseEnd_349281] using wordTrace_append hprefix tailTrace_349281
  have hstable : (prefixWord ++ tailWord_349281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349281).length < 2 ^ (prefixWord ++ tailWord_349281).sum := by decide
  have hdescent : baseEnd_349281 < baseStart_349281 := by decide
  rcases family_descends (prefixWord ++ tailWord_349281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349305 : List Nat := [1, 2, 1, 3, 6, 7]
def baseStart_349305 : Nat := 118140960795 + 349305 * 2 ^ 59
def prefixEnd_349305 : Nat := 4983230072969 + 3 ^ 40 * 349305 * 2
def baseEnd_349305 : Nat := 5904900741361681523657

theorem tailTrace_349305 : CollatzResearch.WordTrace tailWord_349305 prefixEnd_349305 5904900741361681523657 := by
  unfold tailWord_349305
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740199999535116389609369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8493466666356744259739579 12740199999535116389609369)
  ·
    refine ⟨9555149999651337292207027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12740199999535116389609369 9555149999651337292207027)
    ·
      refine ⟨14332724999477005938310541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9555149999651337292207027 14332724999477005938310541)
      ·
        refine ⟨5374771874803877226866453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14332724999477005938310541 5374771874803877226866453)
        ·
          refine ⟨251942431631431745009365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5374771874803877226866453 251942431631431745009365)
          ·
            refine ⟨5904900741361681523657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 251942431631431745009365 5904900741361681523657)
            ·
              rfl

theorem cell20_349305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 7].length) (baseStart_349305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349305 prefixEnd_349305 := by exact prefixLift 349305
  have htrace : WordTrace (prefixWord ++ tailWord_349305) baseStart_349305 baseEnd_349305 := by
    simpa [prefixWord, tailWord_349305, baseEnd_349305] using wordTrace_append hprefix tailTrace_349305
  have hstable : (prefixWord ++ tailWord_349305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349305).length < 2 ^ (prefixWord ++ tailWord_349305).sum := by decide
  have hdescent : baseEnd_349305 < baseStart_349305 := by decide
  rcases family_descends (prefixWord ++ tailWord_349305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349312 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_349312 : Nat := 118140960795 + 349312 * 2 ^ 59
def prefixEnd_349312 : Nat := 4983230072969 + 3 ^ 40 * 349312 * 2
def baseEnd_349312 : Nat := 159435515007504487905377

theorem tailTrace_349312 : CollatzResearch.WordTrace tailWord_349312 prefixEnd_349312 159435515007504487905377 := by
  unfold tailWord_349312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370227655254878292557095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8493636873673171056742793 6370227655254878292557095)
  ·
    refine ⟨9555341482882317438835643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370227655254878292557095 9555341482882317438835643)
    ·
      refine ⟨14333012224323476158253465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9555341482882317438835643 14333012224323476158253465)
      ·
        refine ⟨10749759168242607118690099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14333012224323476158253465 10749759168242607118690099)
        ·
          refine ⟨16124638752363910678035149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10749759168242607118690099 16124638752363910678035149)
          ·
            refine ⟨6046739532136466504263181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16124638752363910678035149 6046739532136466504263181)
            ·
              refine ⟨2267527324551174939098693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6046739532136466504263181 2267527324551174939098693)
              ·
                refine ⟨425161373353345301081005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2267527324551174939098693 425161373353345301081005)
                ·
                  refine ⟨159435515007504487905377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425161373353345301081005 159435515007504487905377)
                  ·
                    rfl

theorem cell20_349312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_349312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349312 prefixEnd_349312 := by exact prefixLift 349312
  have htrace : WordTrace (prefixWord ++ tailWord_349312) baseStart_349312 baseEnd_349312 := by
    simpa [prefixWord, tailWord_349312, baseEnd_349312] using wordTrace_append hprefix tailTrace_349312
  have hstable : (prefixWord ++ tailWord_349312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349312).length < 2 ^ (prefixWord ++ tailWord_349312).sum := by decide
  have hdescent : baseEnd_349312 < baseStart_349312 := by decide
  rcases family_descends (prefixWord ++ tailWord_349312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349319 : List Nat := [1, 1, 4, 2, 1, 1, 1, 5, 4]
def baseStart_349319 : Nat := 118140960795 + 349319 * 2 ^ 59
def prefixEnd_349319 : Nat := 4983230072969 + 3 ^ 40 * 349319 * 2
def baseEnd_349319 : Nat := 159438709998243574672015

theorem tailTrace_349319 : CollatzResearch.WordTrace tailWord_349319 prefixEnd_349319 159438709998243574672015 := by
  unfold tailWord_349319
  simp only [CollatzResearch.WordTrace]
  refine ⟨12740710621484396780619011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8493807080989597853746007 12740710621484396780619011)
  ·
    refine ⟨19111065932226595170928517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12740710621484396780619011 19111065932226595170928517)
    ·
      refine ⟨3583324862292486594549097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19111065932226595170928517 3583324862292486594549097)
      ·
        refine ⟨2687493646719364945911823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3583324862292486594549097 2687493646719364945911823)
        ·
          refine ⟨4031240470079047418867735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2687493646719364945911823 4031240470079047418867735)
          ·
            refine ⟨6046860705118571128301603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4031240470079047418867735 6046860705118571128301603)
            ·
              refine ⟨9070291057677856692452405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6046860705118571128301603 9070291057677856692452405)
              ·
                refine ⟨850339786657299064917413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9070291057677856692452405 850339786657299064917413)
                ·
                  refine ⟨159438709998243574672015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850339786657299064917413 159438709998243574672015)
                  ·
                    rfl

theorem cell20_349319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_349319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349319 prefixEnd_349319 := by exact prefixLift 349319
  have htrace : WordTrace (prefixWord ++ tailWord_349319) baseStart_349319 baseEnd_349319 := by
    simpa [prefixWord, tailWord_349319, baseEnd_349319] using wordTrace_append hprefix tailTrace_349319
  have hstable : (prefixWord ++ tailWord_349319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349319).length < 2 ^ (prefixWord ++ tailWord_349319).sum := by decide
  have hdescent : baseEnd_349319 < baseStart_349319 := by decide
  rcases family_descends (prefixWord ++ tailWord_349319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349336 : List Nat := [2, 1, 2, 4, 2, 2, 1, 2, 4]
def baseStart_349336 : Nat := 118140960795 + 349336 * 2 ^ 59
def prefixEnd_349336 : Nat := 4983230072969 + 3 ^ 40 * 349336 * 2
def baseEnd_349336 : Nat := 159446469261467071105279

theorem tailTrace_349336 : CollatzResearch.WordTrace tailWord_349336 prefixEnd_349336 159446469261467071105279 := by
  unfold tailWord_349336
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370665331211404341993931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8494220441615205789325241 6370665331211404341993931)
  ·
    refine ⟨9555997996817106512990897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370665331211404341993931 9555997996817106512990897)
    ·
      refine ⟨7166998497612829884743173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9555997996817106512990897 7166998497612829884743173)
      ·
        refine ⟨1343812218302405603389345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7166998497612829884743173 1343812218302405603389345)
        ·
          refine ⟨1007859163726804202542009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1343812218302405603389345 1007859163726804202542009)
          ·
            refine ⟨755894372795103151906507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007859163726804202542009 755894372795103151906507)
            ·
              refine ⟨1133841559192654727859761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 755894372795103151906507 1133841559192654727859761)
              ·
                refine ⟨850381169394491045894821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1133841559192654727859761 850381169394491045894821)
                ·
                  refine ⟨159446469261467071105279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850381169394491045894821 159446469261467071105279)
                  ·
                    rfl

theorem cell20_349336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_349336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349336 prefixEnd_349336 := by exact prefixLift 349336
  have htrace : WordTrace (prefixWord ++ tailWord_349336) baseStart_349336 baseEnd_349336 := by
    simpa [prefixWord, tailWord_349336, baseEnd_349336] using wordTrace_append hprefix tailTrace_349336
  have hstable : (prefixWord ++ tailWord_349336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349336).length < 2 ^ (prefixWord ++ tailWord_349336).sum := by decide
  have hdescent : baseEnd_349336 < baseStart_349336 := by decide
  rcases family_descends (prefixWord ++ tailWord_349336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349374 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_349374 : Nat := 118140960795 + 349374 * 2 ^ 59
def prefixEnd_349374 : Nat := 4983230072969 + 3 ^ 40 * 349374 * 2
def baseEnd_349374 : Nat := 159463813496907827838457

theorem tailTrace_349374 : CollatzResearch.WordTrace tailWord_349374 prefixEnd_349374 159463813496907827838457 := by
  unfold tailWord_349374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1592839579535642646733897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8495144424190094115914117 1592839579535642646733897)
  ·
    refine ⟨1194629684651731985050423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1592839579535642646733897 1194629684651731985050423)
    ·
      refine ⟨1791944526977597977575635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1194629684651731985050423 1791944526977597977575635)
      ·
        refine ⟨2687916790466396966363453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1791944526977597977575635 2687916790466396966363453)
        ·
          refine ⟨1007968796424898862386295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2687916790466396966363453 1007968796424898862386295)
          ·
            refine ⟨1511953194637348293579443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007968796424898862386295 1511953194637348293579443)
            ·
              refine ⟨2267929791956022440369165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1511953194637348293579443 2267929791956022440369165)
              ·
                refine ⟨850473671983508415138437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2267929791956022440369165 850473671983508415138437)
                ·
                  refine ⟨159463813496907827838457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 850473671983508415138437 159463813496907827838457)
                  ·
                    rfl

theorem cell20_349374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_349374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349374 prefixEnd_349374 := by exact prefixLift 349374
  have htrace : WordTrace (prefixWord ++ tailWord_349374) baseStart_349374 baseEnd_349374 := by
    simpa [prefixWord, tailWord_349374, baseEnd_349374] using wordTrace_append hprefix tailTrace_349374
  have hstable : (prefixWord ++ tailWord_349374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349374).length < 2 ^ (prefixWord ++ tailWord_349374).sum := by decide
  have hdescent : baseEnd_349374 < baseStart_349374 := by decide
  rcases family_descends (prefixWord ++ tailWord_349374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349443 : List Nat := [1, 1, 1, 3, 2, 4, 4, 1, 3]
def baseStart_349443 : Nat := 118140960795 + 349443 * 2 ^ 59
def prefixEnd_349443 : Nat := 4983230072969 + 3 ^ 40 * 349443 * 2
def baseEnd_349443 : Nat := 159495306977050254538175

theorem tailTrace_349443 : CollatzResearch.WordTrace tailWord_349443 prefixEnd_349443 159495306977050254538175 := by
  unfold tailWord_349443
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745233273035165958132983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8496822182023443972088655 12745233273035165958132983)
  ·
    refine ⟨19117849909552748937199475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12745233273035165958132983 19117849909552748937199475)
    ·
      refine ⟨28676774864329123405799213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19117849909552748937199475 28676774864329123405799213)
      ·
        refine ⟨10753790574123421277174705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28676774864329123405799213 10753790574123421277174705)
        ·
          refine ⟨8065342930592565957881029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10753790574123421277174705 8065342930592565957881029)
          ·
            refine ⟨1512251799486106117102693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8065342930592565957881029 1512251799486106117102693)
            ·
              refine ⟨283547212403644896956755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1512251799486106117102693 283547212403644896956755)
              ·
                refine ⟨425320818605467345435133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283547212403644896956755 425320818605467345435133)
                ·
                  refine ⟨159495306977050254538175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425320818605467345435133 159495306977050254538175)
                  ·
                    rfl

theorem cell20_349443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 3].length) (baseStart_349443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349443 prefixEnd_349443 := by exact prefixLift 349443
  have htrace : WordTrace (prefixWord ++ tailWord_349443) baseStart_349443 baseEnd_349443 := by
    simpa [prefixWord, tailWord_349443, baseEnd_349443] using wordTrace_append hprefix tailTrace_349443
  have hstable : (prefixWord ++ tailWord_349443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349443).length < 2 ^ (prefixWord ++ tailWord_349443).sum := by decide
  have hdescent : baseEnd_349443 < baseStart_349443 := by decide
  rcases family_descends (prefixWord ++ tailWord_349443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349488 : List Nat := [2, 1, 1, 1, 2, 2, 5, 4, 2]
def baseStart_349488 : Nat := 118140960795 + 349488 * 2 ^ 59
def prefixEnd_349488 : Nat := 4983230072969 + 3 ^ 40 * 349488 * 2
def baseEnd_349488 : Nat := 159515846203230098037991

theorem tailTrace_349488 : CollatzResearch.WordTrace tailWord_349488 prefixEnd_349488 159515846203230098037991 := by
  unfold tailWord_349488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6373437278936069321760559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8497916371914759095680745 6373437278936069321760559)
  ·
    refine ⟨9560155918404103982640839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6373437278936069321760559 9560155918404103982640839)
    ·
      refine ⟨14340233877606155973961259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9560155918404103982640839 14340233877606155973961259)
      ·
        refine ⟨21510350816409233960941889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14340233877606155973961259 21510350816409233960941889)
        ·
          refine ⟨16132763112306925470706417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21510350816409233960941889 16132763112306925470706417)
          ·
            refine ⟨12099572334230194103029813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16132763112306925470706417 12099572334230194103029813)
            ·
              refine ⟨1134334906334080697159045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12099572334230194103029813 1134334906334080697159045)
              ·
                refine ⟨212687794937640130717321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1134334906334080697159045 212687794937640130717321)
                ·
                  refine ⟨159515846203230098037991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212687794937640130717321 159515846203230098037991)
                  ·
                    rfl

theorem cell20_349488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 2].length) (baseStart_349488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349488 prefixEnd_349488 := by exact prefixLift 349488
  have htrace : WordTrace (prefixWord ++ tailWord_349488) baseStart_349488 baseEnd_349488 := by
    simpa [prefixWord, tailWord_349488, baseEnd_349488] using wordTrace_append hprefix tailTrace_349488
  have hstable : (prefixWord ++ tailWord_349488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349488).length < 2 ^ (prefixWord ++ tailWord_349488).sum := by decide
  have hdescent : baseEnd_349488 < baseStart_349488 := by decide
  rcases family_descends (prefixWord ++ tailWord_349488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349523 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_349523 : Nat := 118140960795 + 349523 * 2 ^ 59
def prefixEnd_349523 : Nat := 4983230072969 + 3 ^ 40 * 349523 * 2
def baseEnd_349523 : Nat := 159531821156925531871181

theorem tailTrace_349523 : CollatzResearch.WordTrace tailWord_349523 prefixEnd_349523 159531821156925531871181 := by
  unfold tailWord_349523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12748151112745339621045223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8498767408496893080696815 12748151112745339621045223)
  ·
    refine ⟨19122226669118009431567835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12748151112745339621045223 19122226669118009431567835)
    ·
      refine ⟨28683340003677014147351753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19122226669118009431567835 28683340003677014147351753)
      ·
        refine ⟨21512505002757760610513815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28683340003677014147351753 21512505002757760610513815)
        ·
          refine ⟨32268757504136640915770723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21512505002757760610513815 32268757504136640915770723)
          ·
            refine ⟨48403136256204961373656085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32268757504136640915770723 48403136256204961373656085)
            ·
              refine ⟨2268897012009607564390129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 48403136256204961373656085 2268897012009607564390129)
              ·
                refine ⟨1701672759007205673292597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2268897012009607564390129 1701672759007205673292597)
                ·
                  refine ⟨159531821156925531871181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701672759007205673292597 159531821156925531871181)
                  ·
                    rfl

theorem cell20_349523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_349523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349523 prefixEnd_349523 := by exact prefixLift 349523
  have htrace : WordTrace (prefixWord ++ tailWord_349523) baseStart_349523 baseEnd_349523 := by
    simpa [prefixWord, tailWord_349523, baseEnd_349523] using wordTrace_append hprefix tailTrace_349523
  have hstable : (prefixWord ++ tailWord_349523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349523).length < 2 ^ (prefixWord ++ tailWord_349523).sum := by decide
  have hdescent : baseEnd_349523 < baseStart_349523 := by decide
  rcases family_descends (prefixWord ++ tailWord_349523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349540 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 5]
def baseStart_349540 : Nat := 118140960795 + 349540 * 2 ^ 59
def prefixEnd_349540 : Nat := 4983230072969 + 3 ^ 40 * 349540 * 2
def baseEnd_349540 : Nat := 159539580420149028304445

theorem tailTrace_349540 : CollatzResearch.WordTrace tailWord_349540 prefixEnd_349540 159539580420149028304445 := by
  unfold tailWord_349540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6374385576841875762207037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8499180769122501016276049 6374385576841875762207037)
  ·
    refine ⟨2390394591315703410827639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6374385576841875762207037 2390394591315703410827639)
    ·
      refine ⟨3585591886973555116241459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2390394591315703410827639 3585591886973555116241459)
      ·
        refine ⟨5378387830460332674362189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3585591886973555116241459 5378387830460332674362189)
        ·
          refine ⟨2016895436422624752885821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5378387830460332674362189 2016895436422624752885821)
          ·
            refine ⟨756335788658484282332183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2016895436422624752885821 756335788658484282332183)
            ·
              refine ⟨1134503682987726423498275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756335788658484282332183 1134503682987726423498275)
              ·
                refine ⟨1701755524481589635247413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1134503682987726423498275 1701755524481589635247413)
                ·
                  refine ⟨159539580420149028304445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1701755524481589635247413 159539580420149028304445)
                  ·
                    rfl

theorem cell20_349540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_349540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349540 prefixEnd_349540 := by exact prefixLift 349540
  have htrace : WordTrace (prefixWord ++ tailWord_349540) baseStart_349540 baseEnd_349540 := by
    simpa [prefixWord, tailWord_349540, baseEnd_349540] using wordTrace_append hprefix tailTrace_349540
  have hstable : (prefixWord ++ tailWord_349540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349540).length < 2 ^ (prefixWord ++ tailWord_349540).sum := by decide
  have hdescent : baseEnd_349540 < baseStart_349540 := by decide
  rcases family_descends (prefixWord ++ tailWord_349540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349554 : List Nat := [3, 2, 1, 2, 1, 2, 2, 7]
def baseStart_349554 : Nat := 118140960795 + 349554 * 2 ^ 59
def prefixEnd_349554 : Nat := 4983230072969 + 3 ^ 40 * 349554 * 2
def baseEnd_349554 : Nat := 53181990133875733945907

theorem tailTrace_349554 : CollatzResearch.WordTrace tailWord_349554 prefixEnd_349554 53181990133875733945907 := by
  unfold tailWord_349554
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187320443908257978855929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8499521183755354610282477 3187320443908257978855929)
  ·
    refine ⟨2390490332931193484141947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3187320443908257978855929 2390490332931193484141947)
    ·
      refine ⟨3585735499396790226212921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2390490332931193484141947 3585735499396790226212921)
      ·
        refine ⟨2689301624547592669659691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3585735499396790226212921 2689301624547592669659691)
        ·
          refine ⟨4033952436821389004489537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2689301624547592669659691 4033952436821389004489537)
          ·
            refine ⟨3025464327616041753367153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4033952436821389004489537 3025464327616041753367153)
            ·
              refine ⟨2269098245712031315025365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3025464327616041753367153 2269098245712031315025365)
              ·
                refine ⟨53181990133875733945907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2269098245712031315025365 53181990133875733945907)
                ·
                  rfl

theorem cell20_349554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 7].length) (baseStart_349554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349554 prefixEnd_349554 := by exact prefixLift 349554
  have htrace : WordTrace (prefixWord ++ tailWord_349554) baseStart_349554 baseEnd_349554 := by
    simpa [prefixWord, tailWord_349554, baseEnd_349554] using wordTrace_append hprefix tailTrace_349554
  have hstable : (prefixWord ++ tailWord_349554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349554).length < 2 ^ (prefixWord ++ tailWord_349554).sum := by decide
  have hdescent : baseEnd_349554 < baseStart_349554 := by decide
  rcases family_descends (prefixWord ++ tailWord_349554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349571 : List Nat := [1, 1, 1, 3, 5, 1, 4, 4]
def baseStart_349571 : Nat := 118140960795 + 349571 * 2 ^ 59
def prefixEnd_349571 : Nat := 4983230072969 + 3 ^ 40 * 349571 * 2
def baseEnd_349571 : Nat := 53184576554950232756995

theorem tailTrace_349571 : CollatzResearch.WordTrace tailWord_349571 prefixEnd_349571 53184576554950232756995 := by
  unfold tailWord_349571
  simp only [CollatzResearch.WordTrace]
  refine ⟨12749901816571443818792567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8499934544380962545861711 12749901816571443818792567)
  ·
    refine ⟨19124852724857165728188851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12749901816571443818792567 19124852724857165728188851)
    ·
      refine ⟨28687279087285748592283277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19124852724857165728188851 28687279087285748592283277)
      ·
        refine ⟨10757729657732155722106229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28687279087285748592283277 10757729657732155722106229)
        ·
          refine ⟨1008537155412389598947459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10757729657732155722106229 1008537155412389598947459)
          ·
            refine ⟨1512805733118584398421189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008537155412389598947459 1512805733118584398421189)
            ·
              refine ⟨283651074959734574703973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1512805733118584398421189 283651074959734574703973)
              ·
                refine ⟨53184576554950232756995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283651074959734574703973 53184576554950232756995)
                ·
                  rfl

theorem cell20_349571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 4].length) (baseStart_349571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349571 prefixEnd_349571 := by exact prefixLift 349571
  have htrace : WordTrace (prefixWord ++ tailWord_349571) baseStart_349571 baseEnd_349571 := by
    simpa [prefixWord, tailWord_349571, baseEnd_349571] using wordTrace_append hprefix tailTrace_349571
  have hstable : (prefixWord ++ tailWord_349571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349571).length < 2 ^ (prefixWord ++ tailWord_349571).sum := by decide
  have hdescent : baseEnd_349571 < baseStart_349571 := by decide
  rcases family_descends (prefixWord ++ tailWord_349571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349598 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_349598 : Nat := 118140960795 + 349598 * 2 ^ 59
def prefixEnd_349598 : Nat := 4983230072969 + 3 ^ 40 * 349598 * 2
def baseEnd_349598 : Nat := 159566053200558604370875

theorem tailTrace_349598 : CollatzResearch.WordTrace tailWord_349598 prefixEnd_349598 159566053200558604370875 := by
  unfold tailWord_349598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593860823434203428753181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8500591058315751620016965 1593860823434203428753181)
  ·
    refine ⟨597697808787826285782443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1593860823434203428753181 597697808787826285782443)
    ·
      refine ⟨896546713181739428673665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 597697808787826285782443 896546713181739428673665)
      ·
        refine ⟨672410034886304571505249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 896546713181739428673665 672410034886304571505249)
        ·
          refine ⟨504307526164728428628937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 672410034886304571505249 504307526164728428628937)
          ·
            refine ⟨378230644623546321471703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504307526164728428628937 378230644623546321471703)
            ·
              refine ⟨567345966935319482207555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378230644623546321471703 567345966935319482207555)
              ·
                refine ⟨851018950402979223311333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567345966935319482207555 851018950402979223311333)
                ·
                  refine ⟨159566053200558604370875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851018950402979223311333 159566053200558604370875)
                  ·
                    rfl

theorem cell20_349598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_349598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349598 prefixEnd_349598 := by exact prefixLift 349598
  have htrace : WordTrace (prefixWord ++ tailWord_349598) baseStart_349598 baseEnd_349598 := by
    simpa [prefixWord, tailWord_349598, baseEnd_349598] using wordTrace_append hprefix tailTrace_349598
  have hstable : (prefixWord ++ tailWord_349598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349598).length < 2 ^ (prefixWord ++ tailWord_349598).sum := by decide
  have hdescent : baseEnd_349598 < baseStart_349598 := by decide
  rcases family_descends (prefixWord ++ tailWord_349598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349602 : List Nat := [3, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_349602 : Nat := 118140960795 + 349602 * 2 ^ 59
def prefixEnd_349602 : Nat := 4983230072969 + 3 ^ 40 * 349602 * 2
def baseEnd_349602 : Nat := 159567878909552368237525

theorem tailTrace_349602 : CollatzResearch.WordTrace tailWord_349602 prefixEnd_349602 159567878909552368237525 := by
  unfold tailWord_349602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187758119864784028292765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8500688319639424075447373 3187758119864784028292765)
  ·
    refine ⟨1195409294949294010609787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3187758119864784028292765 1195409294949294010609787)
    ·
      refine ⟨1793113942423941015914681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195409294949294010609787 1793113942423941015914681)
      ·
        refine ⟨1344835456817955761936011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1793113942423941015914681 1344835456817955761936011)
        ·
          refine ⟨2017253185226933642904017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344835456817955761936011 2017253185226933642904017)
          ·
            refine ⟨1512939888920200232178013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017253185226933642904017 1512939888920200232178013)
            ·
              refine ⟨567352458345075087066755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1512939888920200232178013 567352458345075087066755)
              ·
                refine ⟨851028687517612630600133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567352458345075087066755 851028687517612630600133)
                ·
                  refine ⟨159567878909552368237525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851028687517612630600133 159567878909552368237525)
                  ·
                    rfl

theorem cell20_349602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_349602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349602 prefixEnd_349602 := by exact prefixLift 349602
  have htrace : WordTrace (prefixWord ++ tailWord_349602) baseStart_349602 baseEnd_349602 := by
    simpa [prefixWord, tailWord_349602, baseEnd_349602] using wordTrace_append hprefix tailTrace_349602
  have hstable : (prefixWord ++ tailWord_349602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349602).length < 2 ^ (prefixWord ++ tailWord_349602).sum := by decide
  have hdescent : baseEnd_349602 < baseStart_349602 := by decide
  rcases family_descends (prefixWord ++ tailWord_349602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349608 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 3]
def baseStart_349608 : Nat := 118140960795 + 349608 * 2 ^ 59
def prefixEnd_349608 : Nat := 4983230072969 + 3 ^ 40 * 349608 * 2
def baseEnd_349608 : Nat := 159570617473043014037501

theorem tailTrace_349608 : CollatzResearch.WordTrace tailWord_349608 prefixEnd_349608 159570617473043014037501 := by
  unfold tailWord_349608
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375625658718699568944739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8500834211624932758592985 6375625658718699568944739)
  ·
    refine ⟨9563438488078049353417109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6375625658718699568944739 9563438488078049353417109)
    ·
      refine ⟨448286179128658563441427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9563438488078049353417109 448286179128658563441427)
      ·
        refine ⟨672429268692987845162141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448286179128658563441427 672429268692987845162141)
        ·
          refine ⟨252160975759870441935803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672429268692987845162141 252160975759870441935803)
          ·
            refine ⟨378241463639805662903705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252160975759870441935803 378241463639805662903705)
            ·
              refine ⟨283681097729854247177779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378241463639805662903705 283681097729854247177779)
              ·
                refine ⟨425521646594781370766669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283681097729854247177779 425521646594781370766669)
                ·
                  refine ⟨159570617473043014037501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425521646594781370766669 159570617473043014037501)
                  ·
                    rfl

theorem cell20_349608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_349608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349608 prefixEnd_349608 := by exact prefixLift 349608
  have htrace : WordTrace (prefixWord ++ tailWord_349608) baseStart_349608 baseEnd_349608 := by
    simpa [prefixWord, tailWord_349608, baseEnd_349608] using wordTrace_append hprefix tailTrace_349608
  have hstable : (prefixWord ++ tailWord_349608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349608).length < 2 ^ (prefixWord ++ tailWord_349608).sum := by decide
  have hdescent : baseEnd_349608 < baseStart_349608 := by decide
  rcases family_descends (prefixWord ++ tailWord_349608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349640 : List Nat := [2, 1, 3, 1, 3, 1, 2, 5, 2]
def baseStart_349640 : Nat := 118140960795 + 349640 * 2 ^ 59
def prefixEnd_349640 : Nat := 4983230072969 + 3 ^ 40 * 349640 * 2
def baseEnd_349640 : Nat := 159585223144993124970703

theorem tailTrace_349640 : CollatzResearch.WordTrace tailWord_349640 prefixEnd_349640 159585223144993124970703 := by
  unfold tailWord_349640
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376209226660734301527187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8501612302214312402036249 6376209226660734301527187)
  ·
    refine ⟨9564313839991101452290781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6376209226660734301527187 9564313839991101452290781)
    ·
      refine ⟨3586617689996663044609043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9564313839991101452290781 3586617689996663044609043)
      ·
        refine ⟨5379926534994994566913565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586617689996663044609043 5379926534994994566913565)
        ·
          refine ⟨2017472450623122962592587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5379926534994994566913565 2017472450623122962592587)
          ·
            refine ⟨3026208675934684443888881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017472450623122962592587 3026208675934684443888881)
            ·
              refine ⟨2269656506951013332916661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026208675934684443888881 2269656506951013332916661)
              ·
                refine ⟨212780297526657499960937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2269656506951013332916661 212780297526657499960937)
                ·
                  refine ⟨159585223144993124970703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212780297526657499960937 159585223144993124970703)
                  ·
                    rfl

theorem cell20_349640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_349640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349640 prefixEnd_349640 := by exact prefixLift 349640
  have htrace : WordTrace (prefixWord ++ tailWord_349640) baseStart_349640 baseEnd_349640 := by
    simpa [prefixWord, tailWord_349640, baseEnd_349640] using wordTrace_append hprefix tailTrace_349640
  have hstable : (prefixWord ++ tailWord_349640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349640).length < 2 ^ (prefixWord ++ tailWord_349640).sum := by decide
  have hdescent : baseEnd_349640 < baseStart_349640 := by decide
  rcases family_descends (prefixWord ++ tailWord_349640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349657 : List Nat := [1, 2, 1, 2, 4, 2, 4, 2, 2]
def baseStart_349657 : Nat := 118140960795 + 349657 * 2 ^ 59
def prefixEnd_349657 : Nat := 4983230072969 + 3 ^ 40 * 349657 * 2
def baseEnd_349657 : Nat := 159592982408216621403967

theorem tailTrace_349657 : CollatzResearch.WordTrace tailWord_349657 prefixEnd_349657 159592982408216621403967 := by
  unfold tailWord_349657
  simp only [CollatzResearch.WordTrace]
  refine ⟨12753038494259880506423225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8502025662839920337615483 12753038494259880506423225)
  ·
    refine ⟨9564778870694910379817419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12753038494259880506423225 9564778870694910379817419)
    ·
      refine ⟨14347168306042365569726129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9564778870694910379817419 14347168306042365569726129)
      ·
        refine ⟨10760376229531774177294597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14347168306042365569726129 10760376229531774177294597)
        ·
          refine ⟨2017570543037207658242737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10760376229531774177294597 2017570543037207658242737)
          ·
            refine ⟨1513177907277905743682053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2017570543037207658242737 1513177907277905743682053)
            ·
              refine ⟨283720857614607326940385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1513177907277905743682053 283720857614607326940385)
              ·
                refine ⟨212790643210955495205289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283720857614607326940385 212790643210955495205289)
                ·
                  refine ⟨159592982408216621403967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212790643210955495205289 159592982408216621403967)
                  ·
                    rfl

theorem cell20_349657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_349657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349657 prefixEnd_349657 := by exact prefixLift 349657
  have htrace : WordTrace (prefixWord ++ tailWord_349657) baseStart_349657 baseEnd_349657 := by
    simpa [prefixWord, tailWord_349657, baseEnd_349657] using wordTrace_append hprefix tailTrace_349657
  have hstable : (prefixWord ++ tailWord_349657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349657).length < 2 ^ (prefixWord ++ tailWord_349657).sum := by decide
  have hdescent : baseEnd_349657 < baseStart_349657 := by decide
  rcases family_descends (prefixWord ++ tailWord_349657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349706 : List Nat := [3, 1, 2, 2, 2, 3, 7]
def baseStart_349706 : Nat := 118140960795 + 349706 * 2 ^ 59
def prefixEnd_349706 : Nat := 4983230072969 + 3 ^ 40 * 349706 * 2
def baseEnd_349706 : Nat := 17735038593710025418937

theorem tailTrace_349706 : CollatzResearch.WordTrace tailWord_349706 prefixEnd_349706 17735038593710025418937 := by
  unfold tailWord_349706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188706417770590468739243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8503217114054907916637981 3188706417770590468739243)
  ·
    refine ⟨4783059626655885703108865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3188706417770590468739243 4783059626655885703108865)
    ·
      refine ⟨3587294719991914277331649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4783059626655885703108865 3587294719991914277331649)
      ·
        refine ⟨2690471039993935707998737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3587294719991914277331649 2690471039993935707998737)
        ·
          refine ⟨2017853279995451780999053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2690471039993935707998737 2017853279995451780999053)
          ·
            refine ⟨756694979998294417874645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2017853279995451780999053 756694979998294417874645)
            ·
              refine ⟨17735038593710025418937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 756694979998294417874645 17735038593710025418937)
              ·
                rfl

theorem cell20_349706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 7].length) (baseStart_349706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349706 prefixEnd_349706 := by exact prefixLift 349706
  have htrace : WordTrace (prefixWord ++ tailWord_349706) baseStart_349706 baseEnd_349706 := by
    simpa [prefixWord, tailWord_349706, baseEnd_349706] using wordTrace_append hprefix tailTrace_349706
  have hstable : (prefixWord ++ tailWord_349706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349706).length < 2 ^ (prefixWord ++ tailWord_349706).sum := by decide
  have hdescent : baseEnd_349706 < baseStart_349706 := by decide
  rcases family_descends (prefixWord ++ tailWord_349706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349713 : List Nat := [1, 2, 2, 1, 1, 2, 5, 1, 5]
def baseStart_349713 : Nat := 118140960795 + 349713 * 2 ^ 59
def prefixEnd_349713 : Nat := 4983230072969 + 3 ^ 40 * 349713 * 2
def baseEnd_349713 : Nat := 159618542334129315537071

theorem tailTrace_349713 : CollatzResearch.WordTrace tailWord_349713 prefixEnd_349713 159618542334129315537071 := by
  unfold tailWord_349713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755080982057002070461793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8503387321371334713641195 12755080982057002070461793)
  ·
    refine ⟨9566310736542751552846345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12755080982057002070461793 9566310736542751552846345)
    ·
      refine ⟨7174733052407063664634759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9566310736542751552846345 7174733052407063664634759)
      ·
        refine ⟨10762099578610595496952139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7174733052407063664634759 10762099578610595496952139)
        ·
          refine ⟨16143149367915893245428209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10762099578610595496952139 16143149367915893245428209)
          ·
            refine ⟨12107362025936919934071157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16143149367915893245428209 12107362025936919934071157)
            ·
              refine ⟨1135065189931586243819171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12107362025936919934071157 1135065189931586243819171)
              ·
                refine ⟨1702597784897379365728757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1135065189931586243819171 1702597784897379365728757)
                ·
                  refine ⟨159618542334129315537071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702597784897379365728757 159618542334129315537071)
                  ·
                    rfl

theorem cell20_349713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_349713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349713 prefixEnd_349713 := by exact prefixLift 349713
  have htrace : WordTrace (prefixWord ++ tailWord_349713) baseStart_349713 baseEnd_349713 := by
    simpa [prefixWord, tailWord_349713, baseEnd_349713] using wordTrace_append hprefix tailTrace_349713
  have hstable : (prefixWord ++ tailWord_349713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349713).length < 2 ^ (prefixWord ++ tailWord_349713).sum := by decide
  have hdescent : baseEnd_349713 < baseStart_349713 := by decide
  rcases family_descends (prefixWord ++ tailWord_349713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349730 : List Nat := [3, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_349730 : Nat := 118140960795 + 349730 * 2 ^ 59
def prefixEnd_349730 : Nat := 4983230072969 + 3 ^ 40 * 349730 * 2
def baseEnd_349730 : Nat := 159626301597352811970335

theorem tailTrace_349730 : CollatzResearch.WordTrace tailWord_349730 prefixEnd_349730 159626301597352811970335 := by
  unfold tailWord_349730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3188925255748853493457661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8503800681996942649220429 3188925255748853493457661)
  ·
    refine ⟨1195846970905820060046623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3188925255748853493457661 1195846970905820060046623)
    ·
      refine ⟨1793770456358730090069935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195846970905820060046623 1793770456358730090069935)
      ·
        refine ⟨2690655684538095135104903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1793770456358730090069935 2690655684538095135104903)
        ·
          refine ⟨4035983526807142702657355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2690655684538095135104903 4035983526807142702657355)
          ·
            refine ⟨6053975290210714053986033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4035983526807142702657355 6053975290210714053986033)
            ·
              refine ⟨4540481467658035540489525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6053975290210714053986033 4540481467658035540489525)
              ·
                refine ⟨425670137592940831920893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4540481467658035540489525 425670137592940831920893)
                ·
                  refine ⟨159626301597352811970335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425670137592940831920893 159626301597352811970335)
                  ·
                    rfl

theorem cell20_349730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_349730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349730 prefixEnd_349730 := by exact prefixLift 349730
  have htrace : WordTrace (prefixWord ++ tailWord_349730) baseStart_349730 baseEnd_349730 := by
    simpa [prefixWord, tailWord_349730, baseEnd_349730] using wordTrace_append hprefix tailTrace_349730
  have hstable : (prefixWord ++ tailWord_349730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349730).length < 2 ^ (prefixWord ++ tailWord_349730).sum := by decide
  have hdescent : baseEnd_349730 < baseStart_349730 := by decide
  rcases family_descends (prefixWord ++ tailWord_349730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349751 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 5]
def baseStart_349751 : Nat := 118140960795 + 349751 * 2 ^ 59
def prefixEnd_349751 : Nat := 4983230072969 + 3 ^ 40 * 349751 * 2
def baseEnd_349751 : Nat := 159635886569570072270249

theorem tailTrace_349751 : CollatzResearch.WordTrace tailWord_349751 prefixEnd_349751 159635886569570072270249 := by
  unfold tailWord_349751
  simp only [CollatzResearch.WordTrace]
  refine ⟨12756466955919334560345107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8504311303946223040230071 12756466955919334560345107)
  ·
    refine ⟨19134700433879001840517661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12756466955919334560345107 19134700433879001840517661)
    ·
      refine ⟨7175512662704625690194123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19134700433879001840517661 7175512662704625690194123)
      ·
        refine ⟨10763268994056938535291185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7175512662704625690194123 10763268994056938535291185)
        ·
          refine ⟨8072451745542703901468389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10763268994056938535291185 8072451745542703901468389)
          ·
            refine ⟨1513584702289256981525323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8072451745542703901468389 1513584702289256981525323)
            ·
              refine ⟨2270377053433885472287985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1513584702289256981525323 2270377053433885472287985)
              ·
                refine ⟨1702782790075414104215989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2270377053433885472287985 1702782790075414104215989)
                ·
                  refine ⟨159635886569570072270249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1702782790075414104215989 159635886569570072270249)
                  ·
                    rfl

theorem cell20_349751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_349751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349751 prefixEnd_349751 := by exact prefixLift 349751
  have htrace : WordTrace (prefixWord ++ tailWord_349751) baseStart_349751 baseEnd_349751 := by
    simpa [prefixWord, tailWord_349751, baseEnd_349751] using wordTrace_append hprefix tailTrace_349751
  have hstable : (prefixWord ++ tailWord_349751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349751).length < 2 ^ (prefixWord ++ tailWord_349751).sum := by decide
  have hdescent : baseEnd_349751 < baseStart_349751 := by decide
  rcases family_descends (prefixWord ++ tailWord_349751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349841 : List Nat := [1, 2, 2, 1, 1, 1, 1, 11]
def baseStart_349841 : Nat := 118140960795 + 349841 * 2 ^ 59
def prefixEnd_349841 : Nat := 4983230072969 + 3 ^ 40 * 349841 * 2
def baseEnd_349841 : Nat := 53225655007309919756627

theorem tailTrace_349841 : CollatzResearch.WordTrace tailWord_349841 prefixEnd_349841 53225655007309919756627 := by
  unfold tailWord_349841
  simp only [CollatzResearch.WordTrace]
  refine ⟨12759749525593279931121377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8506499683728853287414251 12759749525593279931121377)
  ·
    refine ⟨9569812144194959948341033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12759749525593279931121377 9569812144194959948341033)
    ·
      refine ⟨7177359108146219961255775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9569812144194959948341033 7177359108146219961255775)
      ·
        refine ⟨10766038662219329941883663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7177359108146219961255775 10766038662219329941883663)
        ·
          refine ⟨16149057993328994912825495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10766038662219329941883663 16149057993328994912825495)
          ·
            refine ⟨24223586989993492369238243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16149057993328994912825495 24223586989993492369238243)
            ·
              refine ⟨36335380484990238553857365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24223586989993492369238243 36335380484990238553857365)
              ·
                refine ⟨53225655007309919756627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 36335380484990238553857365 53225655007309919756627)
                ·
                  rfl

theorem cell20_349841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 11].length) (baseStart_349841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349841 prefixEnd_349841 := by exact prefixLift 349841
  have htrace : WordTrace (prefixWord ++ tailWord_349841) baseStart_349841 baseEnd_349841 := by
    simpa [prefixWord, tailWord_349841, baseEnd_349841] using wordTrace_append hprefix tailTrace_349841
  have hstable : (prefixWord ++ tailWord_349841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349841).length < 2 ^ (prefixWord ++ tailWord_349841).sum := by decide
  have hdescent : baseEnd_349841 < baseStart_349841 := by decide
  rcases family_descends (prefixWord ++ tailWord_349841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349854 : List Nat := [4, 3, 1, 1, 1, 3, 3, 4]
def baseStart_349854 : Nat := 118140960795 + 349854 * 2 ^ 59
def prefixEnd_349854 : Nat := 4983230072969 + 3 ^ 40 * 349854 * 2
def baseEnd_349854 : Nat := 53227632858719830612165

theorem tailTrace_349854 : CollatzResearch.WordTrace tailWord_349854 prefixEnd_349854 53227632858719830612165 := by
  unfold tailWord_349854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1595027959318272893918077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8506815783030788767563077 1595027959318272893918077)
  ·
    refine ⟨598135484744352335219279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1595027959318272893918077 598135484744352335219279)
    ·
      refine ⟨897203227116528502828919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598135484744352335219279 897203227116528502828919)
      ·
        refine ⟨1345804840674792754243379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 897203227116528502828919 1345804840674792754243379)
        ·
          refine ⟨2018707261012189131365069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345804840674792754243379 2018707261012189131365069)
          ·
            refine ⟨757015222879570924261901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2018707261012189131365069 757015222879570924261901)
            ·
              refine ⟨283880708579839096598213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 757015222879570924261901 283880708579839096598213)
              ·
                refine ⟨53227632858719830612165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283880708579839096598213 53227632858719830612165)
                ·
                  rfl

theorem cell20_349854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_349854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349854 prefixEnd_349854 := by exact prefixLift 349854
  have htrace : WordTrace (prefixWord ++ tailWord_349854) baseStart_349854 baseEnd_349854 := by
    simpa [prefixWord, tailWord_349854, baseEnd_349854] using wordTrace_append hprefix tailTrace_349854
  have hstable : (prefixWord ++ tailWord_349854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349854).length < 2 ^ (prefixWord ++ tailWord_349854).sum := by decide
  have hdescent : baseEnd_349854 < baseStart_349854 := by decide
  rcases family_descends (prefixWord ++ tailWord_349854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349878 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_349878 : Nat := 118140960795 + 349878 * 2 ^ 59
def prefixEnd_349878 : Nat := 4983230072969 + 3 ^ 40 * 349878 * 2
def baseEnd_349878 : Nat := 159693852830122075036397

theorem tailTrace_349878 : CollatzResearch.WordTrace tailWord_349878 prefixEnd_349878 159693852830122075036397 := by
  unfold tailWord_349878
  simp only [CollatzResearch.WordTrace]
  refine ⟨797568689153702203138643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8507399350972823500145525 797568689153702203138643)
  ·
    refine ⟨1196353033730553304707965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797568689153702203138643 1196353033730553304707965)
    ·
      refine ⟨448632387648957489265487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1196353033730553304707965 448632387648957489265487)
      ·
        refine ⟨672948581473436233898231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448632387648957489265487 672948581473436233898231)
        ·
          refine ⟨1009422872210154350847347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672948581473436233898231 1009422872210154350847347)
          ·
            refine ⟨1514134308315231526271021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009422872210154350847347 1514134308315231526271021)
            ·
              refine ⟨567800365618211822351633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1514134308315231526271021 567800365618211822351633)
              ·
                refine ⟨425850274213658866763725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567800365618211822351633 425850274213658866763725)
                ·
                  refine ⟨159693852830122075036397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425850274213658866763725 159693852830122075036397)
                  ·
                    rfl

theorem cell20_349878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_349878 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349878 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349878 prefixEnd_349878 := by exact prefixLift 349878
  have htrace : WordTrace (prefixWord ++ tailWord_349878) baseStart_349878 baseEnd_349878 := by
    simpa [prefixWord, tailWord_349878, baseEnd_349878] using wordTrace_append hprefix tailTrace_349878
  have hstable : (prefixWord ++ tailWord_349878).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349878).length < 2 ^ (prefixWord ++ tailWord_349878).sum := by decide
  have hdescent : baseEnd_349878 < baseStart_349878 := by decide
  rcases family_descends (prefixWord ++ tailWord_349878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349882 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 3]
def baseStart_349882 : Nat := 118140960795 + 349882 * 2 ^ 59
def prefixEnd_349882 : Nat := 4983230072969 + 3 ^ 40 * 349882 * 2
def baseEnd_349882 : Nat := 159695678539115838903047

theorem tailTrace_349882 : CollatzResearch.WordTrace tailWord_349882 prefixEnd_349882 159695678539115838903047 := by
  unfold tailWord_349882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3190311229611185983340975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8507496612296495955575933 3190311229611185983340975)
  ·
    refine ⟨4785466844416778975011463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3190311229611185983340975 4785466844416778975011463)
    ·
      refine ⟨7178200266625168462517195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4785466844416778975011463 7178200266625168462517195)
      ·
        refine ⟨10767300399937752693775793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7178200266625168462517195 10767300399937752693775793)
        ·
          refine ⟨8075475299953314520331845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10767300399937752693775793 8075475299953314520331845)
          ·
            refine ⟨1514151618741246472562221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8075475299953314520331845 1514151618741246472562221)
            ·
              refine ⟨567806857027967427210833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1514151618741246472562221 567806857027967427210833)
              ·
                refine ⟨425855142770975570408125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567806857027967427210833 425855142770975570408125)
                ·
                  refine ⟨159695678539115838903047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425855142770975570408125 159695678539115838903047)
                  ·
                    rfl

theorem cell20_349882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_349882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349882 prefixEnd_349882 := by exact prefixLift 349882
  have htrace : WordTrace (prefixWord ++ tailWord_349882) baseStart_349882 baseEnd_349882 := by
    simpa [prefixWord, tailWord_349882, baseEnd_349882] using wordTrace_append hprefix tailTrace_349882
  have hstable : (prefixWord ++ tailWord_349882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349882).length < 2 ^ (prefixWord ++ tailWord_349882).sum := by decide
  have hdescent : baseEnd_349882 < baseStart_349882 := by decide
  rcases family_descends (prefixWord ++ tailWord_349882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349903 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 3]
def baseStart_349903 : Nat := 118140960795 + 349903 * 2 ^ 59
def prefixEnd_349903 : Nat := 4983230072969 + 3 ^ 40 * 349903 * 2
def baseEnd_349903 : Nat := 159705263511333099202961

theorem tailTrace_349903 : CollatzResearch.WordTrace tailWord_349903 prefixEnd_349903 159705263511333099202961 := by
  unfold tailWord_349903
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762010851368664519878363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8508007234245776346585575 12762010851368664519878363)
  ·
    refine ⟨19143016277052996779817545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12762010851368664519878363 19143016277052996779817545)
    ·
      refine ⟨14357262207789747584863159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19143016277052996779817545 14357262207789747584863159)
      ·
        refine ⟨21535893311684621377294739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14357262207789747584863159 21535893311684621377294739)
        ·
          refine ⟨32303839967526932065942109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21535893311684621377294739 32303839967526932065942109)
          ·
            refine ⟨12113939987822599524728291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32303839967526932065942109 12113939987822599524728291)
            ·
              refine ⟨18170909981733899287092437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12113939987822599524728291 18170909981733899287092437)
              ·
                refine ⟨425880702696888264541229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 18170909981733899287092437 425880702696888264541229)
                ·
                  refine ⟨159705263511333099202961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425880702696888264541229 159705263511333099202961)
                  ·
                    rfl

theorem cell20_349903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 3].length) (baseStart_349903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349903 prefixEnd_349903 := by exact prefixLift 349903
  have htrace : WordTrace (prefixWord ++ tailWord_349903) baseStart_349903 baseEnd_349903 := by
    simpa [prefixWord, tailWord_349903, baseEnd_349903] using wordTrace_append hprefix tailTrace_349903
  have hstable : (prefixWord ++ tailWord_349903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349903).length < 2 ^ (prefixWord ++ tailWord_349903).sum := by decide
  have hdescent : baseEnd_349903 < baseStart_349903 := by decide
  rcases family_descends (prefixWord ++ tailWord_349903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349913 : List Nat := [1, 2, 1, 2, 3, 5, 2, 4]
def baseStart_349913 : Nat := 118140960795 + 349913 * 2 ^ 59
def prefixEnd_349913 : Nat := 4983230072969 + 3 ^ 40 * 349913 * 2
def baseEnd_349913 : Nat := 53236609261272502956529

theorem tailTrace_349913 : CollatzResearch.WordTrace tailWord_349913 prefixEnd_349913 53236609261272502956529 := by
  unfold tailWord_349913
  simp only [CollatzResearch.WordTrace]
  refine ⟨12762375581332436227742393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8508250387554957485161595 12762375581332436227742393)
  ·
    refine ⟨9571781685999327170806795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12762375581332436227742393 9571781685999327170806795)
    ·
      refine ⟨14357672528998990756210193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9571781685999327170806795 14357672528998990756210193)
      ·
        refine ⟨10768254396749243067157645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14357672528998990756210193 10768254396749243067157645)
        ·
          refine ⟨4038095398780966150184117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10768254396749243067157645 4038095398780966150184117)
          ·
            refine ⟨378571443635715576579761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4038095398780966150184117 378571443635715576579761)
            ·
              refine ⟨283928582726786682434821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378571443635715576579761 283928582726786682434821)
              ·
                refine ⟨53236609261272502956529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283928582726786682434821 53236609261272502956529)
                ·
                  rfl

theorem cell20_349913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 4].length) (baseStart_349913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349913 prefixEnd_349913 := by exact prefixLift 349913
  have htrace : WordTrace (prefixWord ++ tailWord_349913) baseStart_349913 baseEnd_349913 := by
    simpa [prefixWord, tailWord_349913, baseEnd_349913] using wordTrace_append hprefix tailTrace_349913
  have hstable : (prefixWord ++ tailWord_349913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349913).length < 2 ^ (prefixWord ++ tailWord_349913).sum := by decide
  have hdescent : baseEnd_349913 < baseStart_349913 := by decide
  rcases family_descends (prefixWord ++ tailWord_349913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349940 : List Nat := [2, 6, 1, 1, 1, 3, 1, 1, 4]
def baseStart_349940 : Nat := 118140960795 + 349940 * 2 ^ 59
def prefixEnd_349940 : Nat := 4983230072969 + 3 ^ 40 * 349940 * 2
def baseEnd_349940 : Nat := 159722151319525414969477

theorem tailTrace_349940 : CollatzResearch.WordTrace tailWord_349940 prefixEnd_349940 159722151319525414969477 := by
  unfold tailWord_349940
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381680176117309919487637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8508906901489746559316849 6381680176117309919487637)
  ·
    refine ⟨299141258255498902475983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6381680176117309919487637 299141258255498902475983)
    ·
      refine ⟨448711887383248353713975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299141258255498902475983 448711887383248353713975)
      ·
        refine ⟨673067831074872530570963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448711887383248353713975 673067831074872530570963)
        ·
          refine ⟨1009601746612308795856445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673067831074872530570963 1009601746612308795856445)
          ·
            refine ⟨378600654979615798446167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1009601746612308795856445 378600654979615798446167)
            ·
              refine ⟨567900982469423697669251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378600654979615798446167 567900982469423697669251)
              ·
                refine ⟨851851473704135546503877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567900982469423697669251 851851473704135546503877)
                ·
                  refine ⟨159722151319525414969477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 851851473704135546503877 159722151319525414969477)
                  ·
                    rfl

theorem cell20_349940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_349940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349940 prefixEnd_349940 := by exact prefixLift 349940
  have htrace : WordTrace (prefixWord ++ tailWord_349940) baseStart_349940 baseEnd_349940 := by
    simpa [prefixWord, tailWord_349940, baseEnd_349940] using wordTrace_append hprefix tailTrace_349940
  have hstable : (prefixWord ++ tailWord_349940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349940).length < 2 ^ (prefixWord ++ tailWord_349940).sum := by decide
  have hdescent : baseEnd_349940 < baseStart_349940 := by decide
  rcases family_descends (prefixWord ++ tailWord_349940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349955 : List Nat := [1, 1, 1, 3, 2, 2, 3, 7]
def baseStart_349955 : Nat := 118140960795 + 349955 * 2 ^ 59
def prefixEnd_349955 : Nat := 4983230072969 + 3 ^ 40 * 349955 * 2
def baseEnd_349955 : Nat := 53242999242750676489805

theorem tailTrace_349955 : CollatzResearch.WordTrace tailWord_349955 prefixEnd_349955 53242999242750676489805 := by
  unfold tailWord_349955
  simp only [CollatzResearch.WordTrace]
  refine ⟨12763907447180277400771319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8509271631453518267180879 12763907447180277400771319)
  ·
    refine ⟨19145861170770416101156979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12763907447180277400771319 19145861170770416101156979)
    ·
      refine ⟨28718791756155624151735469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19145861170770416101156979 28718791756155624151735469)
      ·
        refine ⟨10769546908558359056900801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28718791756155624151735469 10769546908558359056900801)
        ·
          refine ⟨8077160181418769292675601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10769546908558359056900801 8077160181418769292675601)
          ·
            refine ⟨6057870136064076969506701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8077160181418769292675601 6057870136064076969506701)
            ·
              refine ⟨2271701301024028863565013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6057870136064076969506701 2271701301024028863565013)
              ·
                refine ⟨53242999242750676489805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2271701301024028863565013 53242999242750676489805)
                ·
                  rfl

theorem cell20_349955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_349955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349955 prefixEnd_349955 := by exact prefixLift 349955
  have htrace : WordTrace (prefixWord ++ tailWord_349955) baseStart_349955 baseEnd_349955 := by
    simpa [prefixWord, tailWord_349955, baseEnd_349955] using wordTrace_append hprefix tailTrace_349955
  have hstable : (prefixWord ++ tailWord_349955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349955).length < 2 ^ (prefixWord ++ tailWord_349955).sum := by decide
  have hdescent : baseEnd_349955 < baseStart_349955 := by decide
  rcases family_descends (prefixWord ++ tailWord_349955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349996 : List Nat := [2, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_349996 : Nat := 118140960795 + 349996 * 2 ^ 59
def prefixEnd_349996 : Nat := 4983230072969 + 3 ^ 40 * 349996 * 2
def baseEnd_349996 : Nat := 159747711245438109102581

theorem tailTrace_349996 : CollatzResearch.WordTrace tailWord_349996 prefixEnd_349996 159747711245438109102581 := by
  unfold tailWord_349996
  simp only [CollatzResearch.WordTrace]
  refine ⟨6382701420015870701506921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8510268560021160935342561 6382701420015870701506921)
  ·
    refine ⟨4787026065011903026130191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6382701420015870701506921 4787026065011903026130191)
    ·
      refine ⟨7180539097517854539195287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787026065011903026130191 7180539097517854539195287)
      ·
        refine ⟨10770808646276781808792931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7180539097517854539195287 10770808646276781808792931)
        ·
          refine ⟨16156212969415172713189397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10770808646276781808792931 16156212969415172713189397)
          ·
            refine ⟨757322482941336220930753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16156212969415172713189397 757322482941336220930753)
            ·
              refine ⟨567991862206002165698065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757322482941336220930753 567991862206002165698065)
              ·
                refine ⟨425993896654501624273549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 567991862206002165698065 425993896654501624273549)
                ·
                  refine ⟨159747711245438109102581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425993896654501624273549 159747711245438109102581)
                  ·
                    rfl

theorem cell20_349996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_349996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_349996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_349996 prefixEnd_349996 := by exact prefixLift 349996
  have htrace : WordTrace (prefixWord ++ tailWord_349996) baseStart_349996 baseEnd_349996 := by
    simpa [prefixWord, tailWord_349996, baseEnd_349996] using wordTrace_append hprefix tailTrace_349996
  have hstable : (prefixWord ++ tailWord_349996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349996).length < 2 ^ (prefixWord ++ tailWord_349996).sum := by decide
  have hdescent : baseEnd_349996 < baseStart_349996 := by decide
  rcases family_descends (prefixWord ++ tailWord_349996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350006 : List Nat := [5, 1, 2, 2, 1, 3, 1, 5]
def baseStart_350006 : Nat := 118140960795 + 350006 * 2 ^ 59
def prefixEnd_350006 : Nat := 4983230072969 + 3 ^ 40 * 350006 * 2
def baseEnd_350006 : Nat := 53250758505974172923069

theorem tailTrace_350006 : CollatzResearch.WordTrace tailWord_350006 prefixEnd_350006 53250758505974172923069 := by
  unfold tailWord_350006
  simp only [CollatzResearch.WordTrace]
  refine ⟨797860473124719569429867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8510511713330342073918581 797860473124719569429867)
  ·
    refine ⟨1196790709687079354144801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 797860473124719569429867 1196790709687079354144801)
    ·
      refine ⟨897593032265309515608601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1196790709687079354144801 897593032265309515608601)
      ·
        refine ⟨673194774198982136706451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 897593032265309515608601 673194774198982136706451)
        ·
          refine ⟨1009792161298473205059677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673194774198982136706451 1009792161298473205059677)
          ·
            refine ⟨378672060486927451897379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1009792161298473205059677 378672060486927451897379)
            ·
              refine ⟨568008090730391177846069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378672060486927451897379 568008090730391177846069)
              ·
                refine ⟨53250758505974172923069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568008090730391177846069 53250758505974172923069)
                ·
                  rfl

theorem cell20_350006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_350006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350006 prefixEnd_350006 := by exact prefixLift 350006
  have htrace : WordTrace (prefixWord ++ tailWord_350006) baseStart_350006 baseEnd_350006 := by
    simpa [prefixWord, tailWord_350006, baseEnd_350006] using wordTrace_append hprefix tailTrace_350006
  have hstable : (prefixWord ++ tailWord_350006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350006).length < 2 ^ (prefixWord ++ tailWord_350006).sum := by decide
  have hdescent : baseEnd_350006 < baseStart_350006 := by decide
  rcases family_descends (prefixWord ++ tailWord_350006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350010 : List Nat := [3, 1, 1, 1, 5, 1, 3, 5]
def baseStart_350010 : Nat := 118140960795 + 350010 * 2 ^ 59
def prefixEnd_350010 : Nat := 4983230072969 + 3 ^ 40 * 350010 * 2
def baseEnd_350010 : Nat := 53251367075638760878619

theorem tailTrace_350010 : CollatzResearch.WordTrace tailWord_350010 prefixEnd_350010 53251367075638760878619 := by
  unfold tailWord_350010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191478365495255448505871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8510608974654014529348989 3191478365495255448505871)
  ·
    refine ⟨4787217548242883172758807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3191478365495255448505871 4787217548242883172758807)
    ·
      refine ⟨7180826322364324759138211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787217548242883172758807 7180826322364324759138211)
      ·
        refine ⟨10771239483546487138707317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7180826322364324759138211 10771239483546487138707317)
        ·
          refine ⟨1009803701582483169253811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10771239483546487138707317 1009803701582483169253811)
          ·
            refine ⟨1514705552373724753880717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009803701582483169253811 1514705552373724753880717)
            ·
              refine ⟨568014582140146782705269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1514705552373724753880717 568014582140146782705269)
              ·
                refine ⟨53251367075638760878619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568014582140146782705269 53251367075638760878619)
                ·
                  rfl

theorem cell20_350010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 5].length) (baseStart_350010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350010 prefixEnd_350010 := by exact prefixLift 350010
  have htrace : WordTrace (prefixWord ++ tailWord_350010) baseStart_350010 baseEnd_350010 := by
    simpa [prefixWord, tailWord_350010, baseEnd_350010] using wordTrace_append hprefix tailTrace_350010
  have hstable : (prefixWord ++ tailWord_350010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350010).length < 2 ^ (prefixWord ++ tailWord_350010).sum := by decide
  have hdescent : baseEnd_350010 < baseStart_350010 := by decide
  rcases family_descends (prefixWord ++ tailWord_350010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350024 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 6]
def baseStart_350024 : Nat := 118140960795 + 350024 * 2 ^ 59
def prefixEnd_350024 : Nat := 4983230072969 + 3 ^ 40 * 350024 * 2
def baseEnd_350024 : Nat := 159760491208394456169133

theorem tailTrace_350024 : CollatzResearch.WordTrace tailWord_350024 prefixEnd_350024 159760491208394456169133 := by
  unfold tailWord_350024
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383212041965151092516563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8510949389286868123355417 6383212041965151092516563)
  ·
    refine ⟨9574818062947726638774845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6383212041965151092516563 9574818062947726638774845)
    ·
      refine ⟨3590556773605397489540567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9574818062947726638774845 3590556773605397489540567)
      ·
        refine ⟨5385835160408096234310851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3590556773605397489540567 5385835160408096234310851)
        ·
          refine ⟨8078752740612144351466277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5385835160408096234310851 8078752740612144351466277)
          ·
            refine ⟨1514766138864777065899927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8078752740612144351466277 1514766138864777065899927)
            ·
              refine ⟨2272149208297165598849891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1514766138864777065899927 2272149208297165598849891)
              ·
                refine ⟨3408223812445748398274837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2272149208297165598849891 3408223812445748398274837)
                ·
                  refine ⟨159760491208394456169133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3408223812445748398274837 159760491208394456169133)
                  ·
                    rfl

theorem cell20_350024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 6].length) (baseStart_350024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350024 prefixEnd_350024 := by exact prefixLift 350024
  have htrace : WordTrace (prefixWord ++ tailWord_350024) baseStart_350024 baseEnd_350024 := by
    simpa [prefixWord, tailWord_350024, baseEnd_350024] using wordTrace_append hprefix tailTrace_350024
  have hstable : (prefixWord ++ tailWord_350024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350024).length < 2 ^ (prefixWord ++ tailWord_350024).sum := by decide
  have hdescent : baseEnd_350024 < baseStart_350024 := by decide
  rcases family_descends (prefixWord ++ tailWord_350024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350051 : List Nat := [1, 1, 1, 5, 4, 2, 1, 2, 3]
def baseStart_350051 : Nat := 118140960795 + 350051 * 2 ^ 59
def prefixEnd_350051 : Nat := 4983230072969 + 3 ^ 40 * 350051 * 2
def baseEnd_350051 : Nat := 159772814744102362269023

theorem tailTrace_350051 : CollatzResearch.WordTrace tailWord_350051 prefixEnd_350051 159772814744102362269023 := by
  unfold tailWord_350051
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767408854832485796266007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8511605903221657197510671 12767408854832485796266007)
  ·
    refine ⟨19151113282248728694399011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12767408854832485796266007 19151113282248728694399011)
    ·
      refine ⟨28726669923373093041598517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19151113282248728694399011 28726669923373093041598517)
      ·
        refine ⟨2693125305316227472649861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28726669923373093041598517 2693125305316227472649861)
        ·
          refine ⟨504960994746792651121849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2693125305316227472649861 504960994746792651121849)
          ·
            refine ⟨378720746060094488341387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504960994746792651121849 378720746060094488341387)
            ·
              refine ⟨568081119090141732512081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378720746060094488341387 568081119090141732512081)
              ·
                refine ⟨426060839317606299384061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568081119090141732512081 426060839317606299384061)
                ·
                  refine ⟨159772814744102362269023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426060839317606299384061 159772814744102362269023)
                  ·
                    rfl

theorem cell20_350051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 2, 3].length) (baseStart_350051 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350051 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350051 prefixEnd_350051 := by exact prefixLift 350051
  have htrace : WordTrace (prefixWord ++ tailWord_350051) baseStart_350051 baseEnd_350051 := by
    simpa [prefixWord, tailWord_350051, baseEnd_350051] using wordTrace_append hprefix tailTrace_350051
  have hstable : (prefixWord ++ tailWord_350051).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350051).length < 2 ^ (prefixWord ++ tailWord_350051).sum := by decide
  have hdescent : baseEnd_350051 < baseStart_350051 := by decide
  rcases family_descends (prefixWord ++ tailWord_350051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350055 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 5]
def baseStart_350055 : Nat := 118140960795 + 350055 * 2 ^ 59
def prefixEnd_350055 : Nat := 4983230072969 + 3 ^ 40 * 350055 * 2
def baseEnd_350055 : Nat := 159774640453096126135673

theorem tailTrace_350055 : CollatzResearch.WordTrace tailWord_350055 prefixEnd_350055 159774640453096126135673 := by
  unfold tailWord_350055
  simp only [CollatzResearch.WordTrace]
  refine ⟨12767554746817994479411619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8511703164545329652941079 12767554746817994479411619)
  ·
    refine ⟨19151332120226991719117429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12767554746817994479411619 19151332120226991719117429)
    ·
      refine ⟨1795437386271280473667259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19151332120226991719117429 1795437386271280473667259)
      ·
        refine ⟨2693156079406920710500889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1795437386271280473667259 2693156079406920710500889)
        ·
          refine ⟨2019867059555190532875667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2693156079406920710500889 2019867059555190532875667)
          ·
            refine ⟨3029800589332785799313501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2019867059555190532875667 3029800589332785799313501)
            ·
              refine ⟨1136175220999794674742563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3029800589332785799313501 1136175220999794674742563)
              ·
                refine ⟨1704262831499692012113845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1136175220999794674742563 1704262831499692012113845)
                ·
                  refine ⟨159774640453096126135673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1704262831499692012113845 159774640453096126135673)
                  ·
                    rfl

theorem cell20_350055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_350055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350055 prefixEnd_350055 := by exact prefixLift 350055
  have htrace : WordTrace (prefixWord ++ tailWord_350055) baseStart_350055 baseEnd_350055 := by
    simpa [prefixWord, tailWord_350055, baseEnd_350055] using wordTrace_append hprefix tailTrace_350055
  have hstable : (prefixWord ++ tailWord_350055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350055).length < 2 ^ (prefixWord ++ tailWord_350055).sum := by decide
  have hdescent : baseEnd_350055 < baseStart_350055 := by decide
  rcases family_descends (prefixWord ++ tailWord_350055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350113 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 4]
def baseStart_350113 : Nat := 118140960795 + 350113 * 2 ^ 59
def prefixEnd_350113 : Nat := 4983230072969 + 3 ^ 40 * 350113 * 2
def baseEnd_350113 : Nat := 159801113233505702202103

theorem tailTrace_350113 : CollatzResearch.WordTrace tailWord_350113 prefixEnd_350113 159801113233505702202103 := by
  unfold tailWord_350113
  simp only [CollatzResearch.WordTrace]
  refine ⟨12769670180607870385022993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8513113453738580256681995 12769670180607870385022993)
  ·
    refine ⟨9577252635455902788767245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12769670180607870385022993 9577252635455902788767245)
    ·
      refine ⟨3591469738295963545787717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9577252635455902788767245 3591469738295963545787717)
      ·
        refine ⟨673400575930493164835197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3591469738295963545787717 673400575930493164835197)
        ·
          refine ⟨252525215973934936813199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 673400575930493164835197 252525215973934936813199)
          ·
            refine ⟨378787823960902405219799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252525215973934936813199 378787823960902405219799)
            ·
              refine ⟨568181735941353607829699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378787823960902405219799 568181735941353607829699)
              ·
                refine ⟨852272603912030411744549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568181735941353607829699 852272603912030411744549)
                ·
                  refine ⟨159801113233505702202103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 852272603912030411744549 159801113233505702202103)
                  ·
                    rfl

theorem cell20_350113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_350113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350113 prefixEnd_350113 := by exact prefixLift 350113
  have htrace : WordTrace (prefixWord ++ tailWord_350113) baseStart_350113 baseEnd_350113 := by
    simpa [prefixWord, tailWord_350113, baseEnd_350113] using wordTrace_append hprefix tailTrace_350113
  have hstable : (prefixWord ++ tailWord_350113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350113).length < 2 ^ (prefixWord ++ tailWord_350113).sum := by decide
  have hdescent : baseEnd_350113 < baseStart_350113 := by decide
  rcases family_descends (prefixWord ++ tailWord_350113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350117 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 2]
def baseStart_350117 : Nat := 118140960795 + 350117 * 2 ^ 59
def prefixEnd_350117 : Nat := 4983230072969 + 3 ^ 40 * 350117 * 2
def baseEnd_350117 : Nat := 159802938942499466068753

theorem tailTrace_350117 : CollatzResearch.WordTrace tailWord_350117 prefixEnd_350117 159802938942499466068753 := by
  unfold tailWord_350117
  simp only [CollatzResearch.WordTrace]
  refine ⟨12769816072593379068168605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8513210715062252712112403 12769816072593379068168605)
  ·
    refine ⟨4788681027222517150563227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12769816072593379068168605 4788681027222517150563227)
    ·
      refine ⟨7183021540833775725844841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788681027222517150563227 7183021540833775725844841)
      ·
        refine ⟨5387266155625331794383631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7183021540833775725844841 5387266155625331794383631)
        ·
          refine ⟨8080899233437997691575447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5387266155625331794383631 8080899233437997691575447)
          ·
            refine ⟨12121348850156996537363171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8080899233437997691575447 12121348850156996537363171)
            ·
              refine ⟨18182023275235494806044757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12121348850156996537363171 18182023275235494806044757)
              ·
                refine ⟨213070585256665954758337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 18182023275235494806044757 213070585256665954758337)
                ·
                  refine ⟨159802938942499466068753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213070585256665954758337 159802938942499466068753)
                  ·
                    rfl

theorem cell20_350117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_350117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350117 prefixEnd_350117 := by exact prefixLift 350117
  have htrace : WordTrace (prefixWord ++ tailWord_350117) baseStart_350117 baseEnd_350117 := by
    simpa [prefixWord, tailWord_350117, baseEnd_350117] using wordTrace_append hprefix tailTrace_350117
  have hstable : (prefixWord ++ tailWord_350117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350117).length < 2 ^ (prefixWord ++ tailWord_350117).sum := by decide
  have hdescent : baseEnd_350117 < baseStart_350117 := by decide
  rcases family_descends (prefixWord ++ tailWord_350117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350120 : List Nat := [2, 1, 6, 2, 1, 1, 2, 5]
def baseStart_350120 : Nat := 118140960795 + 350120 * 2 ^ 59
def prefixEnd_350120 : Nat := 4983230072969 + 3 ^ 40 * 350120 * 2
def baseEnd_350120 : Nat := 53268102741414929656247

theorem tailTrace_350120 : CollatzResearch.WordTrace tailWord_350120 prefixEnd_350120 53268102741414929656247 := by
  unfold tailWord_350120
  simp only [CollatzResearch.WordTrace]
  refine ⟨6384962745791255290263907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8513283661055007053685209 6384962745791255290263907)
  ·
    refine ⟨9577444118686882935395861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6384962745791255290263907 9577444118686882935395861)
    ·
      refine ⟨448942693063447637596681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9577444118686882935395861 448942693063447637596681)
      ·
        refine ⟨336707019797585728197511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448942693063447637596681 336707019797585728197511)
        ·
          refine ⟨505060529696378592296267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336707019797585728197511 505060529696378592296267)
          ·
            refine ⟨757590794544567888444401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505060529696378592296267 757590794544567888444401)
            ·
              refine ⟨568193095908425916333301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757590794544567888444401 568193095908425916333301)
              ·
                refine ⟨53268102741414929656247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568193095908425916333301 53268102741414929656247)
                ·
                  rfl

theorem cell20_350120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 5].length) (baseStart_350120 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350120 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350120 prefixEnd_350120 := by exact prefixLift 350120
  have htrace : WordTrace (prefixWord ++ tailWord_350120) baseStart_350120 baseEnd_350120 := by
    simpa [prefixWord, tailWord_350120, baseEnd_350120] using wordTrace_append hprefix tailTrace_350120
  have hstable : (prefixWord ++ tailWord_350120).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350120).length < 2 ^ (prefixWord ++ tailWord_350120).sum := by decide
  have hdescent : baseEnd_350120 < baseStart_350120 := by decide
  rcases family_descends (prefixWord ++ tailWord_350120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350131 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 3]
def baseStart_350131 : Nat := 118140960795 + 350131 * 2 ^ 59
def prefixEnd_350131 : Nat := 4983230072969 + 3 ^ 40 * 350131 * 2
def baseEnd_350131 : Nat := 159809328923977639602029

theorem tailTrace_350131 : CollatzResearch.WordTrace tailWord_350131 prefixEnd_350131 159809328923977639602029 := by
  unfold tailWord_350131
  simp only [CollatzResearch.WordTrace]
  refine ⟨12770326694542659459178247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8513551129695106306118831 12770326694542659459178247)
  ·
    refine ⟨19155490041813989188767371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12770326694542659459178247 19155490041813989188767371)
    ·
      refine ⟨28733235062720983783151057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19155490041813989188767371 28733235062720983783151057)
      ·
        refine ⟨21549926297040737837363293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28733235062720983783151057 21549926297040737837363293)
        ·
          refine ⟨8081222361390276689011235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21549926297040737837363293 8081222361390276689011235)
          ·
            refine ⟨12121833542085415033516853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8081222361390276689011235 12121833542085415033516853)
            ·
              refine ⟨1136421894570507659392205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12121833542085415033516853 1136421894570507659392205)
              ·
                refine ⟨426158210463940372272077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1136421894570507659392205 426158210463940372272077)
                ·
                  refine ⟨159809328923977639602029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426158210463940372272077 159809328923977639602029)
                  ·
                    rfl

theorem cell20_350131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_350131 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350131 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350131 prefixEnd_350131 := by exact prefixLift 350131
  have htrace : WordTrace (prefixWord ++ tailWord_350131) baseStart_350131 baseEnd_350131 := by
    simpa [prefixWord, tailWord_350131, baseEnd_350131] using wordTrace_append hprefix tailTrace_350131
  have hstable : (prefixWord ++ tailWord_350131).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350131).length < 2 ^ (prefixWord ++ tailWord_350131).sum := by decide
  have hdescent : baseEnd_350131 < baseStart_350131 := by decide
  rcases family_descends (prefixWord ++ tailWord_350131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350155 : List Nat := [1, 1, 1, 1, 3, 4, 2, 5, 2]
def baseStart_350155 : Nat := 118140960795 + 350155 * 2 ^ 59
def prefixEnd_350155 : Nat := 4983230072969 + 3 ^ 40 * 350155 * 2
def baseEnd_350155 : Nat := 159820283177940222801931

theorem tailTrace_350155 : CollatzResearch.WordTrace tailWord_350155 prefixEnd_350155 159820283177940222801931 := by
  unfold tailWord_350155
  simp only [CollatzResearch.WordTrace]
  refine ⟨12771202046455711558051919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8514134697637141038701279 12771202046455711558051919)
  ·
    refine ⟨19156803069683567337077879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12771202046455711558051919 19156803069683567337077879)
    ·
      refine ⟨28735204604525351005616819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19156803069683567337077879 28735204604525351005616819)
      ·
        refine ⟨43102806906788026508425229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28735204604525351005616819 43102806906788026508425229)
        ·
          refine ⟨16163552590045509940659461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43102806906788026508425229 16163552590045509940659461)
          ·
            refine ⟨3030666110633533113873649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16163552590045509940659461 3030666110633533113873649)
            ·
              refine ⟨2272999582975149835405237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3030666110633533113873649 2272999582975149835405237)
              ·
                refine ⟨213093710903920297069241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2272999582975149835405237 213093710903920297069241)
                ·
                  refine ⟨159820283177940222801931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213093710903920297069241 159820283177940222801931)
                  ·
                    rfl

theorem cell20_350155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 5, 2].length) (baseStart_350155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350155 prefixEnd_350155 := by exact prefixLift 350155
  have htrace : WordTrace (prefixWord ++ tailWord_350155) baseStart_350155 baseEnd_350155 := by
    simpa [prefixWord, tailWord_350155, baseEnd_350155] using wordTrace_append hprefix tailTrace_350155
  have hstable : (prefixWord ++ tailWord_350155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350155).length < 2 ^ (prefixWord ++ tailWord_350155).sum := by decide
  have hdescent : baseEnd_350155 < baseStart_350155 := by decide
  rcases family_descends (prefixWord ++ tailWord_350155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350162 : List Nat := [3, 2, 2, 3, 2, 8]
def baseStart_350162 : Nat := 118140960795 + 350162 * 2 ^ 59
def prefixEnd_350162 : Nat := 4983230072969 + 3 ^ 40 * 350162 * 2
def baseEnd_350162 : Nat := 5919388080321455909947

theorem tailTrace_350162 : CollatzResearch.WordTrace tailWord_350162 prefixEnd_350162 5919388080321455909947 := by
  unfold tailWord_350162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192864339357587938389185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8514304904953567835704493 3192864339357587938389185)
  ·
    refine ⟨2394648254518190953791889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3192864339357587938389185 2394648254518190953791889)
    ·
      refine ⟨1795986190888643215343917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2394648254518190953791889 1795986190888643215343917)
      ·
        refine ⟨673494821583241205753969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1795986190888643215343917 673494821583241205753969)
        ·
          refine ⟨505121116187430904315477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 673494821583241205753969 505121116187430904315477)
          ·
            refine ⟨5919388080321455909947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 505121116187430904315477 5919388080321455909947)
            ·
              rfl

theorem cell20_350162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 8].length) (baseStart_350162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350162 prefixEnd_350162 := by exact prefixLift 350162
  have htrace : WordTrace (prefixWord ++ tailWord_350162) baseStart_350162 baseEnd_350162 := by
    simpa [prefixWord, tailWord_350162, baseEnd_350162] using wordTrace_append hprefix tailTrace_350162
  have hstable : (prefixWord ++ tailWord_350162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350162).length < 2 ^ (prefixWord ++ tailWord_350162).sum := by decide
  have hdescent : baseEnd_350162 < baseStart_350162 := by decide
  rcases family_descends (prefixWord ++ tailWord_350162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350193 : List Nat := [1, 2, 2, 2, 5, 1, 1, 2, 4]
def baseStart_350193 : Nat := 118140960795 + 350193 * 2 ^ 59
def prefixEnd_350193 : Nat := 4983230072969 + 3 ^ 40 * 350193 * 2
def baseEnd_350193 : Nat := 159837627413380979535109

theorem tailTrace_350193 : CollatzResearch.WordTrace tailWord_350193 prefixEnd_350193 159837627413380979535109 := by
  unfold tailWord_350193
  simp only [CollatzResearch.WordTrace]
  refine ⟨12772588020318044047935233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8515058680212029365290155 12772588020318044047935233)
  ·
    refine ⟨9579441015238533035951425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12772588020318044047935233 9579441015238533035951425)
    ·
      refine ⟨7184580761428899776963569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9579441015238533035951425 7184580761428899776963569)
      ·
        refine ⟨5388435571071674832722677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7184580761428899776963569 5388435571071674832722677)
        ·
          refine ⟨505165834787969515567751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5388435571071674832722677 505165834787969515567751)
          ·
            refine ⟨757748752181954273351627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505165834787969515567751 757748752181954273351627)
            ·
              refine ⟨1136623128272931410027441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757748752181954273351627 1136623128272931410027441)
              ·
                refine ⟨852467346204698557520581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1136623128272931410027441 852467346204698557520581)
                ·
                  refine ⟨159837627413380979535109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 852467346204698557520581 159837627413380979535109)
                  ·
                    rfl

theorem cell20_350193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_350193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350193 prefixEnd_350193 := by exact prefixLift 350193
  have htrace : WordTrace (prefixWord ++ tailWord_350193) baseStart_350193 baseEnd_350193 := by
    simpa [prefixWord, tailWord_350193, baseEnd_350193] using wordTrace_append hprefix tailTrace_350193
  have hstable : (prefixWord ++ tailWord_350193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350193).length < 2 ^ (prefixWord ++ tailWord_350193).sum := by decide
  have hdescent : baseEnd_350193 < baseStart_350193 := by decide
  rcases family_descends (prefixWord ++ tailWord_350193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350241 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 3]
def baseStart_350241 : Nat := 118140960795 + 350241 * 2 ^ 59
def prefixEnd_350241 : Nat := 4983230072969 + 3 ^ 40 * 350241 * 2
def baseEnd_350241 : Nat := 159859535921306145934913

theorem tailTrace_350241 : CollatzResearch.WordTrace tailWord_350241 prefixEnd_350241 159859535921306145934913 := by
  unfold tailWord_350241
  simp only [CollatzResearch.WordTrace]
  refine ⟨12774338724144148245682577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8516225816096098830455051 12774338724144148245682577)
  ·
    refine ⟨9580754043108111184261933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12774338724144148245682577 9580754043108111184261933)
    ·
      refine ⟨3592782766165541694098225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9580754043108111184261933 3592782766165541694098225)
      ·
        refine ⟨2694587074624156270573669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3592782766165541694098225 2694587074624156270573669)
        ·
          refine ⟨505235076492029300732563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2694587074624156270573669 505235076492029300732563)
          ·
            refine ⟨757852614738043951098845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505235076492029300732563 757852614738043951098845)
            ·
              refine ⟨284194730526766481662067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 757852614738043951098845 284194730526766481662067)
              ·
                refine ⟨426292095790149722493101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284194730526766481662067 426292095790149722493101)
                ·
                  refine ⟨159859535921306145934913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426292095790149722493101 159859535921306145934913)
                  ·
                    rfl

theorem cell20_350241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_350241 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350241 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350241 prefixEnd_350241 := by exact prefixLift 350241
  have htrace : WordTrace (prefixWord ++ tailWord_350241) baseStart_350241 baseEnd_350241 := by
    simpa [prefixWord, tailWord_350241, baseEnd_350241] using wordTrace_append hprefix tailTrace_350241
  have hstable : (prefixWord ++ tailWord_350241).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350241).length < 2 ^ (prefixWord ++ tailWord_350241).sum := by decide
  have hdescent : baseEnd_350241 < baseStart_350241 := by decide
  rcases family_descends (prefixWord ++ tailWord_350241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350265 : List Nat := [1, 2, 1, 5, 3, 2, 1, 3, 2]
def baseStart_350265 : Nat := 118140960795 + 350265 * 2 ^ 59
def prefixEnd_350265 : Nat := 4983230072969 + 3 ^ 40 * 350265 * 2
def baseEnd_350265 : Nat := 159870490175268729134815

theorem tailTrace_350265 : CollatzResearch.WordTrace tailWord_350265 prefixEnd_350265 159870490175268729134815 := by
  unfold tailWord_350265
  simp only [CollatzResearch.WordTrace]
  refine ⟨12775214076057200344556249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8516809384038133563037499 12775214076057200344556249)
  ·
    refine ⟨9581410557042900258417187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12775214076057200344556249 9581410557042900258417187)
    ·
      refine ⟨14372115835564350387625781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9581410557042900258417187 14372115835564350387625781)
      ·
        refine ⟨1347385859584157848839917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14372115835564350387625781 1347385859584157848839917)
        ·
          refine ⟨505269697344059193314969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1347385859584157848839917 505269697344059193314969)
          ·
            refine ⟨378952273008044394986227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505269697344059193314969 378952273008044394986227)
            ·
              refine ⟨568428409512066592479341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378952273008044394986227 568428409512066592479341)
              ·
                refine ⟨213160653567024972179753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568428409512066592479341 213160653567024972179753)
                ·
                  refine ⟨159870490175268729134815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213160653567024972179753 159870490175268729134815)
                  ·
                    rfl

theorem cell20_350265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_350265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350265 prefixEnd_350265 := by exact prefixLift 350265
  have htrace : WordTrace (prefixWord ++ tailWord_350265) baseStart_350265 baseEnd_350265 := by
    simpa [prefixWord, tailWord_350265, baseEnd_350265] using wordTrace_append hprefix tailTrace_350265
  have hstable : (prefixWord ++ tailWord_350265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350265).length < 2 ^ (prefixWord ++ tailWord_350265).sum := by decide
  have hdescent : baseEnd_350265 < baseStart_350265 := by decide
  rcases family_descends (prefixWord ++ tailWord_350265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350297 : List Nat := [1, 2, 1, 2, 2, 1, 6, 5]
def baseStart_350297 : Nat := 118140960795 + 350297 * 2 ^ 59
def prefixEnd_350297 : Nat := 4983230072969 + 3 ^ 40 * 350297 * 2
def baseEnd_350297 : Nat := 53295031949072946689339

theorem tailTrace_350297 : CollatzResearch.WordTrace tailWord_350297 prefixEnd_350297 53295031949072946689339 := by
  unfold tailWord_350297
  simp only [CollatzResearch.WordTrace]
  refine ⟨12776381211941269809721145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8517587474627513206480763 12776381211941269809721145)
  ·
    refine ⟨9582285908955952357290859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12776381211941269809721145 9582285908955952357290859)
    ·
      refine ⟨14373428863433928535936289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9582285908955952357290859 14373428863433928535936289)
      ·
        refine ⟨10780071647575446401952217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14373428863433928535936289 10780071647575446401952217)
        ·
          refine ⟨8085053735681584801464163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10780071647575446401952217 8085053735681584801464163)
          ·
            refine ⟨12127580603522377202196245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8085053735681584801464163 12127580603522377202196245)
            ·
              refine ⟨568480340790111431352949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12127580603522377202196245 568480340790111431352949)
              ·
                refine ⟨53295031949072946689339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 568480340790111431352949 53295031949072946689339)
                ·
                  rfl

theorem cell20_350297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_350297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350297 prefixEnd_350297 := by exact prefixLift 350297
  have htrace : WordTrace (prefixWord ++ tailWord_350297) baseStart_350297 baseEnd_350297 := by
    simpa [prefixWord, tailWord_350297, baseEnd_350297] using wordTrace_append hprefix tailTrace_350297
  have hstable : (prefixWord ++ tailWord_350297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350297).length < 2 ^ (prefixWord ++ tailWord_350297).sum := by decide
  have hdescent : baseEnd_350297 < baseStart_350297 := by decide
  rcases family_descends (prefixWord ++ tailWord_350297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350300 : List Nat := [2, 2, 4, 1, 1, 3, 1, 3, 3]
def baseStart_350300 : Nat := 118140960795 + 350300 * 2 ^ 59
def prefixEnd_350300 : Nat := 4983230072969 + 3 ^ 40 * 350300 * 2
def baseEnd_350300 : Nat := 159886465128964162968005

theorem tailTrace_350300 : CollatzResearch.WordTrace tailWord_350300 prefixEnd_350300 159886465128964162968005 := by
  unfold tailWord_350300
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388245315465200661040177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8517660420620267548053569 6388245315465200661040177)
  ·
    refine ⟨4791183986598900495780133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6388245315465200661040177 4791183986598900495780133)
    ·
      refine ⟨898346997487293842958775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4791183986598900495780133 898346997487293842958775)
      ·
        refine ⟨1347520496230940764438163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898346997487293842958775 1347520496230940764438163)
        ·
          refine ⟨2021280744346411146657245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1347520496230940764438163 2021280744346411146657245)
          ·
            refine ⟨757980279129904179996467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2021280744346411146657245 757980279129904179996467)
            ·
              refine ⟨1136970418694856269994701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757980279129904179996467 1136970418694856269994701)
              ·
                refine ⟨426363907010571101248013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1136970418694856269994701 426363907010571101248013)
                ·
                  refine ⟨159886465128964162968005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426363907010571101248013 159886465128964162968005)
                  ·
                    rfl

theorem cell20_350300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_350300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350300 prefixEnd_350300 := by exact prefixLift 350300
  have htrace : WordTrace (prefixWord ++ tailWord_350300) baseStart_350300 baseEnd_350300 := by
    simpa [prefixWord, tailWord_350300, baseEnd_350300] using wordTrace_append hprefix tailTrace_350300
  have hstable : (prefixWord ++ tailWord_350300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350300).length < 2 ^ (prefixWord ++ tailWord_350300).sum := by decide
  have hdescent : baseEnd_350300 < baseStart_350300 := by decide
  rcases family_descends (prefixWord ++ tailWord_350300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350341 : List Nat := [1, 3, 1, 1, 5, 3, 2, 2, 2]
def baseStart_350341 : Nat := 118140960795 + 350341 * 2 ^ 59
def prefixEnd_350341 : Nat := 4983230072969 + 3 ^ 40 * 350341 * 2
def baseEnd_350341 : Nat := 159905178646150242601171

theorem tailTrace_350341 : CollatzResearch.WordTrace tailWord_350341 prefixEnd_350341 159905178646150242601171 := by
  unfold tailWord_350341
  simp only [CollatzResearch.WordTrace]
  refine ⟨12777986023781865324322877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8518657349187910216215251 12777986023781865324322877)
  ·
    refine ⟨4791744758918199496621079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12777986023781865324322877 4791744758918199496621079)
    ·
      refine ⟨7187617138377299244931619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791744758918199496621079 7187617138377299244931619)
      ·
        refine ⟨10781425707565948867397429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187617138377299244931619 10781425707565948867397429)
        ·
          refine ⟨1010758660084307706318509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10781425707565948867397429 1010758660084307706318509)
          ·
            refine ⟨379034497531615389869441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1010758660084307706318509 379034497531615389869441)
            ·
              refine ⟨284275873148711542402081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379034497531615389869441 284275873148711542402081)
              ·
                refine ⟨213206904861533656801561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284275873148711542402081 213206904861533656801561)
                ·
                  refine ⟨159905178646150242601171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213206904861533656801561 159905178646150242601171)
                  ·
                    rfl

theorem cell20_350341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 2, 2].length) (baseStart_350341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350341 prefixEnd_350341 := by exact prefixLift 350341
  have htrace : WordTrace (prefixWord ++ tailWord_350341) baseStart_350341 baseEnd_350341 := by
    simpa [prefixWord, tailWord_350341, baseEnd_350341] using wordTrace_append hprefix tailTrace_350341
  have hstable : (prefixWord ++ tailWord_350341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350341).length < 2 ^ (prefixWord ++ tailWord_350341).sum := by decide
  have hdescent : baseEnd_350341 < baseStart_350341 := by decide
  rcases family_descends (prefixWord ++ tailWord_350341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350345 : List Nat := [1, 2, 1, 1, 4, 2, 3, 4, 2]
def baseStart_350345 : Nat := 118140960795 + 350345 * 2 ^ 59
def prefixEnd_350345 : Nat := 4983230072969 + 3 ^ 40 * 350345 * 2
def baseEnd_350345 : Nat := 159907004355144006467821

theorem tailTrace_350345 : CollatzResearch.WordTrace tailWord_350345 prefixEnd_350345 159907004355144006467821 := by
  unfold tailWord_350345
  simp only [CollatzResearch.WordTrace]
  refine ⟨12778131915767374007468489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8518754610511582671645659 12778131915767374007468489)
  ·
    refine ⟨9583598936825530505601367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12778131915767374007468489 9583598936825530505601367)
    ·
      refine ⟨14375398405238295758402051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9583598936825530505601367 14375398405238295758402051)
      ·
        refine ⟨21563097607857443637603077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14375398405238295758402051 21563097607857443637603077)
        ·
          refine ⟨4043080801473270682050577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21563097607857443637603077 4043080801473270682050577)
          ·
            refine ⟨3032310601104953011537933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4043080801473270682050577 3032310601104953011537933)
            ·
              refine ⟨1137116475414357379326725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3032310601104953011537933 1137116475414357379326725)
              ·
                refine ⟨213209339140192008623761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1137116475414357379326725 213209339140192008623761)
                ·
                  refine ⟨159907004355144006467821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213209339140192008623761 159907004355144006467821)
                  ·
                    rfl

theorem cell20_350345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 4, 2].length) (baseStart_350345 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350345 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350345 prefixEnd_350345 := by exact prefixLift 350345
  have htrace : WordTrace (prefixWord ++ tailWord_350345) baseStart_350345 baseEnd_350345 := by
    simpa [prefixWord, tailWord_350345, baseEnd_350345] using wordTrace_append hprefix tailTrace_350345
  have hstable : (prefixWord ++ tailWord_350345).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350345).length < 2 ^ (prefixWord ++ tailWord_350345).sum := by decide
  have hdescent : baseEnd_350345 < baseStart_350345 := by decide
  rcases family_descends (prefixWord ++ tailWord_350345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350387 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_350387 : Nat := 118140960795 + 350387 * 2 ^ 59
def prefixEnd_350387 : Nat := 4983230072969 + 3 ^ 40 * 350387 * 2
def baseEnd_350387 : Nat := 159926174299578527067649

theorem tailTrace_350387 : CollatzResearch.WordTrace tailWord_350387 prefixEnd_350387 159926174299578527067649 := by
  unfold tailWord_350387
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779663781615215180497415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8519775854410143453664943 12779663781615215180497415)
  ·
    refine ⟨19169495672422822770746123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12779663781615215180497415 19169495672422822770746123)
    ·
      refine ⟨28754243508634234156119185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19169495672422822770746123 28754243508634234156119185)
      ·
        refine ⟨21565682631475675617089389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28754243508634234156119185 21565682631475675617089389)
        ·
          refine ⟨8087130986803378356408521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21565682631475675617089389 8087130986803378356408521)
          ·
            refine ⟨6065348240102533767306391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8087130986803378356408521 6065348240102533767306391)
            ·
              refine ⟨9098022360153800650959587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6065348240102533767306391 9098022360153800650959587)
              ·
                refine ⟨13647033540230700976439381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9098022360153800650959587 13647033540230700976439381)
                ·
                  refine ⟨159926174299578527067649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13647033540230700976439381 159926174299578527067649)
                  ·
                    rfl

theorem cell20_350387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_350387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350387 prefixEnd_350387 := by exact prefixLift 350387
  have htrace : WordTrace (prefixWord ++ tailWord_350387) baseStart_350387 baseEnd_350387 := by
    simpa [prefixWord, tailWord_350387, baseEnd_350387] using wordTrace_append hprefix tailTrace_350387
  have hstable : (prefixWord ++ tailWord_350387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350387).length < 2 ^ (prefixWord ++ tailWord_350387).sum := by decide
  have hdescent : baseEnd_350387 < baseStart_350387 := by decide
  rcases family_descends (prefixWord ++ tailWord_350387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350445 : List Nat := [1, 5, 1, 2, 4, 1, 6]
def baseStart_350445 : Nat := 118140960795 + 350445 * 2 ^ 59
def prefixEnd_350445 : Nat := 4983230072969 + 3 ^ 40 * 350445 * 2
def baseEnd_350445 : Nat := 17772516342220900348231

theorem tailTrace_350445 : CollatzResearch.WordTrace tailWord_350445 prefixEnd_350445 17772516342220900348231 := by
  unfold tailWord_350445
  simp only [CollatzResearch.WordTrace]
  refine ⟨12781779215405091086108789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8521186143603394057405859 12781779215405091086108789)
  ·
    refine ⟨1198291801444227289322699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12781779215405091086108789 1198291801444227289322699)
    ·
      refine ⟨1797437702166340933984049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198291801444227289322699 1797437702166340933984049)
      ·
        refine ⟨1348078276624755700488037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1797437702166340933984049 1348078276624755700488037)
        ·
          refine ⟨252764676867141693841507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1348078276624755700488037 252764676867141693841507)
          ·
            refine ⟨379147015300712540762261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252764676867141693841507 379147015300712540762261)
            ·
              refine ⟨17772516342220900348231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 379147015300712540762261 17772516342220900348231)
              ·
                rfl

theorem cell20_350445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 6].length) (baseStart_350445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350445 prefixEnd_350445 := by exact prefixLift 350445
  have htrace : WordTrace (prefixWord ++ tailWord_350445) baseStart_350445 baseEnd_350445 := by
    simpa [prefixWord, tailWord_350445, baseEnd_350445] using wordTrace_append hprefix tailTrace_350445
  have hstable : (prefixWord ++ tailWord_350445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350445).length < 2 ^ (prefixWord ++ tailWord_350445).sum := by decide
  have hdescent : baseEnd_350445 < baseStart_350445 := by decide
  rcases family_descends (prefixWord ++ tailWord_350445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350466 : List Nat := [3, 4, 1, 1, 2, 1, 1, 7]
def baseStart_350466 : Nat := 118140960795 + 350466 * 2 ^ 59
def prefixEnd_350466 : Nat := 4983230072969 + 3 ^ 40 * 350466 * 2
def baseEnd_350466 : Nat := 53320744017401787811331

theorem tailTrace_350466 : CollatzResearch.WordTrace tailWord_350466 prefixEnd_350466 53320744017401787811331 := by
  unfold tailWord_350466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3195636287082252918155813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8521696765552674448415501 3195636287082252918155813)
  ·
    refine ⟨599181803827922422154215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3195636287082252918155813 599181803827922422154215)
    ·
      refine ⟨898772705741883633231323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599181803827922422154215 898772705741883633231323)
      ·
        refine ⟨1348159058612825449846985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898772705741883633231323 1348159058612825449846985)
        ·
          refine ⟨1011119293959619087385239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348159058612825449846985 1011119293959619087385239)
          ·
            refine ⟨1516678940939428631077859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011119293959619087385239 1516678940939428631077859)
            ·
              refine ⟨2275018411409142946616789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516678940939428631077859 2275018411409142946616789)
              ·
                refine ⟨53320744017401787811331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2275018411409142946616789 53320744017401787811331)
                ·
                  rfl

theorem cell20_350466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_350466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350466 prefixEnd_350466 := by exact prefixLift 350466
  have htrace : WordTrace (prefixWord ++ tailWord_350466) baseStart_350466 baseEnd_350466 := by
    simpa [prefixWord, tailWord_350466, baseEnd_350466] using wordTrace_append hprefix tailTrace_350466
  have hstable : (prefixWord ++ tailWord_350466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350466).length < 2 ^ (prefixWord ++ tailWord_350466).sum := by decide
  have hdescent : baseEnd_350466 < baseStart_350466 := by decide
  rcases family_descends (prefixWord ++ tailWord_350466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350473 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 3]
def baseStart_350473 : Nat := 118140960795 + 350473 * 2 ^ 59
def prefixEnd_350473 : Nat := 4983230072969 + 3 ^ 40 * 350473 * 2
def baseEnd_350473 : Nat := 159965427042944450200631

theorem tailTrace_350473 : CollatzResearch.WordTrace tailWord_350473 prefixEnd_350473 159965427042944450200631 := by
  unfold tailWord_350473
  simp only [CollatzResearch.WordTrace]
  refine ⟨12782800459303651868128073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8521866972869101245418715 12782800459303651868128073)
  ·
    refine ⟨9587100344477738901096055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12782800459303651868128073 9587100344477738901096055)
    ·
      refine ⟨14380650516716608351644083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9587100344477738901096055 14380650516716608351644083)
      ·
        refine ⟨21570975775074912527466125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14380650516716608351644083 21570975775074912527466125)
        ·
          refine ⟨8089115915653092197799797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21570975775074912527466125 8089115915653092197799797)
          ·
            refine ⟨758354617092477393543731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8089115915653092197799797 758354617092477393543731)
            ·
              refine ⟨1137531925638716090315597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758354617092477393543731 1137531925638716090315597)
              ·
                refine ⟨426574472114518533868349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1137531925638716090315597 426574472114518533868349)
                ·
                  refine ⟨159965427042944450200631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426574472114518533868349 159965427042944450200631)
                  ·
                    rfl

theorem cell20_350473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_350473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350473 prefixEnd_350473 := by exact prefixLift 350473
  have htrace : WordTrace (prefixWord ++ tailWord_350473) baseStart_350473 baseEnd_350473 := by
    simpa [prefixWord, tailWord_350473, baseEnd_350473] using wordTrace_append hprefix tailTrace_350473
  have hstable : (prefixWord ++ tailWord_350473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350473).length < 2 ^ (prefixWord ++ tailWord_350473).sum := by decide
  have hdescent : baseEnd_350473 < baseStart_350473 := by decide
  rcases family_descends (prefixWord ++ tailWord_350473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350487 : List Nat := [1, 1, 3, 4, 1, 2, 2, 6]
def baseStart_350487 : Nat := 118140960795 + 350487 * 2 ^ 59
def prefixEnd_350487 : Nat := 4983230072969 + 3 ^ 40 * 350487 * 2
def baseEnd_350487 : Nat := 53323939008140874577969

theorem tailTrace_350487 : CollatzResearch.WordTrace tailWord_350487 prefixEnd_350487 53323939008140874577969 := by
  unfold tailWord_350487
  simp only [CollatzResearch.WordTrace]
  refine ⟨12783311081252932259137715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8522207387501954839425143 12783311081252932259137715)
  ·
    refine ⟨19174966621879398388706573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12783311081252932259137715 19174966621879398388706573)
    ·
      refine ⟨7190612483204774395764965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19174966621879398388706573 7190612483204774395764965)
      ·
        refine ⟨1348239840600895199205931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7190612483204774395764965 1348239840600895199205931)
        ·
          refine ⟨2022359760901342798808897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1348239840600895199205931 2022359760901342798808897)
          ·
            refine ⟨1516769820676007099106673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2022359760901342798808897 1516769820676007099106673)
            ·
              refine ⟨1137577365507005324330005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516769820676007099106673 1137577365507005324330005)
              ·
                refine ⟨53323939008140874577969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1137577365507005324330005 53323939008140874577969)
                ·
                  rfl

theorem cell20_350487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 6].length) (baseStart_350487 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350487 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350487 prefixEnd_350487 := by exact prefixLift 350487
  have htrace : WordTrace (prefixWord ++ tailWord_350487) baseStart_350487 baseEnd_350487 := by
    simpa [prefixWord, tailWord_350487, baseEnd_350487] using wordTrace_append hprefix tailTrace_350487
  have hstable : (prefixWord ++ tailWord_350487).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350487).length < 2 ^ (prefixWord ++ tailWord_350487).sum := by decide
  have hdescent : baseEnd_350487 < baseStart_350487 := by decide
  rcases family_descends (prefixWord ++ tailWord_350487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350504 : List Nat := [2, 1, 5, 1, 4, 7]
def baseStart_350504 : Nat := 118140960795 + 350504 * 2 ^ 59
def prefixEnd_350504 : Nat := 4983230072969 + 3 ^ 40 * 350504 * 2
def baseEnd_350504 : Nat := 5925169492135041487673

theorem tailTrace_350504 : CollatzResearch.WordTrace tailWord_350504 prefixEnd_350504 5925169492135041487673 := by
  unfold tailWord_350504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6391965561095672081253283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8522620748127562775004377 6391965561095672081253283)
  ·
    refine ⟨9587948341643508121879925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6391965561095672081253283 9587948341643508121879925)
    ·
      refine ⟨898870157029078886426243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9587948341643508121879925 898870157029078886426243)
      ·
        refine ⟨1348305235543618329639365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898870157029078886426243 1348305235543618329639365)
        ·
          refine ⟨252807231664428436807381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1348305235543618329639365 252807231664428436807381)
          ·
            refine ⟨5925169492135041487673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 252807231664428436807381 5925169492135041487673)
            ·
              rfl

theorem cell20_350504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 7].length) (baseStart_350504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350504 prefixEnd_350504 := by exact prefixLift 350504
  have htrace : WordTrace (prefixWord ++ tailWord_350504) baseStart_350504 baseEnd_350504 := by
    simpa [prefixWord, tailWord_350504, baseEnd_350504] using wordTrace_append hprefix tailTrace_350504
  have hstable : (prefixWord ++ tailWord_350504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350504).length < 2 ^ (prefixWord ++ tailWord_350504).sum := by decide
  have hdescent : baseEnd_350504 < baseStart_350504 := by decide
  rcases family_descends (prefixWord ++ tailWord_350504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350514 : List Nat := [3, 2, 1, 1, 5, 1, 1, 4, 2]
def baseStart_350514 : Nat := 118140960795 + 350514 * 2 ^ 59
def prefixEnd_350514 : Nat := 4983230072969 + 3 ^ 40 * 350514 * 2
def baseEnd_350514 : Nat := 159984140560130529833797

theorem tailTrace_350514 : CollatzResearch.WordTrace tailWord_350514 prefixEnd_350514 159984140560130529833797 := by
  unfold tailWord_350514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196073963038778967592649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8522863901436743913580397 3196073963038778967592649)
  ·
    refine ⟨2397055472279084225694487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3196073963038778967592649 2397055472279084225694487)
    ·
      refine ⟨3595583208418626338541731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397055472279084225694487 3595583208418626338541731)
      ·
        refine ⟨5393374812627939507812597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3595583208418626338541731 5393374812627939507812597)
        ·
          refine ⟨505628888683869328857431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5393374812627939507812597 505628888683869328857431)
          ·
            refine ⟨758443333025803993286147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505628888683869328857431 758443333025803993286147)
            ·
              refine ⟨1137664999538705989929221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758443333025803993286147 1137664999538705989929221)
              ·
                refine ⟨213312187413507373111729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1137664999538705989929221 213312187413507373111729)
                ·
                  refine ⟨159984140560130529833797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213312187413507373111729 159984140560130529833797)
                  ·
                    rfl

theorem cell20_350514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_350514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350514 prefixEnd_350514 := by exact prefixLift 350514
  have htrace : WordTrace (prefixWord ++ tailWord_350514) baseStart_350514 baseEnd_350514 := by
    simpa [prefixWord, tailWord_350514, baseEnd_350514] using wordTrace_append hprefix tailTrace_350514
  have hstable : (prefixWord ++ tailWord_350514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350514).length < 2 ^ (prefixWord ++ tailWord_350514).sum := by decide
  have hdescent : baseEnd_350514 < baseStart_350514 := by decide
  rcases family_descends (prefixWord ++ tailWord_350514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350558 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_350558 : Nat := 118140960795 + 350558 * 2 ^ 59
def prefixEnd_350558 : Nat := 4983230072969 + 3 ^ 40 * 350558 * 2
def baseEnd_350558 : Nat := 160004223359061932366951

theorem tailTrace_350558 : CollatzResearch.WordTrace tailWord_350558 prefixEnd_350558 160004223359061932366951 := by
  unfold tailWord_350558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598237582999463923121541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8523933775997140923314885 1598237582999463923121541)
  ·
    refine ⟨299669546812399485585289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1598237582999463923121541 299669546812399485585289)
    ·
      refine ⟨224752160109299614188967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299669546812399485585289 224752160109299614188967)
      ·
        refine ⟨337128240163949421283451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224752160109299614188967 337128240163949421283451)
        ·
          refine ⟨505692360245924131925177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337128240163949421283451 505692360245924131925177)
          ·
            refine ⟨379269270184443098943883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505692360245924131925177 379269270184443098943883)
            ·
              refine ⟨568903905276664648415825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379269270184443098943883 568903905276664648415825)
              ·
                refine ⟨426677928957498486311869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 568903905276664648415825 426677928957498486311869)
                ·
                  refine ⟨160004223359061932366951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426677928957498486311869 160004223359061932366951)
                  ·
                    rfl

theorem cell20_350558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_350558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350558 prefixEnd_350558 := by exact prefixLift 350558
  have htrace : WordTrace (prefixWord ++ tailWord_350558) baseStart_350558 baseEnd_350558 := by
    simpa [prefixWord, tailWord_350558, baseEnd_350558] using wordTrace_append hprefix tailTrace_350558
  have hstable : (prefixWord ++ tailWord_350558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350558).length < 2 ^ (prefixWord ++ tailWord_350558).sum := by decide
  have hdescent : baseEnd_350558 < baseStart_350558 := by decide
  rcases family_descends (prefixWord ++ tailWord_350558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350573 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 2]
def baseStart_350573 : Nat := 118140960795 + 350573 * 2 ^ 59
def prefixEnd_350573 : Nat := 4983230072969 + 3 ^ 40 * 350573 * 2
def baseEnd_350573 : Nat := 160011069767788546866889

theorem tailTrace_350573 : CollatzResearch.WordTrace tailWord_350573 prefixEnd_350573 160011069767788546866889 := by
  unfold tailWord_350573
  simp only [CollatzResearch.WordTrace]
  refine ⟨12786447758941368946768373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8524298505960912631178915 12786447758941368946768373)
  ·
    refine ⟨1198729477400753338759535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12786447758941368946768373 1198729477400753338759535)
    ·
      refine ⟨1798094216101130008139303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198729477400753338759535 1798094216101130008139303)
      ·
        refine ⟨2697141324151695012208955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798094216101130008139303 2697141324151695012208955)
        ·
          refine ⟨4045711986227542518313433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697141324151695012208955 4045711986227542518313433)
          ·
            refine ⟨3034283989670656888735075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4045711986227542518313433 3034283989670656888735075)
            ·
              refine ⟨4551425984505985333102613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3034283989670656888735075 4551425984505985333102613)
              ·
                refine ⟨213348093023718062489185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4551425984505985333102613 213348093023718062489185)
                ·
                  refine ⟨160011069767788546866889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213348093023718062489185 160011069767788546866889)
                  ·
                    rfl

theorem cell20_350573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_350573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350573 prefixEnd_350573 := by exact prefixLift 350573
  have htrace : WordTrace (prefixWord ++ tailWord_350573) baseStart_350573 baseEnd_350573 := by
    simpa [prefixWord, tailWord_350573, baseEnd_350573] using wordTrace_append hprefix tailTrace_350573
  have hstable : (prefixWord ++ tailWord_350573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350573).length < 2 ^ (prefixWord ++ tailWord_350573).sum := by decide
  have hdescent : baseEnd_350573 < baseStart_350573 := by decide
  rcases family_descends (prefixWord ++ tailWord_350573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350601 : List Nat := [1, 2, 1, 1, 6, 2, 1, 6]
def baseStart_350601 : Nat := 118140960795 + 350601 * 2 ^ 59
def prefixEnd_350601 : Nat := 4983230072969 + 3 ^ 40 * 350601 * 2
def baseEnd_350601 : Nat := 53341283243581631311147

theorem tailTrace_350601 : CollatzResearch.WordTrace tailWord_350601 prefixEnd_350601 53341283243581631311147 := by
  unfold tailWord_350601
  simp only [CollatzResearch.WordTrace]
  refine ⟨12787469002839929728787657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8524979335226619819191771 12787469002839929728787657)
  ·
    refine ⟨9590601752129947296590743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12787469002839929728787657 9590601752129947296590743)
    ·
      refine ⟨14385902628194920944886115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9590601752129947296590743 14385902628194920944886115)
      ·
        refine ⟨21578853942292381417329173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14385902628194920944886115 21578853942292381417329173)
        ·
          refine ⟨1011508778544955378937305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21578853942292381417329173 1011508778544955378937305)
          ·
            refine ⟨758631583908716534202979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1011508778544955378937305 758631583908716534202979)
            ·
              refine ⟨1137947375863074801304469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758631583908716534202979 1137947375863074801304469)
              ·
                refine ⟨53341283243581631311147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1137947375863074801304469 53341283243581631311147)
                ·
                  rfl

theorem cell20_350601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 6].length) (baseStart_350601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350601 prefixEnd_350601 := by exact prefixLift 350601
  have htrace : WordTrace (prefixWord ++ tailWord_350601) baseStart_350601 baseEnd_350601 := by
    simpa [prefixWord, tailWord_350601, baseEnd_350601] using wordTrace_append hprefix tailTrace_350601
  have hstable : (prefixWord ++ tailWord_350601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350601).length < 2 ^ (prefixWord ++ tailWord_350601).sum := by decide
  have hdescent : baseEnd_350601 < baseStart_350601 := by decide
  rcases family_descends (prefixWord ++ tailWord_350601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350615 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 6]
def baseStart_350615 : Nat := 118140960795 + 350615 * 2 ^ 59
def prefixEnd_350615 : Nat := 4983230072969 + 3 ^ 40 * 350615 * 2
def baseEnd_350615 : Nat := 160030239712223067466717

theorem tailTrace_350615 : CollatzResearch.WordTrace tailWord_350615 prefixEnd_350615 160030239712223067466717 := by
  unfold tailWord_350615
  simp only [CollatzResearch.WordTrace]
  refine ⟨12787979624789210119797299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8525319749859473413198199 12787979624789210119797299)
  ·
    refine ⟨19181969437183815179695949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12787979624789210119797299 19181969437183815179695949)
    ·
      refine ⟨7193238538943930692385981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19181969437183815179695949 7193238538943930692385981)
      ·
        refine ⟨2697464452103974009644743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7193238538943930692385981 2697464452103974009644743)
        ·
          refine ⟨4046196678155961014467115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2697464452103974009644743 4046196678155961014467115)
          ·
            refine ⟨6069295017233941521700673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4046196678155961014467115 6069295017233941521700673)
            ·
              refine ⟨4551971262925456141275505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6069295017233941521700673 4551971262925456141275505)
              ·
                refine ⟨3413978447194092105956629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4551971262925456141275505 3413978447194092105956629)
                ·
                  refine ⟨160030239712223067466717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3413978447194092105956629 160030239712223067466717)
                  ·
                    rfl

theorem cell20_350615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_350615 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350615 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350615 prefixEnd_350615 := by exact prefixLift 350615
  have htrace : WordTrace (prefixWord ++ tailWord_350615) baseStart_350615 baseEnd_350615 := by
    simpa [prefixWord, tailWord_350615, baseEnd_350615] using wordTrace_append hprefix tailTrace_350615
  have hstable : (prefixWord ++ tailWord_350615).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350615).length < 2 ^ (prefixWord ++ tailWord_350615).sum := by decide
  have hdescent : baseEnd_350615 < baseStart_350615 := by decide
  rcases family_descends (prefixWord ++ tailWord_350615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350634 : List Nat := [3, 1, 6, 1, 2, 1, 2, 1, 3]
def baseStart_350634 : Nat := 118140960795 + 350634 * 2 ^ 59
def prefixEnd_350634 : Nat := 4983230072969 + 3 ^ 40 * 350634 * 2
def baseEnd_350634 : Nat := 160038911829943445833307

theorem tailTrace_350634 : CollatzResearch.WordTrace tailWord_350634 prefixEnd_350634 160038911829943445833307 := by
  unfold tailWord_350634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197168152930094091184739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8525781741146917576492637 3197168152930094091184739)
  ·
    refine ⟨4795752229395141136777109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3197168152930094091184739 4795752229395141136777109)
    ·
      refine ⟨224800885752897240786427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4795752229395141136777109 224800885752897240786427)
      ·
        refine ⟨337201328629345861179641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224800885752897240786427 337201328629345861179641)
        ·
          refine ⟨252900996472009395884731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337201328629345861179641 252900996472009395884731)
          ·
            refine ⟨379351494708014093827097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252900996472009395884731 379351494708014093827097)
            ·
              refine ⟨284513621031010570370323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379351494708014093827097 284513621031010570370323)
              ·
                refine ⟨426770431546515855555485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284513621031010570370323 426770431546515855555485)
                ·
                  refine ⟨160038911829943445833307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426770431546515855555485 160038911829943445833307)
                  ·
                    rfl

theorem cell20_350634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 1, 3].length) (baseStart_350634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350634 prefixEnd_350634 := by exact prefixLift 350634
  have htrace : WordTrace (prefixWord ++ tailWord_350634) baseStart_350634 baseEnd_350634 := by
    simpa [prefixWord, tailWord_350634, baseEnd_350634] using wordTrace_append hprefix tailTrace_350634
  have hstable : (prefixWord ++ tailWord_350634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350634).length < 2 ^ (prefixWord ++ tailWord_350634).sum := by decide
  have hdescent : baseEnd_350634 < baseStart_350634 := by decide
  rcases family_descends (prefixWord ++ tailWord_350634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350687 : List Nat := [1, 1, 2, 3, 3, 3, 1, 4, 2]
def baseStart_350687 : Nat := 118140960795 + 350687 * 2 ^ 59
def prefixEnd_350687 : Nat := 4983230072969 + 3 ^ 40 * 350687 * 2
def baseEnd_350687 : Nat := 160063102474110817066423

theorem tailTrace_350687 : CollatzResearch.WordTrace tailWord_350687 prefixEnd_350687 160063102474110817066423 := by
  unfold tailWord_350687
  simp only [CollatzResearch.WordTrace]
  refine ⟨12790605680528366416418315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8527070453685577610945543 12790605680528366416418315)
  ·
    refine ⟨19185908520792549624627473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12790605680528366416418315 19185908520792549624627473)
    ·
      refine ⟨14389431390594412218470605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19185908520792549624627473 14389431390594412218470605)
      ·
        refine ⟨5396036771472904581926477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14389431390594412218470605 5396036771472904581926477)
        ·
          refine ⟨2023513789302339218222429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5396036771472904581926477 2023513789302339218222429)
          ·
            refine ⟨758817670988377206833411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2023513789302339218222429 758817670988377206833411)
            ·
              refine ⟨1138226506482565810250117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758817670988377206833411 1138226506482565810250117)
              ·
                refine ⟨213417469965481089421897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1138226506482565810250117 213417469965481089421897)
                ·
                  refine ⟨160063102474110817066423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213417469965481089421897 160063102474110817066423)
                  ·
                    rfl

theorem cell20_350687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 2].length) (baseStart_350687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350687 prefixEnd_350687 := by exact prefixLift 350687
  have htrace : WordTrace (prefixWord ++ tailWord_350687) baseStart_350687 baseEnd_350687 := by
    simpa [prefixWord, tailWord_350687, baseEnd_350687] using wordTrace_append hprefix tailTrace_350687
  have hstable : (prefixWord ++ tailWord_350687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350687).length < 2 ^ (prefixWord ++ tailWord_350687).sum := by decide
  have hdescent : baseEnd_350687 < baseStart_350687 := by decide
  rcases family_descends (prefixWord ++ tailWord_350687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350690 : List Nat := [3, 3, 3, 2, 1, 2, 1, 5]
def baseStart_350690 : Nat := 118140960795 + 350690 * 2 ^ 59
def prefixEnd_350690 : Nat := 4983230072969 + 3 ^ 40 * 350690 * 2
def baseEnd_350690 : Nat := 53354823918618713322137

theorem tailTrace_350690 : CollatzResearch.WordTrace tailWord_350690 prefixEnd_350690 53354823918618713322137 := by
  unfold tailWord_350690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197678774879374482194381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8527143399678331952518349 3197678774879374482194381)
  ·
    refine ⟨1199129540579765430822893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3197678774879374482194381 1199129540579765430822893)
    ·
      refine ⟨449673577717412036558585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1199129540579765430822893 449673577717412036558585)
      ·
        refine ⟨337255183288059027418939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449673577717412036558585 337255183288059027418939)
        ·
          refine ⟨505882774932088541128409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337255183288059027418939 505882774932088541128409)
          ·
            refine ⟨379412081199066405846307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505882774932088541128409 379412081199066405846307)
            ·
              refine ⟨569118121798599608769461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379412081199066405846307 569118121798599608769461)
              ·
                refine ⟨53354823918618713322137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 569118121798599608769461 53354823918618713322137)
                ·
                  rfl

theorem cell20_350690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_350690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350690 prefixEnd_350690 := by exact prefixLift 350690
  have htrace : WordTrace (prefixWord ++ tailWord_350690) baseStart_350690 baseEnd_350690 := by
    simpa [prefixWord, tailWord_350690, baseEnd_350690] using wordTrace_append hprefix tailTrace_350690
  have hstable : (prefixWord ++ tailWord_350690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350690).length < 2 ^ (prefixWord ++ tailWord_350690).sum := by decide
  have hdescent : baseEnd_350690 < baseStart_350690 := by decide
  rcases family_descends (prefixWord ++ tailWord_350690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350766 : List Nat := [4, 1, 3, 1, 4, 1, 2, 4]
def baseStart_350766 : Nat := 118140960795 + 350766 * 2 ^ 59
def prefixEnd_350766 : Nat := 4983230072969 + 3 ^ 40 * 350766 * 2
def baseEnd_350766 : Nat := 53366386742245884477589

theorem tailTrace_350766 : CollatzResearch.WordTrace tailWord_350766 prefixEnd_350766 53366386742245884477589 := by
  unfold tailWord_350766
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599185880905270363568019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8528991364828108605696101 1599185880905270363568019)
  ·
    refine ⟨2398778821357905545352029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1599185880905270363568019 2398778821357905545352029)
    ·
      refine ⟨899542058009214579507011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2398778821357905545352029 899542058009214579507011)
      ·
        refine ⟨1349313087013821869260517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899542058009214579507011 1349313087013821869260517)
        ·
          refine ⟨252996203815091600486347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1349313087013821869260517 252996203815091600486347)
          ·
            refine ⟨379494305722637400729521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252996203815091600486347 379494305722637400729521)
            ·
              refine ⟨284620729291978050547141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379494305722637400729521 284620729291978050547141)
              ·
                refine ⟨53366386742245884477589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284620729291978050547141 53366386742245884477589)
                ·
                  rfl

theorem cell20_350766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 4].length) (baseStart_350766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350766 prefixEnd_350766 := by exact prefixLift 350766
  have htrace : WordTrace (prefixWord ++ tailWord_350766) baseStart_350766 baseEnd_350766 := by
    simpa [prefixWord, tailWord_350766, baseEnd_350766] using wordTrace_append hprefix tailTrace_350766
  have hstable : (prefixWord ++ tailWord_350766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350766).length < 2 ^ (prefixWord ++ tailWord_350766).sum := by decide
  have hdescent : baseEnd_350766 < baseStart_350766 := by decide
  rcases family_descends (prefixWord ++ tailWord_350766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350780 : List Nat := [2, 2, 2, 2, 3, 3, 1, 3, 2]
def baseStart_350780 : Nat := 118140960795 + 350780 * 2 ^ 59
def prefixEnd_350780 : Nat := 4983230072969 + 3 ^ 40 * 350780 * 2
def baseEnd_350780 : Nat := 160105550208215826966043

theorem tailTrace_350780 : CollatzResearch.WordTrace tailWord_350780 prefixEnd_350780 160105550208215826966043 := by
  unfold tailWord_350780
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396998834595721649776897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8529331779460962199702529 6396998834595721649776897)
  ·
    refine ⟨4797749125946791237332673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6396998834595721649776897 4797749125946791237332673)
    ·
      refine ⟨3598311844460093427999505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4797749125946791237332673 3598311844460093427999505)
      ·
        refine ⟨2698733883345070070999629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3598311844460093427999505 2698733883345070070999629)
        ·
          refine ⟨1012025206254401276624861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2698733883345070070999629 1012025206254401276624861)
          ·
            refine ⟨379509452345400478734323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1012025206254401276624861 379509452345400478734323)
            ·
              refine ⟨569264178518100718101485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379509452345400478734323 569264178518100718101485)
              ·
                refine ⟨213474066944287769288057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 569264178518100718101485 213474066944287769288057)
                ·
                  refine ⟨160105550208215826966043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213474066944287769288057 160105550208215826966043)
                  ·
                    rfl

theorem cell20_350780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 3, 2].length) (baseStart_350780 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350780 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350780 prefixEnd_350780 := by exact prefixLift 350780
  have htrace : WordTrace (prefixWord ++ tailWord_350780) baseStart_350780 baseEnd_350780 := by
    simpa [prefixWord, tailWord_350780, baseEnd_350780] using wordTrace_append hprefix tailTrace_350780
  have hstable : (prefixWord ++ tailWord_350780).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350780).length < 2 ^ (prefixWord ++ tailWord_350780).sum := by decide
  have hdescent : baseEnd_350780 < baseStart_350780 := by decide
  rcases family_descends (prefixWord ++ tailWord_350780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350791 : List Nat := [1, 1, 4, 1, 4, 3, 6]
def baseStart_350791 : Nat := 118140960795 + 350791 * 2 ^ 59
def prefixEnd_350791 : Nat := 4983230072969 + 3 ^ 40 * 350791 * 2
def baseEnd_350791 : Nat := 17790063434216519733259

theorem tailTrace_350791 : CollatzResearch.WordTrace tailWord_350791 prefixEnd_350791 17790063434216519733259 := by
  unfold tailWord_350791
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794398872151592178204227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8529599248101061452136151 12794398872151592178204227)
  ·
    refine ⟨19191598308227388267306341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12794398872151592178204227 19191598308227388267306341)
    ·
      refine ⟨3598424682792635300119939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19191598308227388267306341 3598424682792635300119939)
      ·
        refine ⟨5397637024188952950179909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598424682792635300119939 5397637024188952950179909)
        ·
          refine ⟨1012056942035428678158733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5397637024188952950179909 1012056942035428678158733)
          ·
            refine ⟨379521353263285754309525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1012056942035428678158733 379521353263285754309525)
            ·
              refine ⟨17790063434216519733259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 379521353263285754309525 17790063434216519733259)
              ·
                rfl

theorem cell20_350791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 6].length) (baseStart_350791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350791 prefixEnd_350791 := by exact prefixLift 350791
  have htrace : WordTrace (prefixWord ++ tailWord_350791) baseStart_350791 baseEnd_350791 := by
    simpa [prefixWord, tailWord_350791, baseEnd_350791] using wordTrace_append hprefix tailTrace_350791
  have hstable : (prefixWord ++ tailWord_350791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350791).length < 2 ^ (prefixWord ++ tailWord_350791).sum := by decide
  have hdescent : baseEnd_350791 < baseStart_350791 := by decide
  rcases family_descends (prefixWord ++ tailWord_350791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350797 : List Nat := [1, 6, 1, 1, 2, 2, 3, 2, 2]
def baseStart_350797 : Nat := 118140960795 + 350797 * 2 ^ 59
def prefixEnd_350797 : Nat := 4983230072969 + 3 ^ 40 * 350797 * 2
def baseEnd_350797 : Nat := 160113309471439323399307

theorem tailTrace_350797 : CollatzResearch.WordTrace tailWord_350797 prefixEnd_350797 160113309471439323399307 := by
  unfold tailWord_350797
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794617710129855202922645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8529745140086570135281763 12794617710129855202922645)
  ·
    refine ⟨599747705162336962636999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12794617710129855202922645 599747705162336962636999)
    ·
      refine ⟨899621557743505443955499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 599747705162336962636999 899621557743505443955499)
      ·
        refine ⟨1349432336615258165933249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 899621557743505443955499 1349432336615258165933249)
        ·
          refine ⟨1012074252461443624449937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1349432336615258165933249 1012074252461443624449937)
          ·
            refine ⟨759055689346082718337453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012074252461443624449937 759055689346082718337453)
            ·
              refine ⟨284645883504781019376545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759055689346082718337453 284645883504781019376545)
              ·
                refine ⟨213484412628585764532409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284645883504781019376545 213484412628585764532409)
                ·
                  refine ⟨160113309471439323399307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213484412628585764532409 160113309471439323399307)
                  ·
                    rfl

theorem cell20_350797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_350797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350797 prefixEnd_350797 := by exact prefixLift 350797
  have htrace : WordTrace (prefixWord ++ tailWord_350797) baseStart_350797 baseEnd_350797 := by
    simpa [prefixWord, tailWord_350797, baseEnd_350797] using wordTrace_append hprefix tailTrace_350797
  have hstable : (prefixWord ++ tailWord_350797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350797).length < 2 ^ (prefixWord ++ tailWord_350797).sum := by decide
  have hdescent : baseEnd_350797 < baseStart_350797 := by decide
  rcases family_descends (prefixWord ++ tailWord_350797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350798 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 5]
def baseStart_350798 : Nat := 118140960795 + 350798 * 2 ^ 59
def prefixEnd_350798 : Nat := 4983230072969 + 3 ^ 40 * 350798 * 2
def baseEnd_350798 : Nat := 160113765898687764365969

theorem tailTrace_350798 : CollatzResearch.WordTrace tailWord_350798 prefixEnd_350798 160113765898687764365969 := by
  unfold tailWord_350798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599331772890779046713631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8529769455417488249139365 1599331772890779046713631)
  ·
    refine ⟨2398997659336168570070447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1599331772890779046713631 2398997659336168570070447)
    ·
      refine ⟨3598496489004252855105671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2398997659336168570070447 3598496489004252855105671)
      ·
        refine ⟨5397744733506379282658507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3598496489004252855105671 5397744733506379282658507)
        ·
          refine ⟨8096617100259568923987761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5397744733506379282658507 8096617100259568923987761)
          ·
            refine ⟨6072462825194676692990821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8096617100259568923987761 6072462825194676692990821)
            ·
              refine ⟨1138586779724001879935779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6072462825194676692990821 1138586779724001879935779)
              ·
                refine ⟨1707880169586002819903669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138586779724001879935779 1707880169586002819903669)
                ·
                  refine ⟨160113765898687764365969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1707880169586002819903669 160113765898687764365969)
                  ·
                    rfl

theorem cell20_350798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_350798 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350798 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350798 prefixEnd_350798 := by exact prefixLift 350798
  have htrace : WordTrace (prefixWord ++ tailWord_350798) baseStart_350798 baseEnd_350798 := by
    simpa [prefixWord, tailWord_350798, baseEnd_350798] using wordTrace_append hprefix tailTrace_350798
  have hstable : (prefixWord ++ tailWord_350798).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350798).length < 2 ^ (prefixWord ++ tailWord_350798).sum := by decide
  have hdescent : baseEnd_350798 < baseStart_350798 := by decide
  rcases family_descends (prefixWord ++ tailWord_350798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350829 : List Nat := [1, 5, 1, 1, 3, 1, 2, 6]
def baseStart_350829 : Nat := 118140960795 + 350829 * 2 ^ 59
def prefixEnd_350829 : Nat := 4983230072969 + 3 ^ 40 * 350829 * 2
def baseEnd_350829 : Nat := 53375971714463144777503

theorem tailTrace_350829 : CollatzResearch.WordTrace tailWord_350829 prefixEnd_350829 53375971714463144777503 := by
  unfold tailWord_350829
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795784846013924668087541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8530523230675949778725027 12795784846013924668087541)
  ·
    refine ⟨1199604829313805437633207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12795784846013924668087541 1199604829313805437633207)
    ·
      refine ⟨1799407243970708156449811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1199604829313805437633207 1799407243970708156449811)
      ·
        refine ⟨2699110865956062234674717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1799407243970708156449811 2699110865956062234674717)
        ·
          refine ⟨1012166574733523338003019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2699110865956062234674717 1012166574733523338003019)
          ·
            refine ⟨1518249862100285007004529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012166574733523338003019 1518249862100285007004529)
            ·
              refine ⟨1138687396575213755253397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1518249862100285007004529 1138687396575213755253397)
              ·
                refine ⟨53375971714463144777503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1138687396575213755253397 53375971714463144777503)
                ·
                  rfl

theorem cell20_350829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 6].length) (baseStart_350829 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350829 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350829 prefixEnd_350829 := by exact prefixLift 350829
  have htrace : WordTrace (prefixWord ++ tailWord_350829) baseStart_350829 baseEnd_350829 := by
    simpa [prefixWord, tailWord_350829, baseEnd_350829] using wordTrace_append hprefix tailTrace_350829
  have hstable : (prefixWord ++ tailWord_350829).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350829).length < 2 ^ (prefixWord ++ tailWord_350829).sum := by decide
  have hdescent : baseEnd_350829 < baseStart_350829 := by decide
  rcases family_descends (prefixWord ++ tailWord_350829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350853 : List Nat := [1, 3, 1, 1, 4, 3, 2, 2, 3]
def baseStart_350853 : Nat := 118140960795 + 350853 * 2 ^ 59
def prefixEnd_350853 : Nat := 4983230072969 + 3 ^ 40 * 350853 * 2
def baseEnd_350853 : Nat := 160138869397352017532411

theorem tailTrace_350853 : CollatzResearch.WordTrace tailWord_350853 prefixEnd_350853 160138869397352017532411 := by
  unfold tailWord_350853
  simp only [CollatzResearch.WordTrace]
  refine ⟨12796660197926976766961213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8531106798617984511307475 12796660197926976766961213)
  ·
    refine ⟨4798747574222616287610455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12796660197926976766961213 4798747574222616287610455)
    ·
      refine ⟨7198121361333924431415683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4798747574222616287610455 7198121361333924431415683)
      ·
        refine ⟨10797182042000886647123525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7198121361333924431415683 10797182042000886647123525)
        ·
          refine ⟨2024471632875166246335661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10797182042000886647123525 2024471632875166246335661)
          ·
            refine ⟨759176862328187342375873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2024471632875166246335661 759176862328187342375873)
            ·
              refine ⟨569382646746140506781905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759176862328187342375873 569382646746140506781905)
              ·
                refine ⟨427036985059605380086429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569382646746140506781905 427036985059605380086429)
                ·
                  refine ⟨160138869397352017532411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427036985059605380086429 160138869397352017532411)
                  ·
                    rfl

theorem cell20_350853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_350853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350853 prefixEnd_350853 := by exact prefixLift 350853
  have htrace : WordTrace (prefixWord ++ tailWord_350853) baseStart_350853 baseEnd_350853 := by
    simpa [prefixWord, tailWord_350853, baseEnd_350853] using wordTrace_append hprefix tailTrace_350853
  have hstable : (prefixWord ++ tailWord_350853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350853).length < 2 ^ (prefixWord ++ tailWord_350853).sum := by decide
  have hdescent : baseEnd_350853 < baseStart_350853 := by decide
  rcases family_descends (prefixWord ++ tailWord_350853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350894 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_350894 : Nat := 118140960795 + 350894 * 2 ^ 59
def prefixEnd_350894 : Nat := 4983230072969 + 3 ^ 40 * 350894 * 2
def baseEnd_350894 : Nat := 160157582914538097165577

theorem tailTrace_350894 : CollatzResearch.WordTrace tailWord_350894 prefixEnd_350894 160157582914538097165577 := by
  unfold tailWord_350894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1599769448847305096150467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8532103727185627179469157 1599769448847305096150467)
  ·
    refine ⟨2399654173270957644225701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1599769448847305096150467 2399654173270957644225701)
    ·
      refine ⟨449935157488304558292319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2399654173270957644225701 449935157488304558292319)
      ·
        refine ⟨674902736232456837438479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449935157488304558292319 674902736232456837438479)
        ·
          refine ⟨1012354104348685256157719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674902736232456837438479 1012354104348685256157719)
          ·
            refine ⟨1518531156523027884236579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1012354104348685256157719 1518531156523027884236579)
            ·
              refine ⟨2277796734784541826354869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1518531156523027884236579 2277796734784541826354869)
              ·
                refine ⟨213543443886050796220769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2277796734784541826354869 213543443886050796220769)
                ·
                  refine ⟨160157582914538097165577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213543443886050796220769 160157582914538097165577)
                  ·
                    rfl

theorem cell20_350894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_350894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350894 prefixEnd_350894 := by exact prefixLift 350894
  have htrace : WordTrace (prefixWord ++ tailWord_350894) baseStart_350894 baseEnd_350894 := by
    simpa [prefixWord, tailWord_350894, baseEnd_350894] using wordTrace_append hprefix tailTrace_350894
  have hstable : (prefixWord ++ tailWord_350894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350894).length < 2 ^ (prefixWord ++ tailWord_350894).sum := by decide
  have hdescent : baseEnd_350894 < baseStart_350894 := by decide
  rcases family_descends (prefixWord ++ tailWord_350894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350912 : List Nat := [2, 1, 1, 2, 4, 3, 1, 1, 5]
def baseStart_350912 : Nat := 118140960795 + 350912 * 2 ^ 59
def prefixEnd_350912 : Nat := 4983230072969 + 3 ^ 40 * 350912 * 2
def baseEnd_350912 : Nat := 160165798605010034565503

theorem tailTrace_350912 : CollatzResearch.WordTrace tailWord_350912 prefixEnd_350912 160165798605010034565503 := by
  unfold tailWord_350912
  simp only [CollatzResearch.WordTrace]
  refine ⟨6399406052356614921679495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8532541403142153228905993 6399406052356614921679495)
  ·
    refine ⟨9599109078534922382519243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6399406052356614921679495 9599109078534922382519243)
    ·
      refine ⟨14398663617802383573778865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9599109078534922382519243 14398663617802383573778865)
      ·
        refine ⟨10798997713351787680334149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14398663617802383573778865 10798997713351787680334149)
        ·
          refine ⟨2024812071253460190062653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10798997713351787680334149 2024812071253460190062653)
          ·
            refine ⟨759304526720047571273495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2024812071253460190062653 759304526720047571273495)
            ·
              refine ⟨1138956790080071356910243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759304526720047571273495 1138956790080071356910243)
              ·
                refine ⟨1708435185120107035365365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138956790080071356910243 1708435185120107035365365)
                ·
                  refine ⟨160165798605010034565503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1708435185120107035365365 160165798605010034565503)
                  ·
                    rfl

theorem cell20_350912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 5].length) (baseStart_350912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350912 prefixEnd_350912 := by exact prefixLift 350912
  have htrace : WordTrace (prefixWord ++ tailWord_350912) baseStart_350912 baseEnd_350912 := by
    simpa [prefixWord, tailWord_350912, baseEnd_350912] using wordTrace_append hprefix tailTrace_350912
  have hstable : (prefixWord ++ tailWord_350912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350912).length < 2 ^ (prefixWord ++ tailWord_350912).sum := by decide
  have hdescent : baseEnd_350912 < baseStart_350912 := by decide
  rcases family_descends (prefixWord ++ tailWord_350912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350929 : List Nat := [1, 2, 2, 1, 2, 3, 5, 1, 3]
def baseStart_350929 : Nat := 118140960795 + 350929 * 2 ^ 59
def prefixEnd_350929 : Nat := 4983230072969 + 3 ^ 40 * 350929 * 2
def baseEnd_350929 : Nat := 160173557868233530998767

theorem tailTrace_350929 : CollatzResearch.WordTrace tailWord_350929 prefixEnd_350929 160173557868233530998767 := by
  unfold tailWord_350929
  simp only [CollatzResearch.WordTrace]
  refine ⟨12799432145651641746727841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8532954763767761164485227 12799432145651641746727841)
  ·
    refine ⟨9599574109238731310045881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12799432145651641746727841 9599574109238731310045881)
    ·
      refine ⟨7199680581929048482534411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9599574109238731310045881 7199680581929048482534411)
      ·
        refine ⟨10799520872893572723801617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7199680581929048482534411 10799520872893572723801617)
        ·
          refine ⟨8099640654670179542851213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10799520872893572723801617 8099640654670179542851213)
          ·
            refine ⟨3037365245501317328569205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8099640654670179542851213 3037365245501317328569205)
            ·
              refine ⟨284752991765748499553363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3037365245501317328569205 284752991765748499553363)
              ·
                refine ⟨427129487648622749330045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284752991765748499553363 427129487648622749330045)
                ·
                  refine ⟨160173557868233530998767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427129487648622749330045 160173557868233530998767)
                  ·
                    rfl

theorem cell20_350929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 1, 3].length) (baseStart_350929 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350929 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350929 prefixEnd_350929 := by exact prefixLift 350929
  have htrace : WordTrace (prefixWord ++ tailWord_350929) baseStart_350929 baseEnd_350929 := by
    simpa [prefixWord, tailWord_350929, baseEnd_350929] using wordTrace_append hprefix tailTrace_350929
  have hstable : (prefixWord ++ tailWord_350929).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350929).length < 2 ^ (prefixWord ++ tailWord_350929).sum := by decide
  have hdescent : baseEnd_350929 < baseStart_350929 := by decide
  rcases family_descends (prefixWord ++ tailWord_350929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350943 : List Nat := [1, 1, 2, 3, 2, 3, 4, 4]
def baseStart_350943 : Nat := 118140960795 + 350943 * 2 ^ 59
def prefixEnd_350943 : Nat := 4983230072969 + 3 ^ 40 * 350943 * 2
def baseEnd_350943 : Nat := 53393315949903901510681

theorem tailTrace_350943 : CollatzResearch.WordTrace tailWord_350943 prefixEnd_350943 53393315949903901510681 := by
  unfold tailWord_350943
  simp only [CollatzResearch.WordTrace]
  refine ⟨12799942767600922137737483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8533295178400614758491655 12799942767600922137737483)
  ·
    refine ⟨19199914151401383206606225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12799942767600922137737483 19199914151401383206606225)
    ·
      refine ⟨14399935613551037404954669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19199914151401383206606225 14399935613551037404954669)
      ·
        refine ⟨5399975855081639026858001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14399935613551037404954669 5399975855081639026858001)
        ·
          refine ⟨4049981891311229270143501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5399975855081639026858001 4049981891311229270143501)
          ·
            refine ⟨1518743209241710976303813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4049981891311229270143501 1518743209241710976303813)
            ·
              refine ⟨284764351732820808056965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1518743209241710976303813 284764351732820808056965)
              ·
                refine ⟨53393315949903901510681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284764351732820808056965 53393315949903901510681)
                ·
                  rfl

theorem cell20_350943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 4].length) (baseStart_350943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350943 prefixEnd_350943 := by exact prefixLift 350943
  have htrace : WordTrace (prefixWord ++ tailWord_350943) baseStart_350943 baseEnd_350943 := by
    simpa [prefixWord, tailWord_350943, baseEnd_350943] using wordTrace_append hprefix tailTrace_350943
  have hstable : (prefixWord ++ tailWord_350943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350943).length < 2 ^ (prefixWord ++ tailWord_350943).sum := by decide
  have hdescent : baseEnd_350943 < baseStart_350943 := by decide
  rcases family_descends (prefixWord ++ tailWord_350943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350984 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 3]
def baseStart_350984 : Nat := 118140960795 + 350984 * 2 ^ 59
def prefixEnd_350984 : Nat := 4983230072969 + 3 ^ 40 * 350984 * 2
def baseEnd_350984 : Nat := 160198661366897784165209

theorem tailTrace_350984 : CollatzResearch.WordTrace tailWord_350984 prefixEnd_350984 160198661366897784165209 := by
  unfold tailWord_350984
  simp only [CollatzResearch.WordTrace]
  refine ⟨6400719080226193069990003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8534292106968257426653337 6400719080226193069990003)
  ·
    refine ⟨9601078620339289604985005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6400719080226193069990003 9601078620339289604985005)
    ·
      refine ⟨3600404482627233601869377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9601078620339289604985005 3600404482627233601869377)
      ·
        refine ⟨2700303361970425201402033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3600404482627233601869377 2700303361970425201402033)
        ·
          refine ⟨2025227521477818901051525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2700303361970425201402033 2025227521477818901051525)
          ·
            refine ⟨379730160277091043947161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2025227521477818901051525 379730160277091043947161)
            ·
              refine ⟨284797620207818282960371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379730160277091043947161 284797620207818282960371)
              ·
                refine ⟨427196430311727424440557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284797620207818282960371 427196430311727424440557)
                ·
                  refine ⟨160198661366897784165209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427196430311727424440557 160198661366897784165209)
                  ·
                    rfl

theorem cell20_350984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 3].length) (baseStart_350984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_350984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_350984 prefixEnd_350984 := by exact prefixLift 350984
  have htrace : WordTrace (prefixWord ++ tailWord_350984) baseStart_350984 baseEnd_350984 := by
    simpa [prefixWord, tailWord_350984, baseEnd_350984] using wordTrace_append hprefix tailTrace_350984
  have hstable : (prefixWord ++ tailWord_350984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350984).length < 2 ^ (prefixWord ++ tailWord_350984).sum := by decide
  have hdescent : baseEnd_350984 < baseStart_350984 := by decide
  rcases family_descends (prefixWord ++ tailWord_350984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351002 : List Nat := [3, 1, 1, 3, 2, 1, 1, 8]
def baseStart_351002 : Nat := 118140960795 + 351002 * 2 ^ 59
def prefixEnd_351002 : Nat := 4983230072969 + 3 ^ 40 * 351002 * 2
def baseEnd_351002 : Nat := 53402292352456573855045

theorem tailTrace_351002 : CollatzResearch.WordTrace tailWord_351002 prefixEnd_351002 53402292352456573855045 := by
  unfold tailWord_351002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3200523668596793803533815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8534729782924783476090173 3200523668596793803533815)
  ·
    refine ⟨4800785502895190705300723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3200523668596793803533815 4800785502895190705300723)
    ·
      refine ⟨7201178254342786057951085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4800785502895190705300723 7201178254342786057951085)
      ·
        refine ⟨2700441845378544771731657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7201178254342786057951085 2700441845378544771731657)
        ·
          refine ⟨2025331384033908578798743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2700441845378544771731657 2025331384033908578798743)
          ·
            refine ⟨3037997076050862868198115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2025331384033908578798743 3037997076050862868198115)
            ·
              refine ⟨4556995614076294302297173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037997076050862868198115 4556995614076294302297173)
              ·
                refine ⟨53402292352456573855045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4556995614076294302297173 53402292352456573855045)
                ·
                  rfl

theorem cell20_351002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_351002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351002 prefixEnd_351002 := by exact prefixLift 351002
  have htrace : WordTrace (prefixWord ++ tailWord_351002) baseStart_351002 baseEnd_351002 := by
    simpa [prefixWord, tailWord_351002, baseEnd_351002] using wordTrace_append hprefix tailTrace_351002
  have hstable : (prefixWord ++ tailWord_351002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351002).length < 2 ^ (prefixWord ++ tailWord_351002).sum := by decide
  have hdescent : baseEnd_351002 < baseStart_351002 := by decide
  rcases family_descends (prefixWord ++ tailWord_351002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351021 : List Nat := [1, 5, 3, 2, 2, 1, 2, 2, 2]
def baseStart_351021 : Nat := 118140960795 + 351021 * 2 ^ 59
def prefixEnd_351021 : Nat := 4983230072969 + 3 ^ 40 * 351021 * 2
def baseEnd_351021 : Nat := 160215549175090099931725

theorem tailTrace_351021 : CollatzResearch.WordTrace tailWord_351021 prefixEnd_351021 160215549175090099931725 := by
  unfold tailWord_351021
  simp only [CollatzResearch.WordTrace]
  refine ⟨12802787661318341459076917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535191774212227639384611 12802787661318341459076917)
  ·
    refine ⟨1200261343248594511788461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12802787661318341459076917 1200261343248594511788461)
    ·
      refine ⟨450098003718222941920673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1200261343248594511788461 450098003718222941920673)
      ·
        refine ⟨337573502788667206440505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450098003718222941920673 337573502788667206440505)
        ·
          refine ⟨253180127091500404830379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337573502788667206440505 253180127091500404830379)
          ·
            refine ⟨379770190637250607245569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253180127091500404830379 379770190637250607245569)
            ·
              refine ⟨284827642977937955434177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379770190637250607245569 284827642977937955434177)
              ·
                refine ⟨213620732233453466575633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284827642977937955434177 213620732233453466575633)
                ·
                  refine ⟨160215549175090099931725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213620732233453466575633 160215549175090099931725)
                  ·
                    rfl

theorem cell20_351021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_351021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351021 prefixEnd_351021 := by exact prefixLift 351021
  have htrace : WordTrace (prefixWord ++ tailWord_351021) baseStart_351021 baseEnd_351021 := by
    simpa [prefixWord, tailWord_351021, baseEnd_351021] using wordTrace_append hprefix tailTrace_351021
  have hstable : (prefixWord ++ tailWord_351021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351021).length < 2 ^ (prefixWord ++ tailWord_351021).sum := by decide
  have hdescent : baseEnd_351021 < baseStart_351021 := by decide
  rcases family_descends (prefixWord ++ tailWord_351021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351022 : List Nat := [4, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_351022 : Nat := 118140960795 + 351022 * 2 ^ 59
def prefixEnd_351022 : Nat := 4983230072969 + 3 ^ 40 * 351022 * 2
def baseEnd_351022 : Nat := 160216005602338540898387

theorem tailTrace_351022 : CollatzResearch.WordTrace tailWord_351022 prefixEnd_351022 160216005602338540898387 := by
  unfold tailWord_351022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1600353016789339828732915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8535216089543145753242213 1600353016789339828732915)
  ·
    refine ⟨2400529525184009743099373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1600353016789339828732915 2400529525184009743099373)
    ·
      refine ⟨900198571944003653662265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2400529525184009743099373 900198571944003653662265)
      ·
        refine ⟨675148928958002740246699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900198571944003653662265 675148928958002740246699)
        ·
          refine ⟨1012723393437004110370049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675148928958002740246699 1012723393437004110370049)
          ·
            refine ⟨759542545077753082777537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012723393437004110370049 759542545077753082777537)
            ·
              refine ⟨569656908808314812083153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759542545077753082777537 569656908808314812083153)
              ·
                refine ⟨427242681606236109062365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569656908808314812083153 427242681606236109062365)
                ·
                  refine ⟨160216005602338540898387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427242681606236109062365 160216005602338540898387)
                  ·
                    rfl

theorem cell20_351022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_351022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351022 prefixEnd_351022 := by exact prefixLift 351022
  have htrace : WordTrace (prefixWord ++ tailWord_351022) baseStart_351022 baseEnd_351022 := by
    simpa [prefixWord, tailWord_351022, baseEnd_351022] using wordTrace_append hprefix tailTrace_351022
  have hstable : (prefixWord ++ tailWord_351022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351022).length < 2 ^ (prefixWord ++ tailWord_351022).sum := by decide
  have hdescent : baseEnd_351022 < baseStart_351022 := by decide
  rcases family_descends (prefixWord ++ tailWord_351022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351029 : List Nat := [1, 3, 3, 1, 3, 2, 1, 4, 2]
def baseStart_351029 : Nat := 118140960795 + 351029 * 2 ^ 59
def prefixEnd_351029 : Nat := 4983230072969 + 3 ^ 40 * 351029 * 2
def baseEnd_351029 : Nat := 160219200593077627665025

theorem tailTrace_351029 : CollatzResearch.WordTrace tailWord_351029 prefixEnd_351029 160219200593077627665025 := by
  unfold tailWord_351029
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803079445289358825368141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535386296859572550245427 12803079445289358825368141)
  ·
    refine ⟨4801154791983509559513053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12803079445289358825368141 4801154791983509559513053)
    ·
      refine ⟨1800433046993816084817395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4801154791983509559513053 1800433046993816084817395)
      ·
        refine ⟨2700649570490724127226093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1800433046993816084817395 2700649570490724127226093)
        ·
          refine ⟨1012743588934021547709785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2700649570490724127226093 1012743588934021547709785)
          ·
            refine ⟨759557691700516160782339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1012743588934021547709785 759557691700516160782339)
            ·
              refine ⟨1139336537550774241173509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759557691700516160782339 1139336537550774241173509)
              ·
                refine ⟨213625600790770170220033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1139336537550774241173509 213625600790770170220033)
                ·
                  refine ⟨160219200593077627665025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213625600790770170220033 160219200593077627665025)
                  ·
                    rfl

theorem cell20_351029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_351029 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351029 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351029 prefixEnd_351029 := by exact prefixLift 351029
  have htrace : WordTrace (prefixWord ++ tailWord_351029) baseStart_351029 baseEnd_351029 := by
    simpa [prefixWord, tailWord_351029, baseEnd_351029] using wordTrace_append hprefix tailTrace_351029
  have hstable : (prefixWord ++ tailWord_351029).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351029).length < 2 ^ (prefixWord ++ tailWord_351029).sum := by decide
  have hdescent : baseEnd_351029 < baseStart_351029 := by decide
  rcases family_descends (prefixWord ++ tailWord_351029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351046 : List Nat := [6, 1, 1, 2, 2, 1, 1, 2, 4]
def baseStart_351046 : Nat := 118140960795 + 351046 * 2 ^ 59
def prefixEnd_351046 : Nat := 4983230072969 + 3 ^ 40 * 351046 * 2
def baseEnd_351046 : Nat := 160226959856301124098289

theorem tailTrace_351046 : CollatzResearch.WordTrace tailWord_351046 prefixEnd_351046 160226959856301124098289 := by
  unfold tailWord_351046
  simp only [CollatzResearch.WordTrace]
  refine ⟨400115608944617835273031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8535799657485180485824661 400115608944617835273031)
  ·
    refine ⟨600173413416926752909547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400115608944617835273031 600173413416926752909547)
    ·
      refine ⟨900260120125390129364321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600173413416926752909547 900260120125390129364321)
      ·
        refine ⟨675195090094042597023241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900260120125390129364321 675195090094042597023241)
        ·
          refine ⟨506396317570531947767431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675195090094042597023241 506396317570531947767431)
          ·
            refine ⟨759594476355797921651147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506396317570531947767431 759594476355797921651147)
            ·
              refine ⟨1139391714533696882476721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 759594476355797921651147 1139391714533696882476721)
              ·
                refine ⟨854543785900272661857541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139391714533696882476721 854543785900272661857541)
                ·
                  refine ⟨160226959856301124098289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854543785900272661857541 160226959856301124098289)
                  ·
                    rfl

theorem cell20_351046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_351046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351046 prefixEnd_351046 := by exact prefixLift 351046
  have htrace : WordTrace (prefixWord ++ tailWord_351046) baseStart_351046 baseEnd_351046 := by
    simpa [prefixWord, tailWord_351046, baseEnd_351046] using wordTrace_append hprefix tailTrace_351046
  have hstable : (prefixWord ++ tailWord_351046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351046).length < 2 ^ (prefixWord ++ tailWord_351046).sum := by decide
  have hdescent : baseEnd_351046 < baseStart_351046 := by decide
  rcases family_descends (prefixWord ++ tailWord_351046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351047 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 7]
def baseStart_351047 : Nat := 118140960795 + 351047 * 2 ^ 59
def prefixEnd_351047 : Nat := 4983230072969 + 3 ^ 40 * 351047 * 2
def baseEnd_351047 : Nat := 160227416283549565064951

theorem tailTrace_351047 : CollatzResearch.WordTrace tailWord_351047 prefixEnd_351047 160227416283549565064951 := by
  unfold tailWord_351047
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803735959224147899523395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535823972816098599682263 12803735959224147899523395)
  ·
    refine ⟨19205603938836221849285093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12803735959224147899523395 19205603938836221849285093)
    ·
      refine ⟨3601050738531791596740955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19205603938836221849285093 3601050738531791596740955)
      ·
        refine ⟨5401576107797687395111433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3601050738531791596740955 5401576107797687395111433)
        ·
          refine ⟨4051182080848265546333575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5401576107797687395111433 4051182080848265546333575)
          ·
            refine ⟨6076773121272398319500363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051182080848265546333575 6076773121272398319500363)
            ·
              refine ⟨9115159681908597479250545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076773121272398319500363 9115159681908597479250545)
              ·
                refine ⟨6836369761431448109437909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9115159681908597479250545 6836369761431448109437909)
                ·
                  refine ⟨160227416283549565064951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6836369761431448109437909 160227416283549565064951)
                  ·
                    rfl

theorem cell20_351047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 7].length) (baseStart_351047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351047 prefixEnd_351047 := by exact prefixLift 351047
  have htrace : WordTrace (prefixWord ++ tailWord_351047) baseStart_351047 baseEnd_351047 := by
    simpa [prefixWord, tailWord_351047, baseEnd_351047] using wordTrace_append hprefix tailTrace_351047
  have hstable : (prefixWord ++ tailWord_351047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351047).length < 2 ^ (prefixWord ++ tailWord_351047).sum := by decide
  have hdescent : baseEnd_351047 < baseStart_351047 := by decide
  rcases family_descends (prefixWord ++ tailWord_351047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351053 : List Nat := [1, 6, 1, 2, 2, 1, 3, 4]
def baseStart_351053 : Nat := 118140960795 + 351053 * 2 ^ 59
def prefixEnd_351053 : Nat := 4983230072969 + 3 ^ 40 * 351053 * 2
def baseEnd_351053 : Nat := 53410051615680070288309

theorem tailTrace_351053 : CollatzResearch.WordTrace tailWord_351053 prefixEnd_351053 53410051615680070288309 := by
  unfold tailWord_351053
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803954797202410924241813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535969864801607282827875 12803954797202410924241813)
  ·
    refine ⟨600185381118863012073835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12803954797202410924241813 600185381118863012073835)
    ·
      refine ⟨900278071678294518110753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600185381118863012073835 900278071678294518110753)
      ·
        refine ⟨675208553758720888583065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900278071678294518110753 675208553758720888583065)
        ·
          refine ⟨506406415319040666437299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675208553758720888583065 506406415319040666437299)
          ·
            refine ⟨759609622978560999655949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506406415319040666437299 759609622978560999655949)
            ·
              refine ⟨284853608616960374870981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759609622978560999655949 284853608616960374870981)
              ·
                refine ⟨53410051615680070288309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284853608616960374870981 53410051615680070288309)
                ·
                  rfl

theorem cell20_351053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_351053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351053 prefixEnd_351053 := by exact prefixLift 351053
  have htrace : WordTrace (prefixWord ++ tailWord_351053) baseStart_351053 baseEnd_351053 := by
    simpa [prefixWord, tailWord_351053, baseEnd_351053] using wordTrace_append hprefix tailTrace_351053
  have hstable : (prefixWord ++ tailWord_351053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351053).length < 2 ^ (prefixWord ++ tailWord_351053).sum := by decide
  have hdescent : baseEnd_351053 < baseStart_351053 := by decide
  rcases family_descends (prefixWord ++ tailWord_351053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351088 : List Nat := [2, 1, 1, 1, 4, 1, 4, 4, 2]
def baseStart_351088 : Nat := 118140960795 + 351088 * 2 ^ 59
def prefixEnd_351088 : Nat := 4983230072969 + 3 ^ 40 * 351088 * 2
def baseEnd_351088 : Nat := 160246129800735644698117

theorem tailTrace_351088 : CollatzResearch.WordTrace tailWord_351088 prefixEnd_351088 160246129800735644698117 := by
  unfold tailWord_351088
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402615676037805950882959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8536820901383741267843945 6402615676037805950882959)
  ·
    refine ⟨9603923514056708926324439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402615676037805950882959 9603923514056708926324439)
    ·
      refine ⟨14405885271085063389486659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9603923514056708926324439 14405885271085063389486659)
      ·
        refine ⟨21608827906627595084229989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405885271085063389486659 21608827906627595084229989)
        ·
          refine ⟨4051655232492674078293123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21608827906627595084229989 4051655232492674078293123)
          ·
            refine ⟨6077482848739011117439685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051655232492674078293123 6077482848739011117439685)
            ·
              refine ⟨1139528034138564584519941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6077482848739011117439685 1139528034138564584519941)
              ·
                refine ⟨213661506400980859597489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1139528034138564584519941 213661506400980859597489)
                ·
                  refine ⟨160246129800735644698117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213661506400980859597489 160246129800735644698117)
                  ·
                    rfl

theorem cell20_351088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 2].length) (baseStart_351088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351088 prefixEnd_351088 := by exact prefixLift 351088
  have htrace : WordTrace (prefixWord ++ tailWord_351088) baseStart_351088 baseEnd_351088 := by
    simpa [prefixWord, tailWord_351088, baseEnd_351088] using wordTrace_append hprefix tailTrace_351088
  have hstable : (prefixWord ++ tailWord_351088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351088).length < 2 ^ (prefixWord ++ tailWord_351088).sum := by decide
  have hdescent : baseEnd_351088 < baseStart_351088 := by decide
  rcases family_descends (prefixWord ++ tailWord_351088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351109 : List Nat := [1, 3, 1, 1, 3, 3, 2, 2, 4]
def baseStart_351109 : Nat := 118140960795 + 351109 * 2 ^ 59
def prefixEnd_351109 : Nat := 4983230072969 + 3 ^ 40 * 351109 * 2
def baseEnd_351109 : Nat := 160255714772952904998031

theorem tailTrace_351109 : CollatzResearch.WordTrace tailWord_351109 prefixEnd_351109 160255714772952904998031 := by
  unfold tailWord_351109
  simp only [CollatzResearch.WordTrace]
  refine ⟨12805997284999532488280381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8537331523333021658853587 12805997284999532488280381)
  ·
    refine ⟨4802248981874824683105143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12805997284999532488280381 4802248981874824683105143)
    ·
      refine ⟨7203373472812237024657715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4802248981874824683105143 7203373472812237024657715)
      ·
        refine ⟨10805060209218355536986573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7203373472812237024657715 10805060209218355536986573)
        ·
          refine ⟨4051897578456883326369965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10805060209218355536986573 4051897578456883326369965)
          ·
            refine ⟨1519461591921331247388737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4051897578456883326369965 1519461591921331247388737)
            ·
              refine ⟨1139596193940998435541553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1519461591921331247388737 1139596193940998435541553)
              ·
                refine ⟨854697145455748826656165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1139596193940998435541553 854697145455748826656165)
                ·
                  refine ⟨160255714772952904998031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854697145455748826656165 160255714772952904998031)
                  ·
                    rfl

theorem cell20_351109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_351109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351109 prefixEnd_351109 := by exact prefixLift 351109
  have htrace : WordTrace (prefixWord ++ tailWord_351109) baseStart_351109 baseEnd_351109 := by
    simpa [prefixWord, tailWord_351109, baseEnd_351109] using wordTrace_append hprefix tailTrace_351109
  have hstable : (prefixWord ++ tailWord_351109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351109).length < 2 ^ (prefixWord ++ tailWord_351109).sum := by decide
  have hdescent : baseEnd_351109 < baseStart_351109 := by decide
  rcases family_descends (prefixWord ++ tailWord_351109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351112 : List Nat := [2, 1, 3, 3, 2, 3, 2, 4]
def baseStart_351112 : Nat := 118140960795 + 351112 * 2 ^ 59
def prefixEnd_351112 : Nat := 4983230072969 + 3 ^ 40 * 351112 * 2
def baseEnd_351112 : Nat := 53419028018232742632673

theorem tailTrace_351112 : CollatzResearch.WordTrace tailWord_351112 prefixEnd_351112 53419028018232742632673 := by
  unfold tailWord_351112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403053351994332000319795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8537404469325776000426393 6403053351994332000319795)
  ·
    refine ⟨9604580027991498000479693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6403053351994332000319795 9604580027991498000479693)
    ·
      refine ⟨3601717510496811750179885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9604580027991498000479693 3601717510496811750179885)
      ·
        refine ⟨1350644066436304406317457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3601717510496811750179885 1350644066436304406317457)
        ·
          refine ⟨1012983049827228304738093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350644066436304406317457 1012983049827228304738093)
          ·
            refine ⟨379868643685210614276785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1012983049827228304738093 379868643685210614276785)
            ·
              refine ⟨284901482763907960707589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379868643685210614276785 284901482763907960707589)
              ·
                refine ⟨53419028018232742632673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284901482763907960707589 53419028018232742632673)
                ·
                  rfl

theorem cell20_351112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 4].length) (baseStart_351112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351112 prefixEnd_351112 := by exact prefixLift 351112
  have htrace : WordTrace (prefixWord ++ tailWord_351112) baseStart_351112 baseEnd_351112 := by
    simpa [prefixWord, tailWord_351112, baseEnd_351112] using wordTrace_append hprefix tailTrace_351112
  have hstable : (prefixWord ++ tailWord_351112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351112).length < 2 ^ (prefixWord ++ tailWord_351112).sum := by decide
  have hdescent : baseEnd_351112 < baseStart_351112 := by decide
  rcases family_descends (prefixWord ++ tailWord_351112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351140 : List Nat := [2, 3, 1, 2, 1, 2, 2, 4, 3]
def baseStart_351140 : Nat := 118140960795 + 351140 * 2 ^ 59
def prefixEnd_351140 : Nat := 4983230072969 + 3 ^ 40 * 351140 * 2
def baseEnd_351140 : Nat := 160269864017654574964571

theorem tailTrace_351140 : CollatzResearch.WordTrace tailWord_351140 prefixEnd_351140 160269864017654574964571 := by
  unfold tailWord_351140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6403563973943612391329437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8538085298591483188439249 6403563973943612391329437)
  ·
    refine ⟨2401336490228854646748539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6403563973943612391329437 2401336490228854646748539)
    ·
      refine ⟨3602004735343281970122809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2401336490228854646748539 3602004735343281970122809)
      ·
        refine ⟨2701503551507461477592107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3602004735343281970122809 2701503551507461477592107)
        ·
          refine ⟨4052255327261192216388161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701503551507461477592107 4052255327261192216388161)
          ·
            refine ⟨3039191495445894162291121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4052255327261192216388161 3039191495445894162291121)
            ·
              refine ⟨2279393621584420621718341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039191495445894162291121 2279393621584420621718341)
              ·
                refine ⟨427386304047078866572189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2279393621584420621718341 427386304047078866572189)
                ·
                  refine ⟨160269864017654574964571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427386304047078866572189 160269864017654574964571)
                  ·
                    rfl

theorem cell20_351140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 4, 3].length) (baseStart_351140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351140 prefixEnd_351140 := by exact prefixLift 351140
  have htrace : WordTrace (prefixWord ++ tailWord_351140) baseStart_351140 baseEnd_351140 := by
    simpa [prefixWord, tailWord_351140, baseEnd_351140] using wordTrace_append hprefix tailTrace_351140
  have hstable : (prefixWord ++ tailWord_351140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351140).length < 2 ^ (prefixWord ++ tailWord_351140).sum := by decide
  have hdescent : baseEnd_351140 < baseStart_351140 := by decide
  rcases family_descends (prefixWord ++ tailWord_351140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351143 : List Nat := [1, 1, 6, 1, 3, 2, 1, 1, 4]
def baseStart_351143 : Nat := 118140960795 + 351143 * 2 ^ 59
def prefixEnd_351143 : Nat := 4983230072969 + 3 ^ 40 * 351143 * 2
def baseEnd_351143 : Nat := 160271233299399897864559

theorem tailTrace_351143 : CollatzResearch.WordTrace tailWord_351143 prefixEnd_351143 160271233299399897864559 := by
  unfold tailWord_351143
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807237366876356295018083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8538158244584237530012055 12807237366876356295018083)
  ·
    refine ⟨19210856050314534442527125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12807237366876356295018083 19210856050314534442527125)
    ·
      refine ⟨900508877358493801993459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19210856050314534442527125 900508877358493801993459)
      ·
        refine ⟨1350763316037740702990189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900508877358493801993459 1350763316037740702990189)
        ·
          refine ⟨506536243514152763621321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1350763316037740702990189 506536243514152763621321)
          ·
            refine ⟨379902182635614572715991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 506536243514152763621321 379902182635614572715991)
            ·
              refine ⟨569853273953421859073987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379902182635614572715991 569853273953421859073987)
              ·
                refine ⟨854779910930132788610981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569853273953421859073987 854779910930132788610981)
                ·
                  refine ⟨160271233299399897864559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 854779910930132788610981 160271233299399897864559)
                  ·
                    rfl

theorem cell20_351143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_351143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351143 prefixEnd_351143 := by exact prefixLift 351143
  have htrace : WordTrace (prefixWord ++ tailWord_351143) baseStart_351143 baseEnd_351143 := by
    simpa [prefixWord, tailWord_351143, baseEnd_351143] using wordTrace_append hprefix tailTrace_351143
  have hstable : (prefixWord ++ tailWord_351143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351143).length < 2 ^ (prefixWord ++ tailWord_351143).sum := by decide
  have hdescent : baseEnd_351143 < baseStart_351143 := by decide
  rcases family_descends (prefixWord ++ tailWord_351143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351153 : List Nat := [1, 2, 2, 4, 4, 1, 2, 1, 3]
def baseStart_351153 : Nat := 118140960795 + 351153 * 2 ^ 59
def prefixEnd_351153 : Nat := 4983230072969 + 3 ^ 40 * 351153 * 2
def baseEnd_351153 : Nat := 160275797571884307531185

theorem tailTrace_351153 : CollatzResearch.WordTrace tailWord_351153 prefixEnd_351153 160275797571884307531185 := by
  unfold tailWord_351153
  simp only [CollatzResearch.WordTrace]
  refine ⟨12807602096840128002882113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8538401397893418668588075 12807602096840128002882113)
  ·
    refine ⟨9605701572630096002161585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12807602096840128002882113 9605701572630096002161585)
    ·
      refine ⟨7204276179472572001621189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9605701572630096002161585 7204276179472572001621189)
      ·
        refine ⟨1350801783651107250303973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7204276179472572001621189 1350801783651107250303973)
        ·
          refine ⟨253275334434582609431995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1350801783651107250303973 253275334434582609431995)
          ·
            refine ⟨379913001651873914147993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253275334434582609431995 379913001651873914147993)
            ·
              refine ⟨284934751238905435610995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379913001651873914147993 284934751238905435610995)
              ·
                refine ⟨427402126858358153416493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284934751238905435610995 427402126858358153416493)
                ·
                  refine ⟨160275797571884307531185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427402126858358153416493 160275797571884307531185)
                  ·
                    rfl

theorem cell20_351153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_351153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351153 prefixEnd_351153 := by exact prefixLift 351153
  have htrace : WordTrace (prefixWord ++ tailWord_351153) baseStart_351153 baseEnd_351153 := by
    simpa [prefixWord, tailWord_351153, baseEnd_351153] using wordTrace_append hprefix tailTrace_351153
  have hstable : (prefixWord ++ tailWord_351153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351153).length < 2 ^ (prefixWord ++ tailWord_351153).sum := by decide
  have hdescent : baseEnd_351153 < baseStart_351153 := by decide
  rcases family_descends (prefixWord ++ tailWord_351153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351205 : List Nat := [1, 3, 1, 6, 2, 1, 1, 5]
def baseStart_351205 : Nat := 118140960795 + 351205 * 2 ^ 59
def prefixEnd_351205 : Nat := 4983230072969 + 3 ^ 40 * 351205 * 2
def baseEnd_351205 : Nat := 53433177262934412599213

theorem tailTrace_351205 : CollatzResearch.WordTrace tailWord_351205 prefixEnd_351205 53433177262934412599213 := by
  unfold tailWord_351205
  simp only [CollatzResearch.WordTrace]
  refine ⟨12809498692651740883775069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8539665795101160589183379 12809498692651740883775069)
  ·
    refine ⟨4803562009744402831415651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12809498692651740883775069 4803562009744402831415651)
    ·
      refine ⟨7205343014616604247123477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4803562009744402831415651 7205343014616604247123477)
      ·
        refine ⟨337750453810153324083913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7205343014616604247123477 337750453810153324083913)
        ·
          refine ⟨253312840357614993062935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337750453810153324083913 253312840357614993062935)
          ·
            refine ⟨379969260536422489594403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253312840357614993062935 379969260536422489594403)
            ·
              refine ⟨569953890804633734391605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379969260536422489594403 569953890804633734391605)
              ·
                refine ⟨53433177262934412599213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 569953890804633734391605 53433177262934412599213)
                ·
                  rfl

theorem cell20_351205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 5].length) (baseStart_351205 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351205 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351205 prefixEnd_351205 := by exact prefixLift 351205
  have htrace : WordTrace (prefixWord ++ tailWord_351205) baseStart_351205 baseEnd_351205 := by
    simpa [prefixWord, tailWord_351205, baseEnd_351205] using wordTrace_append hprefix tailTrace_351205
  have hstable : (prefixWord ++ tailWord_351205).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351205).length < 2 ^ (prefixWord ++ tailWord_351205).sum := by decide
  have hdescent : baseEnd_351205 < baseStart_351205 := by decide
  rcases family_descends (prefixWord ++ tailWord_351205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351237 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 5]
def baseStart_351237 : Nat := 118140960795 + 351237 * 2 ^ 59
def prefixEnd_351237 : Nat := 4983230072969 + 3 ^ 40 * 351237 * 2
def baseEnd_351237 : Nat := 160314137460753348730841

theorem tailTrace_351237 : CollatzResearch.WordTrace tailWord_351237 prefixEnd_351237 160314137460753348730841 := by
  unfold tailWord_351237
  simp only [CollatzResearch.WordTrace]
  refine ⟨12810665828535810348939965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8540443885690540232626643 12810665828535810348939965)
  ·
    refine ⟨4803999685700928880852487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12810665828535810348939965 4803999685700928880852487)
    ·
      refine ⟨7205999528551393321278731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4803999685700928880852487 7205999528551393321278731)
      ·
        refine ⟨10808999292827089981918097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7205999528551393321278731 10808999292827089981918097)
        ·
          refine ⟨8106749469620317486438573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10808999292827089981918097 8106749469620317486438573)
          ·
            refine ⟨3040031051107619057414465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8106749469620317486438573 3040031051107619057414465)
            ·
              refine ⟨2280023288330714293060849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3040031051107619057414465 2280023288330714293060849)
              ·
                refine ⟨1710017466248035719795637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2280023288330714293060849 1710017466248035719795637)
                ·
                  refine ⟨160314137460753348730841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1710017466248035719795637 160314137460753348730841)
                  ·
                    rfl

theorem cell20_351237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_351237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351237 prefixEnd_351237 := by exact prefixLift 351237
  have htrace : WordTrace (prefixWord ++ tailWord_351237) baseStart_351237 baseEnd_351237 := by
    simpa [prefixWord, tailWord_351237, baseEnd_351237] using wordTrace_append hprefix tailTrace_351237
  have hstable : (prefixWord ++ tailWord_351237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351237).length < 2 ^ (prefixWord ++ tailWord_351237).sum := by decide
  have hdescent : baseEnd_351237 < baseStart_351237 := by decide
  rcases family_descends (prefixWord ++ tailWord_351237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351240 : List Nat := [2, 1, 3, 2, 1, 3, 1, 5, 2]
def baseStart_351240 : Nat := 118140960795 + 351240 * 2 ^ 59
def prefixEnd_351240 : Nat := 4983230072969 + 3 ^ 40 * 351240 * 2
def baseEnd_351240 : Nat := 160315506742498671630829

theorem tailTrace_351240 : CollatzResearch.WordTrace tailWord_351240 prefixEnd_351240 160315506742498671630829 := by
  unfold tailWord_351240
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405387623762470930649587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8540516831683294574199449 6405387623762470930649587)
  ·
    refine ⟨9608081435643706395974381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6405387623762470930649587 9608081435643706395974381)
    ·
      refine ⟨3603030538366389898490393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9608081435643706395974381 3603030538366389898490393)
      ·
        refine ⟨2702272903774792423867795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3603030538366389898490393 2702272903774792423867795)
        ·
          refine ⟨4053409355662188635801693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702272903774792423867795 4053409355662188635801693)
          ·
            refine ⟨1520028508373320738425635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4053409355662188635801693 1520028508373320738425635)
            ·
              refine ⟨2280042762559981107638453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1520028508373320738425635 2280042762559981107638453)
              ·
                refine ⟨213754008989998228841105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2280042762559981107638453 213754008989998228841105)
                ·
                  refine ⟨160315506742498671630829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213754008989998228841105 160315506742498671630829)
                  ·
                    rfl

theorem cell20_351240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 2].length) (baseStart_351240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351240 prefixEnd_351240 := by exact prefixLift 351240
  have htrace : WordTrace (prefixWord ++ tailWord_351240) baseStart_351240 baseEnd_351240 := by
    simpa [prefixWord, tailWord_351240, baseEnd_351240] using wordTrace_append hprefix tailTrace_351240
  have hstable : (prefixWord ++ tailWord_351240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351240).length < 2 ^ (prefixWord ++ tailWord_351240).sum := by decide
  have hdescent : baseEnd_351240 < baseStart_351240 := by decide
  rcases family_descends (prefixWord ++ tailWord_351240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351302 : List Nat := [6, 1, 1, 1, 1, 4, 6]
def baseStart_351302 : Nat := 118140960795 + 351302 * 2 ^ 59
def prefixEnd_351302 : Nat := 4983230072969 + 3 ^ 40 * 351302 * 2
def baseEnd_351302 : Nat := 17815978359100223507101

theorem tailTrace_351302 : CollatzResearch.WordTrace tailWord_351302 prefixEnd_351302 17815978359100223507101 := by
  unfold tailWord_351302
  simp only [CollatzResearch.WordTrace]
  refine ⟨400407392915635201564255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8542024382200217633370773 400407392915635201564255)
  ·
    refine ⟨600611089373452802346383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400407392915635201564255 600611089373452802346383)
    ·
      refine ⟨900916634060179203519575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600611089373452802346383 900916634060179203519575)
      ·
        refine ⟨1351374951090268805279363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 900916634060179203519575 1351374951090268805279363)
        ·
          refine ⟨2027062426635403207919045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351374951090268805279363 2027062426635403207919045)
          ·
            refine ⟨380074204994138101484821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2027062426635403207919045 380074204994138101484821)
            ·
              refine ⟨17815978359100223507101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 380074204994138101484821 17815978359100223507101)
              ·
                rfl

theorem cell20_351302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 6].length) (baseStart_351302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351302 prefixEnd_351302 := by exact prefixLift 351302
  have htrace : WordTrace (prefixWord ++ tailWord_351302) baseStart_351302 baseEnd_351302 := by
    simpa [prefixWord, tailWord_351302, baseEnd_351302] using wordTrace_append hprefix tailTrace_351302
  have hstable : (prefixWord ++ tailWord_351302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351302).length < 2 ^ (prefixWord ++ tailWord_351302).sum := by decide
  have hdescent : baseEnd_351302 < baseStart_351302 := by decide
  rcases family_descends (prefixWord ++ tailWord_351302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351313 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 5]
def baseStart_351313 : Nat := 118140960795 + 351313 * 2 ^ 59
def prefixEnd_351313 : Nat := 4983230072969 + 3 ^ 40 * 351313 * 2
def baseEnd_351313 : Nat := 160348825931634862197197

theorem tailTrace_351313 : CollatzResearch.WordTrace tailWord_351313 prefixEnd_351313 160348825931634862197197 := by
  unfold tailWord_351313
  simp only [CollatzResearch.WordTrace]
  refine ⟨12813437776260475328706593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8542291850840316885804395 12813437776260475328706593)
  ·
    refine ⟨9610078332195356496529945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12813437776260475328706593 9610078332195356496529945)
    ·
      refine ⟨7207558749146517372397459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9610078332195356496529945 7207558749146517372397459)
      ·
        refine ⟨10811338123719776058596189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7207558749146517372397459 10811338123719776058596189)
        ·
          refine ⟨4054251796394916021973571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10811338123719776058596189 4054251796394916021973571)
          ·
            refine ⟨6081377694592374032960357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054251796394916021973571 6081377694592374032960357)
            ·
              refine ⟨1140258317736070131180067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6081377694592374032960357 1140258317736070131180067)
              ·
                refine ⟨1710387476604105196770101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1140258317736070131180067 1710387476604105196770101)
                ·
                  refine ⟨160348825931634862197197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1710387476604105196770101 160348825931634862197197)
                  ·
                    rfl

theorem cell20_351313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 5].length) (baseStart_351313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351313 prefixEnd_351313 := by exact prefixLift 351313
  have htrace : WordTrace (prefixWord ++ tailWord_351313) baseStart_351313 baseEnd_351313 := by
    simpa [prefixWord, tailWord_351313, baseEnd_351313] using wordTrace_append hprefix tailTrace_351313
  have hstable : (prefixWord ++ tailWord_351313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351313).length < 2 ^ (prefixWord ++ tailWord_351313).sum := by decide
  have hdescent : baseEnd_351313 < baseStart_351313 := by decide
  rcases family_descends (prefixWord ++ tailWord_351313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351316 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 2]
def baseStart_351316 : Nat := 118140960795 + 351316 * 2 ^ 59
def prefixEnd_351316 : Nat := 4983230072969 + 3 ^ 40 * 351316 * 2
def baseEnd_351316 : Nat := 160350195213380185097185

theorem tailTrace_351316 : CollatzResearch.WordTrace tailWord_351316 prefixEnd_351316 160350195213380185097185 := by
  unfold tailWord_351316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6406773597624803420532901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8542364796833071227377201 6406773597624803420532901)
  ·
    refine ⟨1201270049554650641349919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6406773597624803420532901 1201270049554650641349919)
    ·
      refine ⟨1801905074331975962024879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1201270049554650641349919 1801905074331975962024879)
      ·
        refine ⟨2702857611497963943037319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801905074331975962024879 2702857611497963943037319)
        ·
          refine ⟨4054286417246945914555979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2702857611497963943037319 4054286417246945914555979)
          ·
            refine ⟨6081429625870418871833969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4054286417246945914555979 6081429625870418871833969)
            ·
              refine ⟨4561072219402814153875477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6081429625870418871833969 4561072219402814153875477)
              ·
                refine ⟨213800260284506913462913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4561072219402814153875477 213800260284506913462913)
                ·
                  refine ⟨160350195213380185097185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213800260284506913462913 160350195213380185097185)
                  ·
                    rfl

theorem cell20_351316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_351316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351316 prefixEnd_351316 := by exact prefixLift 351316
  have htrace : WordTrace (prefixWord ++ tailWord_351316) baseStart_351316 baseEnd_351316 := by
    simpa [prefixWord, tailWord_351316, baseEnd_351316] using wordTrace_append hprefix tailTrace_351316
  have hstable : (prefixWord ++ tailWord_351316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351316).length < 2 ^ (prefixWord ++ tailWord_351316).sum := by decide
  have hdescent : baseEnd_351316 < baseStart_351316 := by decide
  rcases family_descends (prefixWord ++ tailWord_351316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351365 : List Nat := [1, 3, 1, 1, 14]
def baseStart_351365 : Nat := 118140960795 + 351365 * 2 ^ 59
def prefixEnd_351365 : Nat := 4983230072969 + 3 ^ 40 * 351365 * 2
def baseEnd_351365 : Nat := 1979908149982145585971

theorem tailTrace_351365 : CollatzResearch.WordTrace tailWord_351365 prefixEnd_351365 1979908149982145585971 := by
  unfold tailWord_351365
  simp only [CollatzResearch.WordTrace]
  refine ⟨12815334372072088209599549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8543556248048058806399699 12815334372072088209599549)
  ·
    refine ⟨4805750389527033078599831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12815334372072088209599549 4805750389527033078599831)
    ·
      refine ⟨7208625584290549617899747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4805750389527033078599831 7208625584290549617899747)
      ·
        refine ⟨10812938376435824426849621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7208625584290549617899747 10812938376435824426849621)
        ·
          refine ⟨1979908149982145585971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 10812938376435824426849621 1979908149982145585971)
          ·
            rfl

theorem cell20_351365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 14].length) (baseStart_351365 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351365 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351365 prefixEnd_351365 := by exact prefixLift 351365
  have htrace : WordTrace (prefixWord ++ tailWord_351365) baseStart_351365 baseEnd_351365 := by
    simpa [prefixWord, tailWord_351365, baseEnd_351365] using wordTrace_append hprefix tailTrace_351365
  have hstable : (prefixWord ++ tailWord_351365).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351365).length < 2 ^ (prefixWord ++ tailWord_351365).sum := by decide
  have hdescent : baseEnd_351365 < baseStart_351365 := by decide
  rcases family_descends (prefixWord ++ tailWord_351365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351409 : List Nat := [1, 2, 2, 5, 1, 2, 2, 3, 2]
def baseStart_351409 : Nat := 118140960795 + 351409 * 2 ^ 59
def prefixEnd_351409 : Nat := 4983230072969 + 3 ^ 40 * 351409 * 2
def baseEnd_351409 : Nat := 160392642947485194996805

theorem tailTrace_351409 : CollatzResearch.WordTrace tailWord_351409 prefixEnd_351409 160392642947485194996805 := by
  unfold tailWord_351409
  simp only [CollatzResearch.WordTrace]
  refine ⟨12816939183912683724201281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8544626122608455816134187 12816939183912683724201281)
  ·
    refine ⟨9612704387934512793150961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12816939183912683724201281 9612704387934512793150961)
    ·
      refine ⟨7209528290950884594863221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9612704387934512793150961 7209528290950884594863221)
      ·
        refine ⟨675893277276645430768427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7209528290950884594863221 675893277276645430768427)
        ·
          refine ⟨1013839915914968146152641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675893277276645430768427 1013839915914968146152641)
          ·
            refine ⟨760379936936226109614481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013839915914968146152641 760379936936226109614481)
            ·
              refine ⟨570284952702169582210861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760379936936226109614481 570284952702169582210861)
              ·
                refine ⟨213856857263313593329073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570284952702169582210861 213856857263313593329073)
                ·
                  refine ⟨160392642947485194996805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213856857263313593329073 160392642947485194996805)
                  ·
                    rfl

theorem cell20_351409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_351409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351409 prefixEnd_351409 := by exact prefixLift 351409
  have htrace : WordTrace (prefixWord ++ tailWord_351409) baseStart_351409 baseEnd_351409 := by
    simpa [prefixWord, tailWord_351409, baseEnd_351409] using wordTrace_append hprefix tailTrace_351409
  have hstable : (prefixWord ++ tailWord_351409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351409).length < 2 ^ (prefixWord ++ tailWord_351409).sum := by decide
  have hdescent : baseEnd_351409 < baseStart_351409 := by decide
  rcases family_descends (prefixWord ++ tailWord_351409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351420 : List Nat := [2, 2, 2, 3, 2, 2, 7]
def baseStart_351420 : Nat := 118140960795 + 351420 * 2 ^ 59
def prefixEnd_351420 : Nat := 4983230072969 + 3 ^ 40 * 351420 * 2
def baseEnd_351420 : Nat := 17821962627468671736677

theorem tailTrace_351420 : CollatzResearch.WordTrace tailWord_351420 prefixEnd_351420 17821962627468671736677 := by
  unfold tailWord_351420
  simp only [CollatzResearch.WordTrace]
  refine ⟨6408670193436416301425857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8544893591248555068567809 6408670193436416301425857)
  ·
    refine ⟨4806502645077312226069393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6408670193436416301425857 4806502645077312226069393)
    ·
      refine ⟨3604876983807984169552045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4806502645077312226069393 3604876983807984169552045)
      ·
        refine ⟨1351828868927994063582017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3604876983807984169552045 1351828868927994063582017)
        ·
          refine ⟨1013871651695995547686513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1351828868927994063582017 1013871651695995547686513)
          ·
            refine ⟨760403738771996660764885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1013871651695995547686513 760403738771996660764885)
            ·
              refine ⟨17821962627468671736677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 760403738771996660764885 17821962627468671736677)
              ·
                rfl

theorem cell20_351420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 7].length) (baseStart_351420 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351420 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351420 prefixEnd_351420 := by exact prefixLift 351420
  have htrace : WordTrace (prefixWord ++ tailWord_351420) baseStart_351420 baseEnd_351420 := by
    simpa [prefixWord, tailWord_351420, baseEnd_351420] using wordTrace_append hprefix tailTrace_351420
  have hstable : (prefixWord ++ tailWord_351420).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351420).length < 2 ^ (prefixWord ++ tailWord_351420).sum := by decide
  have hdescent : baseEnd_351420 < baseStart_351420 := by decide
  rcases family_descends (prefixWord ++ tailWord_351420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351426 : List Nat := [3, 5, 1, 1, 2, 1, 2, 1, 4]
def baseStart_351426 : Nat := 118140960795 + 351426 * 2 ^ 59
def prefixEnd_351426 : Nat := 4983230072969 + 3 ^ 40 * 351426 * 2
def baseEnd_351426 : Nat := 160400402210708691430069

theorem tailTrace_351426 : CollatzResearch.WordTrace tailWord_351426 prefixEnd_351426 160400402210708691430069 := by
  unfold tailWord_351426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204389806212773906892533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8545039483234063751713421 3204389806212773906892533)
  ·
    refine ⟨300411544332447553771175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3204389806212773906892533 300411544332447553771175)
    ·
      refine ⟨450617316498671330656763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300411544332447553771175 450617316498671330656763)
      ·
        refine ⟨675925974748006995985145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450617316498671330656763 675925974748006995985145)
        ·
          refine ⟨506944481061005246988859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675925974748006995985145 506944481061005246988859)
          ·
            refine ⟨760416721591507870483289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506944481061005246988859 760416721591507870483289)
            ·
              refine ⟨570312541193630902862467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760416721591507870483289 570312541193630902862467)
              ·
                refine ⟨855468811790446354293701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570312541193630902862467 855468811790446354293701)
                ·
                  refine ⟨160400402210708691430069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855468811790446354293701 160400402210708691430069)
                  ·
                    rfl

theorem cell20_351426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_351426 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351426 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351426 prefixEnd_351426 := by exact prefixLift 351426
  have htrace : WordTrace (prefixWord ++ tailWord_351426) baseStart_351426 baseEnd_351426 := by
    simpa [prefixWord, tailWord_351426, baseEnd_351426] using wordTrace_append hprefix tailTrace_351426
  have hstable : (prefixWord ++ tailWord_351426).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351426).length < 2 ^ (prefixWord ++ tailWord_351426).sum := by decide
  have hdescent : baseEnd_351426 < baseStart_351426 := by decide
  rcases family_descends (prefixWord ++ tailWord_351426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351427 : List Nat := [1, 1, 1, 3, 1, 1, 1, 8, 3]
def baseStart_351427 : Nat := 118140960795 + 351427 * 2 ^ 59
def prefixEnd_351427 : Nat := 4983230072969 + 3 ^ 40 * 351427 * 2
def baseEnd_351427 : Nat := 160400858637957132396731

theorem tailTrace_351427 : CollatzResearch.WordTrace tailWord_351427 prefixEnd_351427 160400858637957132396731 := by
  unfold tailWord_351427
  simp only [CollatzResearch.WordTrace]
  refine ⟨12817595697847472798356535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8545063798564981865571023 12817595697847472798356535)
  ·
    refine ⟨19226393546771209197534803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12817595697847472798356535 19226393546771209197534803)
    ·
      refine ⟨28839590320156813796302205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19226393546771209197534803 28839590320156813796302205)
      ·
        refine ⟨10814846370058805173613327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28839590320156813796302205 10814846370058805173613327)
        ·
          refine ⟨16222269555088207760419991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10814846370058805173613327 16222269555088207760419991)
          ·
            refine ⟨24333404332632311640629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16222269555088207760419991 24333404332632311640629987)
            ·
              refine ⟨36500106498948467460944981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24333404332632311640629987 36500106498948467460944981)
              ·
                refine ⟨427735623034552353057949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 36500106498948467460944981 427735623034552353057949)
                ·
                  refine ⟨160400858637957132396731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427735623034552353057949 160400858637957132396731)
                  ·
                    rfl

theorem cell20_351427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_351427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351427 prefixEnd_351427 := by exact prefixLift 351427
  have htrace : WordTrace (prefixWord ++ tailWord_351427) baseStart_351427 baseEnd_351427 := by
    simpa [prefixWord, tailWord_351427, baseEnd_351427] using wordTrace_append hprefix tailTrace_351427
  have hstable : (prefixWord ++ tailWord_351427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351427).length < 2 ^ (prefixWord ++ tailWord_351427).sum := by decide
  have hdescent : baseEnd_351427 < baseStart_351427 := by decide
  rcases family_descends (prefixWord ++ tailWord_351427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351441 : List Nat := [1, 2, 2, 1, 2, 2, 1, 9]
def baseStart_351441 : Nat := 118140960795 + 351441 * 2 ^ 59
def prefixEnd_351441 : Nat := 4983230072969 + 3 ^ 40 * 351441 * 2
def baseEnd_351441 : Nat := 53469082873145101976669

theorem tailTrace_351441 : CollatzResearch.WordTrace tailWord_351441 prefixEnd_351441 53469082873145101976669 := by
  unfold tailWord_351441
  simp only [CollatzResearch.WordTrace]
  refine ⟨12818106319796753189366177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8545404213197835459577451 12818106319796753189366177)
  ·
    refine ⟨9613579739847564892024633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12818106319796753189366177 9613579739847564892024633)
    ·
      refine ⟨7210184804885673669018475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9613579739847564892024633 7210184804885673669018475)
      ·
        refine ⟨10815277207328510503527713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7210184804885673669018475 10815277207328510503527713)
        ·
          refine ⟨8111457905496382877645785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10815277207328510503527713 8111457905496382877645785)
          ·
            refine ⟨6083593429122287158234339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8111457905496382877645785 6083593429122287158234339)
            ·
              refine ⟨9125390143683430737351509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6083593429122287158234339 9125390143683430737351509)
              ·
                refine ⟨53469082873145101976669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9125390143683430737351509 53469082873145101976669)
                ·
                  rfl

theorem cell20_351441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 9].length) (baseStart_351441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351441 prefixEnd_351441 := by exact prefixLift 351441
  have htrace : WordTrace (prefixWord ++ tailWord_351441) baseStart_351441 baseEnd_351441 := by
    simpa [prefixWord, tailWord_351441, baseEnd_351441] using wordTrace_append hprefix tailTrace_351441
  have hstable : (prefixWord ++ tailWord_351441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351441).length < 2 ^ (prefixWord ++ tailWord_351441).sum := by decide
  have hdescent : baseEnd_351441 < baseStart_351441 := by decide
  rcases family_descends (prefixWord ++ tailWord_351441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351468 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 2]
def baseStart_351468 : Nat := 118140960795 + 351468 * 2 ^ 59
def prefixEnd_351468 : Nat := 4983230072969 + 3 ^ 40 * 351468 * 2
def baseEnd_351468 : Nat := 160419572155143212029897

theorem tailTrace_351468 : CollatzResearch.WordTrace tailWord_351468 prefixEnd_351468 160419572155143212029897 := by
  unfold tailWord_351468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409545545349468400299529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8546060727132624533732705 6409545545349468400299529)
  ·
    refine ⟨4807159159012101300224647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6409545545349468400299529 4807159159012101300224647)
    ·
      refine ⟨7210738738518151950336971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4807159159012101300224647 7210738738518151950336971)
      ·
        refine ⟨10816108107777227925505457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7210738738518151950336971 10816108107777227925505457)
        ·
          refine ⟨8112081080832920944129093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10816108107777227925505457 8112081080832920944129093)
          ·
            refine ⟨1521015202656172677024205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8112081080832920944129093 1521015202656172677024205)
            ·
              refine ⟨570380700996064753884077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1521015202656172677024205 570380700996064753884077)
              ·
                refine ⟨213892762873524282706529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570380700996064753884077 213892762873524282706529)
                ·
                  refine ⟨160419572155143212029897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213892762873524282706529 160419572155143212029897)
                  ·
                    rfl

theorem cell20_351468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 2].length) (baseStart_351468 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351468 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351468 prefixEnd_351468 := by exact prefixLift 351468
  have htrace : WordTrace (prefixWord ++ tailWord_351468) baseStart_351468 baseEnd_351468 := by
    simpa [prefixWord, tailWord_351468, baseEnd_351468] using wordTrace_append hprefix tailTrace_351468
  have hstable : (prefixWord ++ tailWord_351468).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351468).length < 2 ^ (prefixWord ++ tailWord_351468).sum := by decide
  have hdescent : baseEnd_351468 < baseStart_351468 := by decide
  rcases family_descends (prefixWord ++ tailWord_351468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351489 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 4]
def baseStart_351489 : Nat := 118140960795 + 351489 * 2 ^ 59
def prefixEnd_351489 : Nat := 4983230072969 + 3 ^ 40 * 351489 * 2
def baseEnd_351489 : Nat := 160429157127360472329811

theorem tailTrace_351489 : CollatzResearch.WordTrace tailWord_351489 prefixEnd_351489 160429157127360472329811 := by
  unfold tailWord_351489
  simp only [CollatzResearch.WordTrace]
  refine ⟨12819857023622857387113521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8546571349081904924742347 12819857023622857387113521)
  ·
    refine ⟨9614892767717143040335141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12819857023622857387113521 9614892767717143040335141)
    ·
      refine ⟨1802792393946964320062839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9614892767717143040335141 1802792393946964320062839)
      ·
        refine ⟨2704188590920446480094259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1802792393946964320062839 2704188590920446480094259)
        ·
          refine ⟨4056282886380669720141389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2704188590920446480094259 4056282886380669720141389)
          ·
            refine ⟨1521106082392751145053021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4056282886380669720141389 1521106082392751145053021)
            ·
              refine ⟨570414780897281679394883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1521106082392751145053021 570414780897281679394883)
              ·
                refine ⟨855622171345922519092325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570414780897281679394883 855622171345922519092325)
                ·
                  refine ⟨160429157127360472329811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 855622171345922519092325 160429157127360472329811)
                  ·
                    rfl

theorem cell20_351489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_351489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351489 prefixEnd_351489 := by exact prefixLift 351489
  have htrace : WordTrace (prefixWord ++ tailWord_351489) baseStart_351489 baseEnd_351489 := by
    simpa [prefixWord, tailWord_351489, baseEnd_351489] using wordTrace_append hprefix tailTrace_351489
  have hstable : (prefixWord ++ tailWord_351489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351489).length < 2 ^ (prefixWord ++ tailWord_351489).sum := by decide
  have hdescent : baseEnd_351489 < baseStart_351489 := by decide
  rcases family_descends (prefixWord ++ tailWord_351489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351499 : List Nat := [1, 1, 1, 1, 5, 5, 2, 1, 3]
def baseStart_351499 : Nat := 118140960795 + 351499 * 2 ^ 59
def prefixEnd_351499 : Nat := 4983230072969 + 3 ^ 40 * 351499 * 2
def baseEnd_351499 : Nat := 160433721399844881996437

theorem tailTrace_351499 : CollatzResearch.WordTrace tailWord_351499 prefixEnd_351499 160433721399844881996437 := by
  unfold tailWord_351499
  simp only [CollatzResearch.WordTrace]
  refine ⟨12820221753586629094977551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8546814502391086063318367 12820221753586629094977551)
  ·
    refine ⟨19230332630379943642466327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12820221753586629094977551 19230332630379943642466327)
    ·
      refine ⟨28845498945569915463699491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19230332630379943642466327 28845498945569915463699491)
      ·
        refine ⟨43268248418354873195549237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28845498945569915463699491 43268248418354873195549237)
        ·
          refine ⟨4056398289220769362082741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43268248418354873195549237 4056398289220769362082741)
          ·
            refine ⟨380287339614447127695257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4056398289220769362082741 380287339614447127695257)
            ·
              refine ⟨285215504710835345771443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380287339614447127695257 285215504710835345771443)
              ·
                refine ⟨427823257066253018657165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285215504710835345771443 427823257066253018657165)
                ·
                  refine ⟨160433721399844881996437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427823257066253018657165 160433721399844881996437)
                  ·
                    rfl

theorem cell20_351499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_351499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351499 prefixEnd_351499 := by exact prefixLift 351499
  have htrace : WordTrace (prefixWord ++ tailWord_351499) baseStart_351499 baseEnd_351499 := by
    simpa [prefixWord, tailWord_351499, baseEnd_351499] using wordTrace_append hprefix tailTrace_351499
  have hstable : (prefixWord ++ tailWord_351499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351499).length < 2 ^ (prefixWord ++ tailWord_351499).sum := by decide
  have hdescent : baseEnd_351499 < baseStart_351499 := by decide
  rcases family_descends (prefixWord ++ tailWord_351499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351574 : List Nat := [5, 2, 3, 1, 1, 1, 2, 3, 2]
def baseStart_351574 : Nat := 118140960795 + 351574 * 2 ^ 59
def prefixEnd_351574 : Nat := 4983230072969 + 3 ^ 40 * 351574 * 2
def baseEnd_351574 : Nat := 160467953443477954496131

theorem tailTrace_351574 : CollatzResearch.WordTrace tailWord_351574 prefixEnd_351574 160467953443477954496131 := by
  unfold tailWord_351574
  simp only [CollatzResearch.WordTrace]
  refine ⟨801434826769682306497361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8548638152209944602638517 801434826769682306497361)
  ·
    refine ⟨601076120077261729873021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 801434826769682306497361 601076120077261729873021)
    ·
      refine ⟨225403545028973148702383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 601076120077261729873021 225403545028973148702383)
      ·
        refine ⟨338105317543459723053575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225403545028973148702383 338105317543459723053575)
        ·
          refine ⟨507157976315189584580363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338105317543459723053575 507157976315189584580363)
          ·
            refine ⟨760736964472784376870545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507157976315189584580363 760736964472784376870545)
            ·
              refine ⟨570552723354588282652909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760736964472784376870545 570552723354588282652909)
              ·
                refine ⟨213957271257970605994841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570552723354588282652909 213957271257970605994841)
                ·
                  refine ⟨160467953443477954496131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213957271257970605994841 160467953443477954496131)
                  ·
                    rfl

theorem cell20_351574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_351574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351574 prefixEnd_351574 := by exact prefixLift 351574
  have htrace : WordTrace (prefixWord ++ tailWord_351574) baseStart_351574 baseEnd_351574 := by
    simpa [prefixWord, tailWord_351574, baseEnd_351574] using wordTrace_append hprefix tailTrace_351574
  have hstable : (prefixWord ++ tailWord_351574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351574).length < 2 ^ (prefixWord ++ tailWord_351574).sum := by decide
  have hdescent : baseEnd_351574 < baseStart_351574 := by decide
  rcases family_descends (prefixWord ++ tailWord_351574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351592 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 3]
def baseStart_351592 : Nat := 118140960795 + 351592 * 2 ^ 59
def prefixEnd_351592 : Nat := 4983230072969 + 3 ^ 40 * 351592 * 2
def baseEnd_351592 : Nat := 160476169133949891896057

theorem tailTrace_351592 : CollatzResearch.WordTrace tailWord_351592 prefixEnd_351592 160476169133949891896057 := by
  unfold tailWord_351592
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411806871124852989056515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8549075828166470652075353 6411806871124852989056515)
  ·
    refine ⟨9617710306687279483584773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6411806871124852989056515 9617710306687279483584773)
    ·
      refine ⟨1803320682503864903172145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9617710306687279483584773 1803320682503864903172145)
      ·
        refine ⟨1352490511877898677379109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1803320682503864903172145 1352490511877898677379109)
        ·
          refine ⟨253591970977106002008583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1352490511877898677379109 253591970977106002008583)
          ·
            refine ⟨380387956465659003012875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253591970977106002008583 380387956465659003012875)
            ·
              refine ⟨570581934698488504519313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380387956465659003012875 570581934698488504519313)
              ·
                refine ⟨427936451023866378389485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570581934698488504519313 427936451023866378389485)
                ·
                  refine ⟨160476169133949891896057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427936451023866378389485 160476169133949891896057)
                  ·
                    rfl

theorem cell20_351592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 3].length) (baseStart_351592 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351592 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351592 prefixEnd_351592 := by exact prefixLift 351592
  have htrace : WordTrace (prefixWord ++ tailWord_351592) baseStart_351592 baseEnd_351592 := by
    simpa [prefixWord, tailWord_351592, baseEnd_351592] using wordTrace_append hprefix tailTrace_351592
  have hstable : (prefixWord ++ tailWord_351592).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351592).length < 2 ^ (prefixWord ++ tailWord_351592).sum := by decide
  have hdescent : baseEnd_351592 < baseStart_351592 := by decide
  rcases family_descends (prefixWord ++ tailWord_351592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351596 : List Nat := [2, 2, 1, 1, 5, 1, 3, 2, 3]
def baseStart_351596 : Nat := 118140960795 + 351596 * 2 ^ 59
def prefixEnd_351596 : Nat := 4983230072969 + 3 ^ 40 * 351596 * 2
def baseEnd_351596 : Nat := 160477994842943655762707

theorem tailTrace_351596 : CollatzResearch.WordTrace tailWord_351596 prefixEnd_351596 160477994842943655762707 := by
  unfold tailWord_351596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6411879817117607330629321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8549173089490143107505761 6411879817117607330629321)
  ·
    refine ⟨4808909862838205497971991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6411879817117607330629321 4808909862838205497971991)
    ·
      refine ⟨7213364794257308246957987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4808909862838205497971991 7213364794257308246957987)
      ·
        refine ⟨10820047191385962370436981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7213364794257308246957987 10820047191385962370436981)
        ·
          refine ⟨1014379424192433972228467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10820047191385962370436981 1014379424192433972228467)
          ·
            refine ⟨1521569136288650958342701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1014379424192433972228467 1521569136288650958342701)
            ·
              refine ⟨570588426108244109378513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1521569136288650958342701 570588426108244109378513)
              ·
                refine ⟨427941319581183082033885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 570588426108244109378513 427941319581183082033885)
                ·
                  refine ⟨160477994842943655762707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 427941319581183082033885 160477994842943655762707)
                  ·
                    rfl

theorem cell20_351596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_351596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351596 prefixEnd_351596 := by exact prefixLift 351596
  have htrace : WordTrace (prefixWord ++ tailWord_351596) baseStart_351596 baseEnd_351596 := by
    simpa [prefixWord, tailWord_351596, baseEnd_351596] using wordTrace_append hprefix tailTrace_351596
  have hstable : (prefixWord ++ tailWord_351596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351596).length < 2 ^ (prefixWord ++ tailWord_351596).sum := by decide
  have hdescent : baseEnd_351596 < baseStart_351596 := by decide
  rcases family_descends (prefixWord ++ tailWord_351596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351644 : List Nat := [2, 2, 3, 4, 2, 1, 6]
def baseStart_351644 : Nat := 118140960795 + 351644 * 2 ^ 59
def prefixEnd_351644 : Nat := 4983230072969 + 3 ^ 40 * 351644 * 2
def baseEnd_351644 : Nat := 17833322594540980240279

theorem tailTrace_351644 : CollatzResearch.WordTrace tailWord_351644 prefixEnd_351644 17833322594540980240279 := by
  unfold tailWord_351644
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412755169030659429502993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8550340225374212572670657 6412755169030659429502993)
  ·
    refine ⟨4809566376772994572127245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6412755169030659429502993 4809566376772994572127245)
    ·
      refine ⟨1803587391289872964547717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4809566376772994572127245 1803587391289872964547717)
      ·
        refine ⟨338172635866851180852697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1803587391289872964547717 338172635866851180852697)
        ·
          refine ⟨253629476900138385639523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338172635866851180852697 253629476900138385639523)
          ·
            refine ⟨380444215350207578459285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253629476900138385639523 380444215350207578459285)
            ·
              refine ⟨17833322594540980240279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 380444215350207578459285 17833322594540980240279)
              ·
                rfl

theorem cell20_351644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 6].length) (baseStart_351644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351644 prefixEnd_351644 := by exact prefixLift 351644
  have htrace : WordTrace (prefixWord ++ tailWord_351644) baseStart_351644 baseEnd_351644 := by
    simpa [prefixWord, tailWord_351644, baseEnd_351644] using wordTrace_append hprefix tailTrace_351644
  have hstable : (prefixWord ++ tailWord_351644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351644).length < 2 ^ (prefixWord ++ tailWord_351644).sum := by decide
  have hdescent : baseEnd_351644 < baseStart_351644 := by decide
  rcases family_descends (prefixWord ++ tailWord_351644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351655 : List Nat := [1, 1, 6, 1, 1, 1, 1, 3, 5]
def baseStart_351655 : Nat := 118140960795 + 351655 * 2 ^ 59
def prefixEnd_351655 : Nat := 4983230072969 + 3 ^ 40 * 351655 * 2
def baseEnd_351655 : Nat := 160504924050601672795799

theorem tailTrace_351655 : CollatzResearch.WordTrace tailWord_351655 prefixEnd_351655 160504924050601672795799 := by
  unfold tailWord_351655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12825911541021467737656419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8550607694014311825104279 12825911541021467737656419)
  ·
    refine ⟨19238867311532201606484629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12825911541021467737656419 19238867311532201606484629)
    ·
      refine ⟨901821905228071950303967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19238867311532201606484629 901821905228071950303967)
      ·
        refine ⟨1352732857842107925455951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 901821905228071950303967 1352732857842107925455951)
        ·
          refine ⟨2029099286763161888183927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1352732857842107925455951 2029099286763161888183927)
          ·
            refine ⟨3043648930144742832275891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2029099286763161888183927 3043648930144742832275891)
            ·
              refine ⟨4565473395217114248413837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3043648930144742832275891 4565473395217114248413837)
              ·
                refine ⟨1712052523206417843155189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4565473395217114248413837 1712052523206417843155189)
                ·
                  refine ⟨160504924050601672795799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1712052523206417843155189 160504924050601672795799)
                  ·
                    rfl

theorem cell20_351655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 5].length) (baseStart_351655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351655 prefixEnd_351655 := by exact prefixLift 351655
  have htrace : WordTrace (prefixWord ++ tailWord_351655) baseStart_351655 baseEnd_351655 := by
    simpa [prefixWord, tailWord_351655, baseEnd_351655] using wordTrace_append hprefix tailTrace_351655
  have hstable : (prefixWord ++ tailWord_351655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351655).length < 2 ^ (prefixWord ++ tailWord_351655).sum := by decide
  have hdescent : baseEnd_351655 < baseStart_351655 := by decide
  rcases family_descends (prefixWord ++ tailWord_351655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351672 : List Nat := [2, 1, 2, 1, 2, 2, 6, 1, 3]
def baseStart_351672 : Nat := 118140960795 + 351672 * 2 ^ 59
def prefixEnd_351672 : Nat := 4983230072969 + 3 ^ 40 * 351672 * 2
def baseEnd_351672 : Nat := 160512683313825169229063

theorem tailTrace_351672 : CollatzResearch.WordTrace tailWord_351672 prefixEnd_351672 160512683313825169229063 := by
  unfold tailWord_351672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6413265790979939820512635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8551021054639919760683513 6413265790979939820512635)
  ·
    refine ⟨9619898686469909730768953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6413265790979939820512635 9619898686469909730768953)
    ·
      refine ⟨7214924014852432298076715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9619898686469909730768953 7214924014852432298076715)
      ·
        refine ⟨10822386022278648447115073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7214924014852432298076715 10822386022278648447115073)
        ·
          refine ⟨8116789516708986335336305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10822386022278648447115073 8116789516708986335336305)
          ·
            refine ⟨6087592137531739751502229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8116789516708986335336305 6087592137531739751502229)
            ·
              refine ⟨285355881446800300851667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6087592137531739751502229 285355881446800300851667)
              ·
                refine ⟨428033822170200451277501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285355881446800300851667 428033822170200451277501)
                ·
                  refine ⟨160512683313825169229063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428033822170200451277501 160512683313825169229063)
                  ·
                    rfl

theorem cell20_351672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 1, 3].length) (baseStart_351672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351672 prefixEnd_351672 := by exact prefixLift 351672
  have htrace : WordTrace (prefixWord ++ tailWord_351672) baseStart_351672 baseEnd_351672 := by
    simpa [prefixWord, tailWord_351672, baseEnd_351672] using wordTrace_append hprefix tailTrace_351672
  have hstable : (prefixWord ++ tailWord_351672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351672).length < 2 ^ (prefixWord ++ tailWord_351672).sum := by decide
  have hdescent : baseEnd_351672 < baseStart_351672 := by decide
  rcases family_descends (prefixWord ++ tailWord_351672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351713 : List Nat := [1, 2, 3, 1, 2, 5, 2, 2, 2]
def baseStart_351713 : Nat := 118140960795 + 351713 * 2 ^ 59
def prefixEnd_351713 : Nat := 4983230072969 + 3 ^ 40 * 351713 * 2
def baseEnd_351713 : Nat := 160531396831011248862229

theorem tailTrace_351713 : CollatzResearch.WordTrace tailWord_351713 prefixEnd_351713 160531396831011248862229 := by
  unfold tailWord_351713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12828026974811343643267793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8552017983207562428845195 12828026974811343643267793)
  ·
    refine ⟨9621020231108507732450845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12828026974811343643267793 9621020231108507732450845)
    ·
      refine ⟨3607882586665690399669067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9621020231108507732450845 3607882586665690399669067)
      ·
        refine ⟨5411823879998535599503601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3607882586665690399669067 5411823879998535599503601)
        ·
          refine ⟨4058867909998901699627701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5411823879998535599503601 4058867909998901699627701)
          ·
            refine ⟨380518866562397034340097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4058867909998901699627701 380518866562397034340097)
            ·
              refine ⟨285389149921797775755073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380518866562397034340097 285389149921797775755073)
              ·
                refine ⟨214041862441348331816305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285389149921797775755073 214041862441348331816305)
                ·
                  refine ⟨160531396831011248862229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214041862441348331816305 160531396831011248862229)
                  ·
                    rfl

theorem cell20_351713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 2, 2, 2].length) (baseStart_351713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351713 prefixEnd_351713 := by exact prefixLift 351713
  have htrace : WordTrace (prefixWord ++ tailWord_351713) baseStart_351713 baseEnd_351713 := by
    simpa [prefixWord, tailWord_351713, baseEnd_351713] using wordTrace_append hprefix tailTrace_351713
  have hstable : (prefixWord ++ tailWord_351713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351713).length < 2 ^ (prefixWord ++ tailWord_351713).sum := by decide
  have hdescent : baseEnd_351713 < baseStart_351713 := by decide
  rcases family_descends (prefixWord ++ tailWord_351713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351738 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 4]
def baseStart_351738 : Nat := 118140960795 + 351738 * 2 ^ 59
def prefixEnd_351738 : Nat := 4983230072969 + 3 ^ 40 * 351738 * 2
def baseEnd_351738 : Nat := 160542807512222273028793

theorem tailTrace_351738 : CollatzResearch.WordTrace tailWord_351738 prefixEnd_351738 160542807512222273028793 := by
  unfold tailWord_351738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3207234699930193228231967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8552625866480515275285245 3207234699930193228231967)
  ·
    refine ⟨4810852049895289842347951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3207234699930193228231967 4810852049895289842347951)
    ·
      refine ⟨7216278074842934763521927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4810852049895289842347951 7216278074842934763521927)
      ·
        refine ⟨10824417112264402145282891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7216278074842934763521927 10824417112264402145282891)
        ·
          refine ⟨16236625668396603217924337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10824417112264402145282891 16236625668396603217924337)
          ·
            refine ⟨12177469251297452413443253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16236625668396603217924337 12177469251297452413443253)
            ·
              refine ⟨1141637742309136163760305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12177469251297452413443253 1141637742309136163760305)
              ·
                refine ⟨856228306731852122820229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1141637742309136163760305 856228306731852122820229)
                ·
                  refine ⟨160542807512222273028793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856228306731852122820229 160542807512222273028793)
                  ·
                    rfl

theorem cell20_351738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_351738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351738 prefixEnd_351738 := by exact prefixLift 351738
  have htrace : WordTrace (prefixWord ++ tailWord_351738) baseStart_351738 baseEnd_351738 := by
    simpa [prefixWord, tailWord_351738, baseEnd_351738] using wordTrace_append hprefix tailTrace_351738
  have hstable : (prefixWord ++ tailWord_351738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351738).length < 2 ^ (prefixWord ++ tailWord_351738).sum := by decide
  have hdescent : baseEnd_351738 < baseStart_351738 := by decide
  rcases family_descends (prefixWord ++ tailWord_351738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351800 : List Nat := [2, 1, 2, 1, 4, 2, 4, 4]
def baseStart_351800 : Nat := 118140960795 + 351800 * 2 ^ 59
def prefixEnd_351800 : Nat := 4983230072969 + 3 ^ 40 * 351800 * 2
def baseEnd_351800 : Nat := 53523702000541870987291

theorem tailTrace_351800 : CollatzResearch.WordTrace tailWord_351800 prefixEnd_351800 53523702000541870987291 := by
  unfold tailWord_351800
  simp only [CollatzResearch.WordTrace]
  refine ⟨6415600062748078750842427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8554133416997438334456569 6415600062748078750842427)
  ·
    refine ⟨9623400094122118126263641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6415600062748078750842427 9623400094122118126263641)
    ·
      refine ⟨7217550070591588594697731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9623400094122118126263641 7217550070591588594697731)
      ·
        refine ⟨10826325105887382892046597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7217550070591588594697731 10826325105887382892046597)
        ·
          refine ⟨2029935957353884292258737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10826325105887382892046597 2029935957353884292258737)
          ·
            refine ⟨1522451968015413219194053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2029935957353884292258737 1522451968015413219194053)
            ·
              refine ⟨285459744002889978598885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1522451968015413219194053 285459744002889978598885)
              ·
                refine ⟨53523702000541870987291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285459744002889978598885 53523702000541870987291)
                ·
                  rfl

theorem cell20_351800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_351800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351800 prefixEnd_351800 := by exact prefixLift 351800
  have htrace : WordTrace (prefixWord ++ tailWord_351800) baseStart_351800 baseEnd_351800 := by
    simpa [prefixWord, tailWord_351800, baseEnd_351800] using wordTrace_append hprefix tailTrace_351800
  have hstable : (prefixWord ++ tailWord_351800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351800).length < 2 ^ (prefixWord ++ tailWord_351800).sum := by decide
  have hdescent : baseEnd_351800 < baseStart_351800 := by decide
  rcases family_descends (prefixWord ++ tailWord_351800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351831 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 4]
def baseStart_351831 : Nat := 118140960795 + 351831 * 2 ^ 59
def prefixEnd_351831 : Nat := 4983230072969 + 3 ^ 40 * 351831 * 2
def baseEnd_351831 : Nat := 160585255246327282928413

theorem tailTrace_351831 : CollatzResearch.WordTrace tailWord_351831 prefixEnd_351831 160585255246327282928413 := by
  unfold tailWord_351831
  simp only [CollatzResearch.WordTrace]
  refine ⟨12832330788383849796063347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8554887192255899864042231 12832330788383849796063347)
  ·
    refine ⟨19248496182575774694095021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12832330788383849796063347 19248496182575774694095021)
    ·
      refine ⟨7218186068465915510285633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19248496182575774694095021 7218186068465915510285633)
      ·
        refine ⟨5413639551349436632714225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7218186068465915510285633 5413639551349436632714225)
        ·
          refine ⟨4060229663512077474535669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5413639551349436632714225 4060229663512077474535669)
          ·
            refine ⟨380646530954257263237719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4060229663512077474535669 380646530954257263237719)
            ·
              refine ⟨570969796431385894856579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380646530954257263237719 570969796431385894856579)
              ·
                refine ⟨856454694647078842284869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570969796431385894856579 856454694647078842284869)
                ·
                  refine ⟨160585255246327282928413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 856454694647078842284869 160585255246327282928413)
                  ·
                    rfl

theorem cell20_351831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 4].length) (baseStart_351831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351831 prefixEnd_351831 := by exact prefixLift 351831
  have htrace : WordTrace (prefixWord ++ tailWord_351831) baseStart_351831 baseEnd_351831 := by
    simpa [prefixWord, tailWord_351831, baseEnd_351831] using wordTrace_append hprefix tailTrace_351831
  have hstable : (prefixWord ++ tailWord_351831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351831).length < 2 ^ (prefixWord ++ tailWord_351831).sum := by decide
  have hdescent : baseEnd_351831 < baseStart_351831 := by decide
  rcases family_descends (prefixWord ++ tailWord_351831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351837 : List Nat := [1, 4, 4, 2, 1, 2, 2, 1, 3]
def baseStart_351837 : Nat := 118140960795 + 351837 * 2 ^ 59
def prefixEnd_351837 : Nat := 4983230072969 + 3 ^ 40 * 351837 * 2
def baseEnd_351837 : Nat := 160587993809817928728389

theorem tailTrace_351837 : CollatzResearch.WordTrace tailWord_351837 prefixEnd_351837 160587993809817928728389 := by
  unfold tailWord_351837
  simp only [CollatzResearch.WordTrace]
  refine ⟨12832549626362112820781765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8555033084241408547187843 12832549626362112820781765)
  ·
    refine ⟨2406103054942896153896581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12832549626362112820781765 2406103054942896153896581)
    ·
      refine ⟨451144322801793028855609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2406103054942896153896581 451144322801793028855609)
      ·
        refine ⟨338358242101344771641707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451144322801793028855609 338358242101344771641707)
        ·
          refine ⟨507537363152017157462561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338358242101344771641707 507537363152017157462561)
          ·
            refine ⟨380653022364012868096921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507537363152017157462561 380653022364012868096921)
            ·
              refine ⟨285489766773009651072691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380653022364012868096921 285489766773009651072691)
              ·
                refine ⟨428234650159514476609037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285489766773009651072691 428234650159514476609037)
                ·
                  refine ⟨160587993809817928728389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428234650159514476609037 160587993809817928728389)
                  ·
                    rfl

theorem cell20_351837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_351837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351837 prefixEnd_351837 := by exact prefixLift 351837
  have htrace : WordTrace (prefixWord ++ tailWord_351837) baseStart_351837 baseEnd_351837 := by
    simpa [prefixWord, tailWord_351837, baseEnd_351837] using wordTrace_append hprefix tailTrace_351837
  have hstable : (prefixWord ++ tailWord_351837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351837).length < 2 ^ (prefixWord ++ tailWord_351837).sum := by decide
  have hdescent : baseEnd_351837 < baseStart_351837 := by decide
  rcases family_descends (prefixWord ++ tailWord_351837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351866 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_351866 : Nat := 118140960795 + 351866 * 2 ^ 59
def prefixEnd_351866 : Nat := 4983230072969 + 3 ^ 40 * 351866 * 2
def baseEnd_351866 : Nat := 160601230200022716761603

theorem tailTrace_351866 : CollatzResearch.WordTrace tailWord_351866 prefixEnd_351866 160601230200022716761603 := by
  unfold tailWord_351866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3208401835814262693396863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8555738228838033849058301 3208401835814262693396863)
  ·
    refine ⟨4812602753721394040095295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3208401835814262693396863 4812602753721394040095295)
    ·
      refine ⟨7218904130582091060142943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4812602753721394040095295 7218904130582091060142943)
      ·
        refine ⟨10828356195873136590214415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7218904130582091060142943 10828356195873136590214415)
        ·
          refine ⟨16242534293809704885321623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10828356195873136590214415 16242534293809704885321623)
          ·
            refine ⟨24363801440714557327982435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16242534293809704885321623 24363801440714557327982435)
            ·
              refine ⟨36545702161071835991973653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24363801440714557327982435 36545702161071835991973653)
              ·
                refine ⟨1713079788800242312123765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36545702161071835991973653 1713079788800242312123765)
                ·
                  refine ⟨160601230200022716761603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1713079788800242312123765 160601230200022716761603)
                  ·
                    rfl

theorem cell20_351866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_351866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351866 prefixEnd_351866 := by exact prefixLift 351866
  have htrace : WordTrace (prefixWord ++ tailWord_351866) baseStart_351866 baseEnd_351866 := by
    simpa [prefixWord, tailWord_351866, baseEnd_351866] using wordTrace_append hprefix tailTrace_351866
  have hstable : (prefixWord ++ tailWord_351866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351866).length < 2 ^ (prefixWord ++ tailWord_351866).sum := by decide
  have hdescent : baseEnd_351866 < baseStart_351866 := by decide
  rcases family_descends (prefixWord ++ tailWord_351866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351876 : List Nat := [2, 3, 2, 1, 5, 7]
def baseStart_351876 : Nat := 118140960795 + 351876 * 2 ^ 59
def prefixEnd_351876 : Nat := 4983230072969 + 3 ^ 40 * 351876 * 2
def baseEnd_351876 : Nat := 5948362758241004682527

theorem tailTrace_351876 : CollatzResearch.WordTrace tailWord_351876 prefixEnd_351876 5948362758241004682527 := by
  unfold tailWord_351876
  simp only [CollatzResearch.WordTrace]
  refine ⟨6416986036610411240725741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8555981382147214987634321 6416986036610411240725741)
  ·
    refine ⟨2406369763728904215272153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6416986036610411240725741 2406369763728904215272153)
    ·
      refine ⟨1804777322796678161454115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2406369763728904215272153 1804777322796678161454115)
      ·
        refine ⟨2707165984195017242181173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1804777322796678161454115 2707165984195017242181173)
        ·
          refine ⟨253796811018282866454485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2707165984195017242181173 253796811018282866454485)
          ·
            refine ⟨5948362758241004682527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 253796811018282866454485 5948362758241004682527)
            ·
              rfl

theorem cell20_351876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 7].length) (baseStart_351876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351876 prefixEnd_351876 := by exact prefixLift 351876
  have htrace : WordTrace (prefixWord ++ tailWord_351876) baseStart_351876 baseEnd_351876 := by
    simpa [prefixWord, tailWord_351876, baseEnd_351876] using wordTrace_append hprefix tailTrace_351876
  have hstable : (prefixWord ++ tailWord_351876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351876).length < 2 ^ (prefixWord ++ tailWord_351876).sum := by decide
  have hdescent : baseEnd_351876 < baseStart_351876 := by decide
  rcases family_descends (prefixWord ++ tailWord_351876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351883 : List Nat := [1, 1, 1, 1, 4, 1, 6, 2, 3]
def baseStart_351883 : Nat := 118140960795 + 351883 * 2 ^ 59
def prefixEnd_351883 : Nat := 4983230072969 + 3 ^ 40 * 351883 * 2
def baseEnd_351883 : Nat := 160608989463246213194867

theorem tailTrace_351883 : CollatzResearch.WordTrace tailWord_351883 prefixEnd_351883 160608989463246213194867 := by
  unfold tailWord_351883
  simp only [CollatzResearch.WordTrace]
  refine ⟨12834227384195462676956303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8556151589463641784637535 12834227384195462676956303)
  ·
    refine ⟨19251341076293194015434455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12834227384195462676956303 19251341076293194015434455)
    ·
      refine ⟨28877011614439791023151683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19251341076293194015434455 28877011614439791023151683)
      ·
        refine ⟨43315517421659686534727525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28877011614439791023151683 43315517421659686534727525)
        ·
          refine ⟨8121659516561191225261411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43315517421659686534727525 8121659516561191225261411)
          ·
            refine ⟨12182489274841786837892117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8121659516561191225261411 12182489274841786837892117)
            ·
              refine ⟨571054184758208758026193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12182489274841786837892117 571054184758208758026193)
              ·
                refine ⟨428290638568656568519645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571054184758208758026193 428290638568656568519645)
                ·
                  refine ⟨160608989463246213194867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428290638568656568519645 160608989463246213194867)
                  ·
                    rfl

theorem cell20_351883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 2, 3].length) (baseStart_351883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351883 prefixEnd_351883 := by exact prefixLift 351883
  have htrace : WordTrace (prefixWord ++ tailWord_351883) baseStart_351883 baseEnd_351883 := by
    simpa [prefixWord, tailWord_351883, baseEnd_351883] using wordTrace_append hprefix tailTrace_351883
  have hstable : (prefixWord ++ tailWord_351883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351883).length < 2 ^ (prefixWord ++ tailWord_351883).sum := by decide
  have hdescent : baseEnd_351883 < baseStart_351883 := by decide
  rcases family_descends (prefixWord ++ tailWord_351883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351886 : List Nat := [4, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_351886 : Nat := 118140960795 + 351886 * 2 ^ 59
def prefixEnd_351886 : Nat := 4983230072969 + 3 ^ 40 * 351886 * 2
def baseEnd_351886 : Nat := 160610358744991536094855

theorem tailTrace_351886 : CollatzResearch.WordTrace tailWord_351886 prefixEnd_351886 160610358744991536094855 := by
  unfold tailWord_351886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604292100398074273664439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8556224535456396126210341 1604292100398074273664439)
  ·
    refine ⟨2406438150597111410496659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604292100398074273664439 2406438150597111410496659)
    ·
      refine ⟨3609657225895667115744989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2406438150597111410496659 3609657225895667115744989)
      ·
        refine ⟨1353621459710875168404371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3609657225895667115744989 1353621459710875168404371)
        ·
          refine ⟨2030432189566312752606557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353621459710875168404371 2030432189566312752606557)
          ·
            refine ⟨761412071087367282227459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2030432189566312752606557 761412071087367282227459)
            ·
              refine ⟨1142118106631050923341189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761412071087367282227459 1142118106631050923341189)
              ·
                refine ⟨214147144993322048126473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1142118106631050923341189 214147144993322048126473)
                ·
                  refine ⟨160610358744991536094855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214147144993322048126473 160610358744991536094855)
                  ·
                    rfl

theorem cell20_351886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_351886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351886 prefixEnd_351886 := by exact prefixLift 351886
  have htrace : WordTrace (prefixWord ++ tailWord_351886) baseStart_351886 baseEnd_351886 := by
    simpa [prefixWord, tailWord_351886, baseEnd_351886] using wordTrace_append hprefix tailTrace_351886
  have hstable : (prefixWord ++ tailWord_351886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351886).length < 2 ^ (prefixWord ++ tailWord_351886).sum := by decide
  have hdescent : baseEnd_351886 < baseStart_351886 := by decide
  rcases family_descends (prefixWord ++ tailWord_351886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351965 : List Nat := [1, 4, 3, 3, 2, 1, 2, 4]
def baseStart_351965 : Nat := 118140960795 + 351965 * 2 ^ 59
def prefixEnd_351965 : Nat := 4983230072969 + 3 ^ 40 * 351965 * 2
def baseEnd_351965 : Nat := 53548805499206124153733

theorem tailTrace_351965 : CollatzResearch.WordTrace tailWord_351965 prefixEnd_351965 53548805499206124153733 := by
  unfold tailWord_351965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837218169898390681441349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558145446598927120960899 12837218169898390681441349)
  ·
    refine ⟨2406978406855948252770253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12837218169898390681441349 2406978406855948252770253)
    ·
      refine ⟨902616902570980594788845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2406978406855948252770253 902616902570980594788845)
      ·
        refine ⟨338481338464117723045817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 902616902570980594788845 338481338464117723045817)
        ·
          refine ⟨253861003848088292284363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338481338464117723045817 253861003848088292284363)
          ·
            refine ⟨380791505772132438426545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253861003848088292284363 380791505772132438426545)
            ·
              refine ⟨285593629329099328819909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380791505772132438426545 285593629329099328819909)
              ·
                refine ⟨53548805499206124153733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285593629329099328819909 53548805499206124153733)
                ·
                  rfl

theorem cell20_351965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 4].length) (baseStart_351965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351965 prefixEnd_351965 := by exact prefixLift 351965
  have htrace : WordTrace (prefixWord ++ tailWord_351965) baseStart_351965 baseEnd_351965 := by
    simpa [prefixWord, tailWord_351965, baseEnd_351965] using wordTrace_append hprefix tailTrace_351965
  have hstable : (prefixWord ++ tailWord_351965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351965).length < 2 ^ (prefixWord ++ tailWord_351965).sum := by decide
  have hdescent : baseEnd_351965 < baseStart_351965 := by decide
  rcases family_descends (prefixWord ++ tailWord_351965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351969 : List Nat := [1, 2, 3, 1, 5, 2, 2, 4]
def baseStart_351969 : Nat := 118140960795 + 351969 * 2 ^ 59
def prefixEnd_351969 : Nat := 4983230072969 + 3 ^ 40 * 351969 * 2
def baseEnd_351969 : Nat := 53549414068870712109283

theorem tailTrace_351969 : CollatzResearch.WordTrace tailWord_351969 prefixEnd_351969 53549414068870712109283 := by
  unfold tailWord_351969
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837364061883899364586961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558242707922599576391307 12837364061883899364586961)
  ·
    refine ⟨9628023046412924523440221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12837364061883899364586961 9628023046412924523440221)
    ·
      refine ⟨3610508642404846696290083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9628023046412924523440221 3610508642404846696290083)
      ·
        refine ⟨5415762963607270044435125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3610508642404846696290083 5415762963607270044435125)
        ·
          refine ⟨507727777838181566665793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5415762963607270044435125 507727777838181566665793)
          ·
            refine ⟨380795833378636174999345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507727777838181566665793 380795833378636174999345)
            ·
              refine ⟨285596875033977131249509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380795833378636174999345 285596875033977131249509)
              ·
                refine ⟨53549414068870712109283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285596875033977131249509 53549414068870712109283)
                ·
                  rfl

theorem cell20_351969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 4].length) (baseStart_351969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351969 prefixEnd_351969 := by exact prefixLift 351969
  have htrace : WordTrace (prefixWord ++ tailWord_351969) baseStart_351969 baseEnd_351969 := by
    simpa [prefixWord, tailWord_351969, baseEnd_351969] using wordTrace_append hprefix tailTrace_351969
  have hstable : (prefixWord ++ tailWord_351969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351969).length < 2 ^ (prefixWord ++ tailWord_351969).sum := by decide
  have hdescent : baseEnd_351969 < baseStart_351969 := by decide
  rcases family_descends (prefixWord ++ tailWord_351969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351973 : List Nat := [1, 3, 1, 4, 1, 1, 3, 6]
def baseStart_351973 : Nat := 118140960795 + 351973 * 2 ^ 59
def prefixEnd_351973 : Nat := 4983230072969 + 3 ^ 40 * 351973 * 2
def baseEnd_351973 : Nat := 53550022638535300064833

theorem tailTrace_351973 : CollatzResearch.WordTrace tailWord_351973 prefixEnd_351973 53550022638535300064833 := by
  unfold tailWord_351973
  simp only [CollatzResearch.WordTrace]
  refine ⟨12837509953869408047732573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558339969246272031821715 12837509953869408047732573)
  ·
    refine ⟨4814066232701028017899715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12837509953869408047732573 4814066232701028017899715)
    ·
      refine ⟨7221099349051542026849573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814066232701028017899715 7221099349051542026849573)
      ·
        refine ⟨1353956127947164130034295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7221099349051542026849573 1353956127947164130034295)
        ·
          refine ⟨2030934191920746195051443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1353956127947164130034295 2030934191920746195051443)
          ·
            refine ⟨3046401287881119292577165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2030934191920746195051443 3046401287881119292577165)
            ·
              refine ⟨1142400482955419734716437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3046401287881119292577165 1142400482955419734716437)
              ·
                refine ⟨53550022638535300064833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1142400482955419734716437 53550022638535300064833)
                ·
                  rfl

theorem cell20_351973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 6].length) (baseStart_351973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351973 prefixEnd_351973 := by exact prefixLift 351973
  have htrace : WordTrace (prefixWord ++ tailWord_351973) baseStart_351973 baseEnd_351973 := by
    simpa [prefixWord, tailWord_351973, baseEnd_351973] using wordTrace_append hprefix tailTrace_351973
  have hstable : (prefixWord ++ tailWord_351973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351973).length < 2 ^ (prefixWord ++ tailWord_351973).sum := by decide
  have hdescent : baseEnd_351973 < baseStart_351973 := by decide
  rcases family_descends (prefixWord ++ tailWord_351973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351980 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_351980 : Nat := 118140960795 + 351980 * 2 ^ 59
def prefixEnd_351980 : Nat := 4983230072969 + 3 ^ 40 * 351980 * 2
def baseEnd_351980 : Nat := 160653262906344986961137

theorem tailTrace_351980 : CollatzResearch.WordTrace tailWord_351980 prefixEnd_351980 160653262906344986961137 := by
  unfold tailWord_351980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6418882632422024121618697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8558510176562698828824929 6418882632422024121618697)
  ·
    refine ⟨4814161974316518091214023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6418882632422024121618697 4814161974316518091214023)
    ·
      refine ⟨7221242961474777136821035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4814161974316518091214023 7221242961474777136821035)
      ·
        refine ⟨10831864442212165705231553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7221242961474777136821035 10831864442212165705231553)
        ·
          refine ⟨8123898331659124278923665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10831864442212165705231553 8123898331659124278923665)
          ·
            refine ⟨6092923748744343209192749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8123898331659124278923665 6092923748744343209192749)
            ·
              refine ⟨2284846405779128703447281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6092923748744343209192749 2284846405779128703447281)
              ·
                refine ⟨1713634804334346527585461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2284846405779128703447281 1713634804334346527585461)
                ·
                  refine ⟨160653262906344986961137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1713634804334346527585461 160653262906344986961137)
                  ·
                    rfl

theorem cell20_351980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_351980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351980 prefixEnd_351980 := by exact prefixLift 351980
  have htrace : WordTrace (prefixWord ++ tailWord_351980) baseStart_351980 baseEnd_351980 := by
    simpa [prefixWord, tailWord_351980, baseEnd_351980] using wordTrace_append hprefix tailTrace_351980
  have hstable : (prefixWord ++ tailWord_351980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351980).length < 2 ^ (prefixWord ++ tailWord_351980).sum := by decide
  have hdescent : baseEnd_351980 < baseStart_351980 := by decide
  rcases family_descends (prefixWord ++ tailWord_351980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351987 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 6]
def baseStart_351987 : Nat := 118140960795 + 351987 * 2 ^ 59
def prefixEnd_351987 : Nat := 4983230072969 + 3 ^ 40 * 351987 * 2
def baseEnd_351987 : Nat := 160656457897084073727775

theorem tailTrace_351987 : CollatzResearch.WordTrace tailWord_351987 prefixEnd_351987 160656457897084073727775 := by
  unfold tailWord_351987
  simp only [CollatzResearch.WordTrace]
  refine ⟨12838020575818688438742215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8558680383879125625828143 12838020575818688438742215)
  ·
    refine ⟨19257030863728032658113323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12838020575818688438742215 19257030863728032658113323)
    ·
      refine ⟨28885546295592048987169985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19257030863728032658113323 28885546295592048987169985)
      ·
        refine ⟨21664159721694036740377489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28885546295592048987169985 21664159721694036740377489)
        ·
          refine ⟨16248119791270527555283117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21664159721694036740377489 16248119791270527555283117)
          ·
            refine ⟨6093044921726447833231169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16248119791270527555283117 6093044921726447833231169)
            ·
              refine ⟨4569783691294835874923377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6093044921726447833231169 4569783691294835874923377)
              ·
                refine ⟨3427337768471126906192533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4569783691294835874923377 3427337768471126906192533)
                ·
                  refine ⟨160656457897084073727775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3427337768471126906192533 160656457897084073727775)
                  ·
                    rfl

theorem cell20_351987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 6].length) (baseStart_351987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351987 prefixEnd_351987 := by exact prefixLift 351987
  have htrace : WordTrace (prefixWord ++ tailWord_351987) baseStart_351987 baseEnd_351987 := by
    simpa [prefixWord, tailWord_351987, baseEnd_351987] using wordTrace_append hprefix tailTrace_351987
  have hstable : (prefixWord ++ tailWord_351987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351987).length < 2 ^ (prefixWord ++ tailWord_351987).sum := by decide
  have hdescent : baseEnd_351987 < baseStart_351987 := by decide
  rcases family_descends (prefixWord ++ tailWord_351987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351990 : List Nat := [5, 1, 1, 1, 1, 5, 6]
def baseStart_351990 : Nat := 118140960795 + 351990 * 2 ^ 59
def prefixEnd_351990 : Nat := 4983230072969 + 3 ^ 40 * 351990 * 2
def baseEnd_351990 : Nat := 17850869686536599625307

theorem tailTrace_351990 : CollatzResearch.WordTrace tailWord_351990 prefixEnd_351990 17850869686536599625307 := by
  unfold tailWord_351990
  simp only [CollatzResearch.WordTrace]
  refine ⟨802383124675488746943839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8558753329871879967400949 802383124675488746943839)
  ·
    refine ⟨1203574687013233120415759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 802383124675488746943839 1203574687013233120415759)
    ·
      refine ⟨1805362030519849680623639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1203574687013233120415759 1805362030519849680623639)
      ·
        refine ⟨2708043045779774520935459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1805362030519849680623639 2708043045779774520935459)
        ·
          refine ⟨4062064568669661781403189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708043045779774520935459 4062064568669661781403189)
          ·
            refine ⟨380818553312780792006549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4062064568669661781403189 380818553312780792006549)
            ·
              refine ⟨17850869686536599625307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 380818553312780792006549 17850869686536599625307)
              ·
                rfl

theorem cell20_351990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 6].length) (baseStart_351990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_351990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_351990 prefixEnd_351990 := by exact prefixLift 351990
  have htrace : WordTrace (prefixWord ++ tailWord_351990) baseStart_351990 baseEnd_351990 := by
    simpa [prefixWord, tailWord_351990, baseEnd_351990] using wordTrace_append hprefix tailTrace_351990
  have hstable : (prefixWord ++ tailWord_351990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351990).length < 2 ^ (prefixWord ++ tailWord_351990).sum := by decide
  have hdescent : baseEnd_351990 < baseStart_351990 := by decide
  rcases family_descends (prefixWord ++ tailWord_351990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352006 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 3]
def baseStart_352006 : Nat := 118140960795 + 352006 * 2 ^ 59
def prefixEnd_352006 : Nat := 4983230072969 + 3 ^ 40 * 352006 * 2
def baseEnd_352006 : Nat := 160665130014804452094365

theorem tailTrace_352006 : CollatzResearch.WordTrace tailWord_352006 prefixEnd_352006 160665130014804452094365 := by
  unfold tailWord_352006
  simp only [CollatzResearch.WordTrace]
  refine ⟨401209798835932958865121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8559142375166569789122581 401209798835932958865121)
  ·
    refine ⟨300907349126949719148841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 401209798835932958865121 300907349126949719148841)
    ·
      refine ⟨225680511845212289361631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300907349126949719148841 225680511845212289361631)
      ·
        refine ⟨338520767767818434042447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225680511845212289361631 338520767767818434042447)
        ·
          refine ⟨507781151651727651063671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338520767767818434042447 507781151651727651063671)
          ·
            refine ⟨761671727477591476595507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507781151651727651063671 761671727477591476595507)
            ·
              refine ⟨1142507591216387214893261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 761671727477591476595507 1142507591216387214893261)
              ·
                refine ⟨428440346706145205584973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1142507591216387214893261 428440346706145205584973)
                ·
                  refine ⟨160665130014804452094365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428440346706145205584973 160665130014804452094365)
                  ·
                    rfl

theorem cell20_352006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_352006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352006 prefixEnd_352006 := by exact prefixLift 352006
  have htrace : WordTrace (prefixWord ++ tailWord_352006) baseStart_352006 baseEnd_352006 := by
    simpa [prefixWord, tailWord_352006, baseEnd_352006] using wordTrace_append hprefix tailTrace_352006
  have hstable : (prefixWord ++ tailWord_352006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352006).length < 2 ^ (prefixWord ++ tailWord_352006).sum := by decide
  have hdescent : baseEnd_352006 < baseStart_352006 := by decide
  rcases family_descends (prefixWord ++ tailWord_352006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352014 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_352014 : Nat := 118140960795 + 352014 * 2 ^ 59
def prefixEnd_352014 : Nat := 4983230072969 + 3 ^ 40 * 352014 * 2
def baseEnd_352014 : Nat := 160668781432791979827665

theorem tailTrace_352014 : CollatzResearch.WordTrace tailWord_352014 prefixEnd_352014 160668781432791979827665 := by
  unfold tailWord_352014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1604875668340109006246887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8559336897813914699983397 1604875668340109006246887)
  ·
    refine ⟨2407313502510163509370331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1604875668340109006246887 2407313502510163509370331)
    ·
      refine ⟨3610970253765245264055497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407313502510163509370331 3610970253765245264055497)
      ·
        refine ⟨2708227690323933948041623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3610970253765245264055497 2708227690323933948041623)
        ·
          refine ⟨4062341535485900922062435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708227690323933948041623 4062341535485900922062435)
          ·
            refine ⟨6093512303228851383093653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4062341535485900922062435 6093512303228851383093653)
            ·
              refine ⟨285633389213852408582515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6093512303228851383093653 285633389213852408582515)
              ·
                refine ⟨428450083820778612873773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285633389213852408582515 428450083820778612873773)
                ·
                  refine ⟨160668781432791979827665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428450083820778612873773 160668781432791979827665)
                  ·
                    rfl

theorem cell20_352014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_352014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352014 prefixEnd_352014 := by exact prefixLift 352014
  have htrace : WordTrace (prefixWord ++ tailWord_352014) baseStart_352014 baseEnd_352014 := by
    simpa [prefixWord, tailWord_352014, baseEnd_352014] using wordTrace_append hprefix tailTrace_352014
  have hstable : (prefixWord ++ tailWord_352014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352014).length < 2 ^ (prefixWord ++ tailWord_352014).sum := by decide
  have hdescent : baseEnd_352014 < baseStart_352014 := by decide
  rcases family_descends (prefixWord ++ tailWord_352014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352052 : List Nat := [2, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_352052 : Nat := 118140960795 + 352052 * 2 ^ 59
def prefixEnd_352052 : Nat := 4983230072969 + 3 ^ 40 * 352052 * 2
def baseEnd_352052 : Nat := 160686125668232736560843

theorem tailTrace_352052 : CollatzResearch.WordTrace tailWord_352052 prefixEnd_352052 160686125668232736560843 := by
  unfold tailWord_352052
  simp only [CollatzResearch.WordTrace]
  refine ⟨6420195660291602269929205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8560260880388803026572273 6420195660291602269929205)
  ·
    refine ⟨601893343152337712805863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6420195660291602269929205 601893343152337712805863)
    ·
      refine ⟨902840014728506569208795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 601893343152337712805863 902840014728506569208795)
      ·
        refine ⟨1354260022092759853813193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 902840014728506569208795 1354260022092759853813193)
        ·
          refine ⟨1015695016569569890359895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1354260022092759853813193 1015695016569569890359895)
          ·
            refine ⟨1523542524854354835539843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1015695016569569890359895 1523542524854354835539843)
            ·
              refine ⟨2285313787281532253309765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1523542524854354835539843 2285313787281532253309765)
              ·
                refine ⟨428496335115287297495581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2285313787281532253309765 428496335115287297495581)
                ·
                  refine ⟨160686125668232736560843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428496335115287297495581 160686125668232736560843)
                  ·
                    rfl

theorem cell20_352052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_352052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352052 prefixEnd_352052 := by exact prefixLift 352052
  have htrace : WordTrace (prefixWord ++ tailWord_352052) baseStart_352052 baseEnd_352052 := by
    simpa [prefixWord, tailWord_352052, baseEnd_352052] using wordTrace_append hprefix tailTrace_352052
  have hstable : (prefixWord ++ tailWord_352052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352052).length < 2 ^ (prefixWord ++ tailWord_352052).sum := by decide
  have hdescent : baseEnd_352052 < baseStart_352052 := by decide
  rcases family_descends (prefixWord ++ tailWord_352052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352097 : List Nat := [1, 2, 3, 1, 1, 1, 6, 3, 2]
def baseStart_352097 : Nat := 118140960795 + 352097 * 2 ^ 59
def prefixEnd_352097 : Nat := 4983230072969 + 3 ^ 40 * 352097 * 2
def baseEnd_352097 : Nat := 160706664894412580060659

theorem tailTrace_352097 : CollatzResearch.WordTrace tailWord_352097 prefixEnd_352097 160706664894412580060659 := by
  unfold tailWord_352097
  simp only [CollatzResearch.WordTrace]
  refine ⟨12842032605420177225246545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8561355070280118150164363 12842032605420177225246545)
  ·
    refine ⟨9631524454065132918934909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12842032605420177225246545 9631524454065132918934909)
    ·
      refine ⟨3611821670274424844600591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9631524454065132918934909 3611821670274424844600591)
      ·
        refine ⟨5417732505411637266900887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3611821670274424844600591 5417732505411637266900887)
        ·
          refine ⟨8126598758117455900351331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5417732505411637266900887 8126598758117455900351331)
          ·
            refine ⟨12189898137176183850526997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8126598758117455900351331 12189898137176183850526997)
            ·
              refine ⟨571401475180133617993453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 12189898137176183850526997 571401475180133617993453)
              ·
                refine ⟨214275553192550106747545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571401475180133617993453 214275553192550106747545)
                ·
                  refine ⟨160706664894412580060659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214275553192550106747545 160706664894412580060659)
                  ·
                    rfl

theorem cell20_352097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_352097 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352097 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352097 prefixEnd_352097 := by exact prefixLift 352097
  have htrace : WordTrace (prefixWord ++ tailWord_352097) baseStart_352097 baseEnd_352097 := by
    simpa [prefixWord, tailWord_352097, baseEnd_352097] using wordTrace_append hprefix tailTrace_352097
  have hstable : (prefixWord ++ tailWord_352097).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352097).length < 2 ^ (prefixWord ++ tailWord_352097).sum := by decide
  have hdescent : baseEnd_352097 < baseStart_352097 := by decide
  rcases family_descends (prefixWord ++ tailWord_352097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352101 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 8]
def baseStart_352101 : Nat := 118140960795 + 352101 * 2 ^ 59
def prefixEnd_352101 : Nat := 4983230072969 + 3 ^ 40 * 352101 * 2
def baseEnd_352101 : Nat := 160708490603406343927309

theorem tailTrace_352101 : CollatzResearch.WordTrace tailWord_352101 prefixEnd_352101 160708490603406343927309 := by
  unfold tailWord_352101
  simp only [CollatzResearch.WordTrace]
  refine ⟨12842178497405685908392157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8561452331603790605594771 12842178497405685908392157)
  ·
    refine ⟨4815816936527132215647059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12842178497405685908392157 4815816936527132215647059)
    ·
      refine ⟨7223725404790698323470589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4815816936527132215647059 7223725404790698323470589)
      ·
        refine ⟨2708897026796511871301471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7223725404790698323470589 2708897026796511871301471)
        ·
          refine ⟨4063345540194767806952207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2708897026796511871301471 4063345540194767806952207)
          ·
            refine ⟨6095018310292151710428311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4063345540194767806952207 6095018310292151710428311)
            ·
              refine ⟨9142527465438227565642467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6095018310292151710428311 9142527465438227565642467)
              ·
                refine ⟨13713791198157341348463701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9142527465438227565642467 13713791198157341348463701)
                ·
                  refine ⟨160708490603406343927309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13713791198157341348463701 160708490603406343927309)
                  ·
                    rfl

theorem cell20_352101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_352101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352101 prefixEnd_352101 := by exact prefixLift 352101
  have htrace : WordTrace (prefixWord ++ tailWord_352101) baseStart_352101 baseEnd_352101 := by
    simpa [prefixWord, tailWord_352101, baseEnd_352101] using wordTrace_append hprefix tailTrace_352101
  have hstable : (prefixWord ++ tailWord_352101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352101).length < 2 ^ (prefixWord ++ tailWord_352101).sum := by decide
  have hdescent : baseEnd_352101 < baseStart_352101 := by decide
  rcases family_descends (prefixWord ++ tailWord_352101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352138 : List Nat := [3, 1, 2, 4, 3, 1, 2, 4]
def baseStart_352138 : Nat := 118140960795 + 352138 * 2 ^ 59
def prefixEnd_352138 : Nat := 4983230072969 + 3 ^ 40 * 352138 * 2
def baseEnd_352138 : Nat := 53575126137199553231275

theorem tailTrace_352138 : CollatzResearch.WordTrace tailWord_352138 prefixEnd_352138 53575126137199553231275 := by
  unfold tailWord_352138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210881999567910306872267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8562351998847760818326045 3210881999567910306872267)
  ·
    refine ⟨4816322999351865460308401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3210881999567910306872267 4816322999351865460308401)
    ·
      refine ⟨3612242249513899095231301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4816322999351865460308401 3612242249513899095231301)
      ·
        refine ⟨677295421783856080355869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3612242249513899095231301 677295421783856080355869)
        ·
          refine ⟨253985783168946030133451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 677295421783856080355869 253985783168946030133451)
          ·
            refine ⟨380978674753419045200177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253985783168946030133451 380978674753419045200177)
            ·
              refine ⟨285734006065064283900133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380978674753419045200177 285734006065064283900133)
              ·
                refine ⟨53575126137199553231275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 285734006065064283900133 53575126137199553231275)
                ·
                  rfl

theorem cell20_352138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_352138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352138 prefixEnd_352138 := by exact prefixLift 352138
  have htrace : WordTrace (prefixWord ++ tailWord_352138) baseStart_352138 baseEnd_352138 := by
    simpa [prefixWord, tailWord_352138, baseEnd_352138] using wordTrace_append hprefix tailTrace_352138
  have hstable : (prefixWord ++ tailWord_352138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352138).length < 2 ^ (prefixWord ++ tailWord_352138).sum := by decide
  have hdescent : baseEnd_352138 < baseStart_352138 := by decide
  rcases family_descends (prefixWord ++ tailWord_352138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352220 : List Nat := [2, 2, 6, 1, 2, 1, 2, 2, 2]
def baseStart_352220 : Nat := 118140960795 + 352220 * 2 ^ 59
def prefixEnd_352220 : Nat := 4983230072969 + 3 ^ 40 * 352220 * 2
def baseEnd_352220 : Nat := 160762805445970818960157

theorem tailTrace_352220 : CollatzResearch.WordTrace tailWord_352220 prefixEnd_352220 160762805445970818960157 := by
  unfold tailWord_352220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6423259391987284615987057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8564345855983046154649409 6423259391987284615987057)
  ·
    refine ⟨4817444543990463461990293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6423259391987284615987057 4817444543990463461990293)
    ·
      refine ⟨225817712999552974780795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4817444543990463461990293 225817712999552974780795)
      ·
        refine ⟨338726569499329462171193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225817712999552974780795 338726569499329462171193)
        ·
          refine ⟨254044927124497096628395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338726569499329462171193 254044927124497096628395)
          ·
            refine ⟨381067390686745644942593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 254044927124497096628395 381067390686745644942593)
            ·
              refine ⟨285800543015059233706945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 381067390686745644942593 285800543015059233706945)
              ·
                refine ⟨214350407261294425280209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 285800543015059233706945 214350407261294425280209)
                ·
                  refine ⟨160762805445970818960157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214350407261294425280209 160762805445970818960157)
                  ·
                    rfl

theorem cell20_352220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 2, 2, 2].length) (baseStart_352220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352220 prefixEnd_352220 := by exact prefixLift 352220
  have htrace : WordTrace (prefixWord ++ tailWord_352220) baseStart_352220 baseEnd_352220 := by
    simpa [prefixWord, tailWord_352220, baseEnd_352220] using wordTrace_append hprefix tailTrace_352220
  have hstable : (prefixWord ++ tailWord_352220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352220).length < 2 ^ (prefixWord ++ tailWord_352220).sum := by decide
  have hdescent : baseEnd_352220 < baseStart_352220 := by decide
  rcases family_descends (prefixWord ++ tailWord_352220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352253 : List Nat := [1, 4, 1, 1, 1, 2, 3, 1, 6]
def baseStart_352253 : Nat := 118140960795 + 352253 * 2 ^ 59
def prefixEnd_352253 : Nat := 4983230072969 + 3 ^ 40 * 352253 * 2
def baseEnd_352253 : Nat := 160777867545169370860021

theorem tailTrace_352253 : CollatzResearch.WordTrace tailWord_352253 prefixEnd_352253 160777867545169370860021 := by
  unfold tailWord_352253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12847722392855015867925413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8565148261903343911950275 12847722392855015867925413)
  ·
    refine ⟨2408947948660315475236015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12847722392855015867925413 2408947948660315475236015)
    ·
      refine ⟨3613421922990473212854023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2408947948660315475236015 3613421922990473212854023)
      ·
        refine ⟨5420132884485709819281035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613421922990473212854023 5420132884485709819281035)
        ·
          refine ⟨8130199326728564728921553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5420132884485709819281035 8130199326728564728921553)
          ·
            refine ⟨6097649495046423546691165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8130199326728564728921553 6097649495046423546691165)
            ·
              refine ⟨2286618560642408830009187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6097649495046423546691165 2286618560642408830009187)
              ·
                refine ⟨3429927840963613245013781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2286618560642408830009187 3429927840963613245013781)
                ·
                  refine ⟨160777867545169370860021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3429927840963613245013781 160777867545169370860021)
                  ·
                    rfl

theorem cell20_352253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_352253 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352253 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352253 prefixEnd_352253 := by exact prefixLift 352253
  have htrace : WordTrace (prefixWord ++ tailWord_352253) baseStart_352253 baseEnd_352253 := by
    simpa [prefixWord, tailWord_352253, baseEnd_352253] using wordTrace_append hprefix tailTrace_352253
  have hstable : (prefixWord ++ tailWord_352253).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352253).length < 2 ^ (prefixWord ++ tailWord_352253).sum := by decide
  have hdescent : baseEnd_352253 < baseStart_352253 := by decide
  rcases family_descends (prefixWord ++ tailWord_352253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352266 : List Nat := [3, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_352266 : Nat := 118140960795 + 352266 * 2 ^ 59
def prefixEnd_352266 : Nat := 4983230072969 + 3 ^ 40 * 352266 * 2
def baseEnd_352266 : Nat := 160783801099399103426635

theorem tailTrace_352266 : CollatzResearch.WordTrace tailWord_352266 prefixEnd_352266 160783801099399103426635 := by
  unfold tailWord_352266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3212049135451979772037163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8565464361205279392099101 3212049135451979772037163)
  ·
    refine ⟨4818073703177969658055745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3212049135451979772037163 4818073703177969658055745)
    ·
      refine ⟨3613555277383477243541809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4818073703177969658055745 3613555277383477243541809)
      ·
        refine ⟨2710166458037607932656357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3613555277383477243541809 2710166458037607932656357)
        ·
          refine ⟨508156210882051487373067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2710166458037607932656357 508156210882051487373067)
          ·
            refine ⟨762234316323077231059601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508156210882051487373067 762234316323077231059601)
            ·
              refine ⟨571675737242307923294701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 762234316323077231059601 571675737242307923294701)
              ·
                refine ⟨214378401465865471235513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 571675737242307923294701 214378401465865471235513)
                ·
                  refine ⟨160783801099399103426635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 214378401465865471235513 160783801099399103426635)
                  ·
                    rfl

theorem cell20_352266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_352266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352266 prefixEnd_352266 := by exact prefixLift 352266
  have htrace : WordTrace (prefixWord ++ tailWord_352266) baseStart_352266 baseEnd_352266 := by
    simpa [prefixWord, tailWord_352266, baseEnd_352266] using wordTrace_append hprefix tailTrace_352266
  have hstable : (prefixWord ++ tailWord_352266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352266).length < 2 ^ (prefixWord ++ tailWord_352266).sum := by decide
  have hdescent : baseEnd_352266 < baseStart_352266 := by decide
  rcases family_descends (prefixWord ++ tailWord_352266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352276 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 3]
def baseStart_352276 : Nat := 118140960795 + 352276 * 2 ^ 59
def prefixEnd_352276 : Nat := 4983230072969 + 3 ^ 40 * 352276 * 2
def baseEnd_352276 : Nat := 160788365371883513093261

theorem tailTrace_352276 : CollatzResearch.WordTrace tailWord_352276 prefixEnd_352276 160788365371883513093261 := by
  unfold tailWord_352276
  simp only [CollatzResearch.WordTrace]
  refine ⟨6424280635885845398006341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8565707514514460530675121 6424280635885845398006341)
  ·
    refine ⟨1204552619228596012126189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6424280635885845398006341 1204552619228596012126189)
    ·
      refine ⟨451707232210723504547321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1204552619228596012126189 451707232210723504547321)
      ·
        refine ⟨338780424158042628410491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 451707232210723504547321 338780424158042628410491)
        ·
          refine ⟨508170636237063942615737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338780424158042628410491 508170636237063942615737)
          ·
            refine ⟨381127977177797956961803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 508170636237063942615737 381127977177797956961803)
            ·
              refine ⟨571691965766696935442705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 381127977177797956961803 571691965766696935442705)
              ·
                refine ⟨428768974325022701582029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 571691965766696935442705 428768974325022701582029)
                ·
                  refine ⟨160788365371883513093261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 428768974325022701582029 160788365371883513093261)
                  ·
                    rfl

theorem cell20_352276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_352276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352276 prefixEnd_352276 := by exact prefixLift 352276
  have htrace : WordTrace (prefixWord ++ tailWord_352276) baseStart_352276 baseEnd_352276 := by
    simpa [prefixWord, tailWord_352276, baseEnd_352276] using wordTrace_append hprefix tailTrace_352276
  have hstable : (prefixWord ++ tailWord_352276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352276).length < 2 ^ (prefixWord ++ tailWord_352276).sum := by decide
  have hdescent : baseEnd_352276 < baseStart_352276 := by decide
  rcases family_descends (prefixWord ++ tailWord_352276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_352277 : List Nat := [1, 3, 2, 1, 5, 1, 7]
def baseStart_352277 : Nat := 118140960795 + 352277 * 2 ^ 59
def prefixEnd_352277 : Nat := 4983230072969 + 3 ^ 40 * 352277 * 2
def baseEnd_352277 : Nat := 17865424644347994895547

theorem tailTrace_352277 : CollatzResearch.WordTrace tailWord_352277 prefixEnd_352277 17865424644347994895547 := by
  unfold tailWord_352277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12848597744768067966799085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8565731829845378644532723 12848597744768067966799085)
  ·
    refine ⟨4818224154288025487549657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12848597744768067966799085 4818224154288025487549657)
    ·
      refine ⟨3613668115716019115662243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4818224154288025487549657 3613668115716019115662243)
      ·
        refine ⟨5420502173574028673493365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3613668115716019115662243 5420502173574028673493365)
        ·
          refine ⟨508172078772565188140003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5420502173574028673493365 508172078772565188140003)
          ·
            refine ⟨762258118158847782210005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 508172078772565188140003 762258118158847782210005)
            ·
              refine ⟨17865424644347994895547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 762258118158847782210005 17865424644347994895547)
              ·
                rfl

theorem cell20_352277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 7].length) (baseStart_352277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_352277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_352277 prefixEnd_352277 := by exact prefixLift 352277
  have htrace : WordTrace (prefixWord ++ tailWord_352277) baseStart_352277 baseEnd_352277 := by
    simpa [prefixWord, tailWord_352277, baseEnd_352277] using wordTrace_append hprefix tailTrace_352277
  have hstable : (prefixWord ++ tailWord_352277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_352277).length < 2 ^ (prefixWord ++ tailWord_352277).sum := by decide
  have hdescent : baseEnd_352277 < baseStart_352277 := by decide
  rcases family_descends (prefixWord ++ tailWord_352277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
