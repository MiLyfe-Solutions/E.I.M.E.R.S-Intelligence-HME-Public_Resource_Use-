import V185TrunkScan23Chunk0309

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1833850 : List Nat := [3, 1, 1, 1, 1, 1, 3, 3, 9]
def baseStart_1833850 : Nat := 118140960795 + 1833850 * 2 ^ 59
def prefixEnd_1833850 : Nat := 4983230072969 + 3 ^ 40 * 1833850 * 2
def baseEnd_1833850 : Nat := 104627388694195031904587

theorem tailTrace_1833850 : CollatzResearch.WordTrace tailWord_1833850 prefixEnd_1833850 104627388694195031904587 := by
  unfold tailWord_1833850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721501101570530372562751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44590669604188080993500669 16721501101570530372562751)
  ·
    refine ⟨25082251652355795558844127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16721501101570530372562751 25082251652355795558844127)
    ·
      refine ⟨37623377478533693338266191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25082251652355795558844127 37623377478533693338266191)
      ·
        refine ⟨56435066217800540007399287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37623377478533693338266191 56435066217800540007399287)
        ·
          refine ⟨84652599326700810011098931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56435066217800540007399287 84652599326700810011098931)
          ·
            refine ⟨126978898990051215016648397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84652599326700810011098931 126978898990051215016648397)
            ·
              refine ⟨47617087121269205631243149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126978898990051215016648397 47617087121269205631243149)
              ·
                refine ⟨17856407670475952111716181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47617087121269205631243149 17856407670475952111716181)
                ·
                  refine ⟨104627388694195031904587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17856407670475952111716181 104627388694195031904587)
                  ·
                    rfl

theorem cell23_1833850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 9].length) (baseStart_1833850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833850 prefixEnd_1833850 := by exact prefixLift 1833850
  have htrace : WordTrace (prefixWord ++ tailWord_1833850) baseStart_1833850 baseEnd_1833850 := by
    simpa [prefixWord, tailWord_1833850, baseEnd_1833850] using wordTrace_append hprefix tailTrace_1833850
  have hstable : (prefixWord ++ tailWord_1833850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833850).length < 2 ^ (prefixWord ++ tailWord_1833850).sum := by decide
  have hdescent : baseEnd_1833850 < baseStart_1833850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833901 : List Nat := [1, 5, 2, 3, 1, 1, 1, 2, 7]
def baseStart_1833901 : Nat := 118140960795 + 1833901 * 2 ^ 59
def prefixEnd_1833901 : Nat := 4983230072969 + 3 ^ 40 * 1833901 * 2
def baseEnd_1833901 : Nat := 104630298417903843067061

theorem tailTrace_1833901 : CollatzResearch.WordTrace tailWord_1833901 prefixEnd_1833901 104630298417903843067061 := by
  unfold tailWord_1833901
  simp only [CollatzResearch.WordTrace]
  refine ⟨66887864529097357200357557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44591909686064904800238371 66887864529097357200357557)
  ·
    refine ⟨6270737299602877237533521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66887864529097357200357557 6270737299602877237533521)
    ·
      refine ⟨4703052974702157928150141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6270737299602877237533521 4703052974702157928150141)
      ·
        refine ⟨1763644865513309223056303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4703052974702157928150141 1763644865513309223056303)
        ·
          refine ⟨2645467298269963834584455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1763644865513309223056303 2645467298269963834584455)
          ·
            refine ⟨3968200947404945751876683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2645467298269963834584455 3968200947404945751876683)
            ·
              refine ⟨5952301421107418627815025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968200947404945751876683 5952301421107418627815025)
              ·
                refine ⟨4464226065830563970861269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5952301421107418627815025 4464226065830563970861269)
                ·
                  refine ⟨104630298417903843067061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4464226065830563970861269 104630298417903843067061)
                  ·
                    rfl

theorem cell23_1833901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_1833901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833901 prefixEnd_1833901 := by exact prefixLift 1833901
  have htrace : WordTrace (prefixWord ++ tailWord_1833901) baseStart_1833901 baseEnd_1833901 := by
    simpa [prefixWord, tailWord_1833901, baseEnd_1833901] using wordTrace_append hprefix tailTrace_1833901
  have hstable : (prefixWord ++ tailWord_1833901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833901).length < 2 ^ (prefixWord ++ tailWord_1833901).sum := by decide
  have hdescent : baseEnd_1833901 < baseStart_1833901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833944 : List Nat := [2, 1, 2, 2, 2, 3, 1, 3, 3, 4]
def baseStart_1833944 : Nat := 118140960795 + 1833944 * 2 ^ 59
def prefixEnd_1833944 : Nat := 4983230072969 + 3 ^ 40 * 1833944 * 2
def baseEnd_1833944 : Nat := 313898255143092639788617

theorem tailTrace_1833944 : CollatzResearch.WordTrace tailWord_1833944 prefixEnd_1833944 313898255143092639788617 := by
  unfold tailWord_1833944
  simp only [CollatzResearch.WordTrace]
  refine ⟨33444716433970787772086443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44592955245294383696115257 33444716433970787772086443)
  ·
    refine ⟨50167074650956181658129665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33444716433970787772086443 50167074650956181658129665)
    ·
      refine ⟨37625305988217136243597249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50167074650956181658129665 37625305988217136243597249)
      ·
        refine ⟨28218979491162852182697937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37625305988217136243597249 28218979491162852182697937)
        ·
          refine ⟨21164234618372139137023453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28218979491162852182697937 21164234618372139137023453)
          ·
            refine ⟨7936587981889552176383795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21164234618372139137023453 7936587981889552176383795)
            ·
              refine ⟨11904881972834328264575693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7936587981889552176383795 11904881972834328264575693)
              ·
                refine ⟨4464330739812873099215885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11904881972834328264575693 4464330739812873099215885)
                ·
                  refine ⟨1674124027429827412205957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4464330739812873099215885 1674124027429827412205957)
                  ·
                    refine ⟨313898255143092639788617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674124027429827412205957 313898255143092639788617)
                    ·
                      rfl

theorem cell23_1833944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_1833944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833944 prefixEnd_1833944 := by exact prefixLift 1833944
  have htrace : WordTrace (prefixWord ++ tailWord_1833944) baseStart_1833944 baseEnd_1833944 := by
    simpa [prefixWord, tailWord_1833944, baseEnd_1833944] using wordTrace_append hprefix tailTrace_1833944
  have hstable : (prefixWord ++ tailWord_1833944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833944).length < 2 ^ (prefixWord ++ tailWord_1833944).sum := by decide
  have hdescent : baseEnd_1833944 < baseStart_1833944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833974 : List Nat := [5, 1, 1, 1, 3, 1, 1, 2, 8]
def baseStart_1833974 : Nat := 118140960795 + 1833974 * 2 ^ 59
def prefixEnd_1833974 : Nat := 4983230072969 + 3 ^ 40 * 1833974 * 2
def baseEnd_1833974 : Nat := 104634463316545866887857

theorem tailTrace_1833974 : CollatzResearch.WordTrace tailWord_1833974 prefixEnd_1833974 104634463316545866887857 := by
  unfold tailWord_1833974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180657941114555666735311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44593684705221927111843317 4180657941114555666735311)
  ·
    refine ⟨6270986911671833500102967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4180657941114555666735311 6270986911671833500102967)
    ·
      refine ⟨9406480367507750250154451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270986911671833500102967 9406480367507750250154451)
      ·
        refine ⟨14109720551261625375231677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9406480367507750250154451 14109720551261625375231677)
        ·
          refine ⟨5291145206723109515711879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14109720551261625375231677 5291145206723109515711879)
          ·
            refine ⟨7936717810084664273567819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291145206723109515711879 7936717810084664273567819)
            ·
              refine ⟨11905076715126996410351729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7936717810084664273567819 11905076715126996410351729)
              ·
                refine ⟨8928807536345247307763797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11905076715126996410351729 8928807536345247307763797)
                ·
                  refine ⟨104634463316545866887857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8928807536345247307763797 104634463316545866887857)
                  ·
                    rfl

theorem cell23_1833974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_1833974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833974 prefixEnd_1833974 := by exact prefixLift 1833974
  have htrace : WordTrace (prefixWord ++ tailWord_1833974) baseStart_1833974 baseEnd_1833974 := by
    simpa [prefixWord, tailWord_1833974, baseEnd_1833974] using wordTrace_append hprefix tailTrace_1833974
  have hstable : (prefixWord ++ tailWord_1833974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833974).length < 2 ^ (prefixWord ++ tailWord_1833974).sum := by decide
  have hdescent : baseEnd_1833974 < baseStart_1833974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1833987 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 7, 5]
def baseStart_1833987 : Nat := 118140960795 + 1833987 * 2 ^ 59
def prefixEnd_1833987 : Nat := 4983230072969 + 3 ^ 40 * 1833987 * 2
def baseEnd_1833987 : Nat := 313905615032473750376051

theorem tailTrace_1833987 : CollatzResearch.WordTrace tailWord_1833987 prefixEnd_1833987 313905615032473750376051 := by
  unfold tailWord_1833987
  simp only [CollatzResearch.WordTrace]
  refine ⟨66891001206785793887988215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44594000804523862591992143 66891001206785793887988215)
  ·
    refine ⟨100336501810178690831982323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66891001206785793887988215 100336501810178690831982323)
    ·
      refine ⟨150504752715268036247973485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100336501810178690831982323 150504752715268036247973485)
      ·
        refine ⟨56439282268225513592990057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150504752715268036247973485 56439282268225513592990057)
        ·
          refine ⟨42329461701169135194742543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56439282268225513592990057 42329461701169135194742543)
          ·
            refine ⟨63494192551753702792113815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42329461701169135194742543 63494192551753702792113815)
            ·
              refine ⟨95241288827630554188170723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63494192551753702792113815 95241288827630554188170723)
              ·
                refine ⟨142861933241445831282256085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95241288827630554188170723 142861933241445831282256085)
                ·
                  refine ⟨3348326560346386670677877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142861933241445831282256085 3348326560346386670677877)
                  ·
                    refine ⟨313905615032473750376051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3348326560346386670677877 313905615032473750376051)
                    ·
                      rfl

theorem cell23_1833987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7, 5].length) (baseStart_1833987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1833987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1833987 prefixEnd_1833987 := by exact prefixLift 1833987
  have htrace : WordTrace (prefixWord ++ tailWord_1833987) baseStart_1833987 baseEnd_1833987 := by
    simpa [prefixWord, tailWord_1833987, baseEnd_1833987] using wordTrace_append hprefix tailTrace_1833987
  have hstable : (prefixWord ++ tailWord_1833987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1833987).length < 2 ^ (prefixWord ++ tailWord_1833987).sum := by decide
  have hdescent : baseEnd_1833987 < baseStart_1833987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1833987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834034 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 1, 6]
def baseStart_1834034 : Nat := 118140960795 + 1834034 * 2 ^ 59
def prefixEnd_1834034 : Nat := 4983230072969 + 3 ^ 40 * 1834034 * 2
def baseEnd_1834034 : Nat := 313913659562727522413479

theorem tailTrace_1834034 : CollatzResearch.WordTrace tailWord_1834034 prefixEnd_1834034 313913659562727522413479 := by
  unfold tailWord_1834034
  simp only [CollatzResearch.WordTrace]
  refine ⟨16723178859403880228737289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44595143625077013943299437 16723178859403880228737289)
  ·
    refine ⟨12542384144552910171552967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16723178859403880228737289 12542384144552910171552967)
    ·
      refine ⟨18813576216829365257329451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12542384144552910171552967 18813576216829365257329451)
      ·
        refine ⟨28220364325244047885994177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18813576216829365257329451 28220364325244047885994177)
        ·
          refine ⟨21165273243933035914495633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28220364325244047885994177 21165273243933035914495633)
          ·
            refine ⟨15873954932949776935871725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21165273243933035914495633 15873954932949776935871725)
            ·
              refine ⟨5952733099856166350951897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15873954932949776935871725 5952733099856166350951897)
              ·
                refine ⟨4464549824892124763213923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5952733099856166350951897 4464549824892124763213923)
                ·
                  refine ⟨6696824737338187144820885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464549824892124763213923 6696824737338187144820885)
                  ·
                    refine ⟨313913659562727522413479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6696824737338187144820885 313913659562727522413479)
                    ·
                      rfl

theorem cell23_1834034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_1834034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834034 prefixEnd_1834034 := by exact prefixLift 1834034
  have htrace : WordTrace (prefixWord ++ tailWord_1834034) baseStart_1834034 baseEnd_1834034 := by
    simpa [prefixWord, tailWord_1834034, baseEnd_1834034] using wordTrace_append hprefix tailTrace_1834034
  have hstable : (prefixWord ++ tailWord_1834034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834034).length < 2 ^ (prefixWord ++ tailWord_1834034).sum := by decide
  have hdescent : baseEnd_1834034 < baseStart_1834034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834051 : List Nat := [1, 1, 1, 3, 1, 2, 6, 2, 2, 4]
def baseStart_1834051 : Nat := 118140960795 + 1834051 * 2 ^ 59
def prefixEnd_1834051 : Nat := 4983230072969 + 3 ^ 40 * 1834051 * 2
def baseEnd_1834051 : Nat := 313916569286436333575953

theorem tailTrace_1834051 : CollatzResearch.WordTrace tailWord_1834051 prefixEnd_1834051 313916569286436333575953 := by
  unfold tailWord_1834051
  simp only [CollatzResearch.WordTrace]
  refine ⟨66893335478553932818318007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44595556985702621878878671 66893335478553932818318007)
  ·
    refine ⟨100340003217830899227477011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66893335478553932818318007 100340003217830899227477011)
    ·
      refine ⟨150510004826746348841215517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100340003217830899227477011 150510004826746348841215517)
      ·
        refine ⟨56441251810029880815455819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150510004826746348841215517 56441251810029880815455819)
        ·
          refine ⟨84661877715044821223183729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56441251810029880815455819 84661877715044821223183729)
          ·
            refine ⟨63496408286283615917387797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84661877715044821223183729 63496408286283615917387797)
            ·
              refine ⟨2976394138419544496127553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63496408286283615917387797 2976394138419544496127553)
              ·
                refine ⟨2232295603814658372095665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976394138419544496127553 2232295603814658372095665)
                ·
                  refine ⟨1674221702860993779071749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2232295603814658372095665 1674221702860993779071749)
                  ·
                    refine ⟨313916569286436333575953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674221702860993779071749 313916569286436333575953)
                    ·
                      rfl

theorem cell23_1834051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 2, 2, 4].length) (baseStart_1834051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834051 prefixEnd_1834051 := by exact prefixLift 1834051
  have htrace : WordTrace (prefixWord ++ tailWord_1834051) baseStart_1834051 baseEnd_1834051 := by
    simpa [prefixWord, tailWord_1834051, baseEnd_1834051] using wordTrace_append hprefix tailTrace_1834051
  have hstable : (prefixWord ++ tailWord_1834051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834051).length < 2 ^ (prefixWord ++ tailWord_1834051).sum := by decide
  have hdescent : baseEnd_1834051 < baseStart_1834051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834057 : List Nat := [1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_1834057 : Nat := 118140960795 + 1834057 * 2 ^ 59
def prefixEnd_1834057 : Nat := 4983230072969 + 3 ^ 40 * 1834057 * 2
def baseEnd_1834057 : Nat := 941752788743235977252831

theorem tailTrace_1834057 : CollatzResearch.WordTrace tailWord_1834057 prefixEnd_1834057 941752788743235977252831 := by
  unfold tailWord_1834057
  simp only [CollatzResearch.WordTrace]
  refine ⟨66893554316532195843036425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44595702877688130562024283 66893554316532195843036425)
  ·
    refine ⟨50170165737399146882277319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66893554316532195843036425 50170165737399146882277319)
    ·
      refine ⟨75255248606098720323415979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50170165737399146882277319 75255248606098720323415979)
      ·
        refine ⟨112882872909148080485123969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75255248606098720323415979 112882872909148080485123969)
        ·
          refine ⟨84662154681861060363842977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112882872909148080485123969 84662154681861060363842977)
          ·
            refine ⟨63496616011395795272882233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84662154681861060363842977 63496616011395795272882233)
            ·
              refine ⟨47622462008546846454661675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63496616011395795272882233 47622462008546846454661675)
              ·
                refine ⟨71433693012820269681992513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47622462008546846454661675 71433693012820269681992513)
                ·
                  refine ⟨53575269759615202261494385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71433693012820269681992513 53575269759615202261494385)
                  ·
                    refine ⟨40181452319711401696120789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53575269759615202261494385 40181452319711401696120789)
                    ·
                      refine ⟨941752788743235977252831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40181452319711401696120789 941752788743235977252831)
                      ·
                        rfl

theorem cell23_1834057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_1834057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834057 prefixEnd_1834057 := by exact prefixLift 1834057
  have htrace : WordTrace (prefixWord ++ tailWord_1834057) baseStart_1834057 baseEnd_1834057 := by
    simpa [prefixWord, tailWord_1834057, baseEnd_1834057] using wordTrace_append hprefix tailTrace_1834057
  have hstable : (prefixWord ++ tailWord_1834057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834057).length < 2 ^ (prefixWord ++ tailWord_1834057).sum := by decide
  have hdescent : baseEnd_1834057 < baseStart_1834057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834067 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6]
def baseStart_1834067 : Nat := 118140960795 + 1834067 * 2 ^ 59
def prefixEnd_1834067 : Nat := 4983230072969 + 3 ^ 40 * 1834067 * 2
def baseEnd_1834067 : Nat := 941757923549780938127785

theorem tailTrace_1834067 : CollatzResearch.WordTrace tailWord_1834067 prefixEnd_1834067 941757923549780938127785 := by
  unfold tailWord_1834067
  simp only [CollatzResearch.WordTrace]
  refine ⟨66893919046495967550900455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44595946030997311700600303 66893919046495967550900455)
  ·
    refine ⟨100340878569743951326350683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66893919046495967550900455 100340878569743951326350683)
    ·
      refine ⟨150511317854615926989526025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100340878569743951326350683 150511317854615926989526025)
      ·
        refine ⟨112883488390961945242144519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150511317854615926989526025 112883488390961945242144519)
        ·
          refine ⟨169325232586442917863216779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112883488390961945242144519 169325232586442917863216779)
          ·
            refine ⟨253987848879664376794825169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169325232586442917863216779 253987848879664376794825169)
            ·
              refine ⟨190490886659748282596118877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253987848879664376794825169 190490886659748282596118877)
              ·
                refine ⟨71434082497405605973544579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190490886659748282596118877 71434082497405605973544579)
                ·
                  refine ⟨107151123746108408960316869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71434082497405605973544579 107151123746108408960316869)
                  ·
                    refine ⟨20090835702395326680059413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107151123746108408960316869 20090835702395326680059413)
                    ·
                      refine ⟨941757923549780938127785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20090835702395326680059413 941757923549780938127785)
                      ·
                        rfl

theorem cell23_1834067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_1834067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834067 prefixEnd_1834067 := by exact prefixLift 1834067
  have htrace : WordTrace (prefixWord ++ tailWord_1834067) baseStart_1834067 baseEnd_1834067 := by
    simpa [prefixWord, tailWord_1834067, baseEnd_1834067] using wordTrace_append hprefix tailTrace_1834067
  have hstable : (prefixWord ++ tailWord_1834067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834067).length < 2 ^ (prefixWord ++ tailWord_1834067).sum := by decide
  have hdescent : baseEnd_1834067 < baseStart_1834067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834135 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 1, 3, 2]
def baseStart_1834135 : Nat := 118140960795 + 1834135 * 2 ^ 59
def prefixEnd_1834135 : Nat := 4983230072969 + 3 ^ 40 * 1834135 * 2
def baseEnd_1834135 : Nat := 941792840234286672077473

theorem tailTrace_1834135 : CollatzResearch.WordTrace tailWord_1834135 prefixEnd_1834135 941792840234286672077473 := by
  unfold tailWord_1834135
  simp only [CollatzResearch.WordTrace]
  refine ⟨66896399210249615164375859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44597599473499743442917239 66896399210249615164375859)
  ·
    refine ⟨100344598815374422746563789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66896399210249615164375859 100344598815374422746563789)
    ·
      refine ⟨37629224555765408529961421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100344598815374422746563789 37629224555765408529961421)
      ·
        refine ⟨14110959208412028198735533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37629224555765408529961421 14110959208412028198735533)
        ·
          refine ⟨5291609703154510574525825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14110959208412028198735533 5291609703154510574525825)
          ·
            refine ⟨3968707277365882930894369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5291609703154510574525825 3968707277365882930894369)
            ·
              refine ⟨2976530458024412198170777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3968707277365882930894369 2976530458024412198170777)
              ·
                refine ⟨2232397843518309148628083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976530458024412198170777 2232397843518309148628083)
                ·
                  refine ⟨3348596765277463722942125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232397843518309148628083 3348596765277463722942125)
                  ·
                    refine ⟨1255723786979048896103297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3348596765277463722942125 1255723786979048896103297)
                    ·
                      refine ⟨941792840234286672077473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255723786979048896103297 941792840234286672077473)
                      ·
                        rfl

theorem cell23_1834135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_1834135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834135 prefixEnd_1834135 := by exact prefixLift 1834135
  have htrace : WordTrace (prefixWord ++ tailWord_1834135) baseStart_1834135 baseEnd_1834135 := by
    simpa [prefixWord, tailWord_1834135, baseEnd_1834135] using wordTrace_append hprefix tailTrace_1834135
  have hstable : (prefixWord ++ tailWord_1834135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834135).length < 2 ^ (prefixWord ++ tailWord_1834135).sum := by decide
  have hdescent : baseEnd_1834135 < baseStart_1834135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834151 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 5]
def baseStart_1834151 : Nat := 118140960795 + 1834151 * 2 ^ 59
def prefixEnd_1834151 : Nat := 4983230072969 + 3 ^ 40 * 1834151 * 2
def baseEnd_1834151 : Nat := 941801055924758609477399

theorem tailTrace_1834151 : CollatzResearch.WordTrace tailWord_1834151 prefixEnd_1834151 941801055924758609477399 := by
  unfold tailWord_1834151
  simp only [CollatzResearch.WordTrace]
  refine ⟨66896982778191649896958307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44597988518794433264638871 66896982778191649896958307)
  ·
    refine ⟨100345474167287474845437461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66896982778191649896958307 100345474167287474845437461)
    ·
      refine ⟨4703694101591600383379881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100345474167287474845437461 4703694101591600383379881)
      ·
        refine ⟨3527770576193700287534911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4703694101591600383379881 3527770576193700287534911)
        ·
          refine ⟨5291655864290550431302367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3527770576193700287534911 5291655864290550431302367)
          ·
            refine ⟨7937483796435825646953551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291655864290550431302367 7937483796435825646953551)
            ·
              refine ⟨11906225694653738470430327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7937483796435825646953551 11906225694653738470430327)
              ·
                refine ⟨17859338541980607705645491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11906225694653738470430327 17859338541980607705645491)
                ·
                  refine ⟨26789007812970911558468237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17859338541980607705645491 26789007812970911558468237)
                  ·
                    refine ⟨10045877929864091834425589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26789007812970911558468237 10045877929864091834425589)
                    ·
                      refine ⟨941801055924758609477399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10045877929864091834425589 941801055924758609477399)
                      ·
                        rfl

theorem cell23_1834151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_1834151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834151 prefixEnd_1834151 := by exact prefixLift 1834151
  have htrace : WordTrace (prefixWord ++ tailWord_1834151) baseStart_1834151 baseEnd_1834151 := by
    simpa [prefixWord, tailWord_1834151, baseEnd_1834151] using wordTrace_append hprefix tailTrace_1834151
  have hstable : (prefixWord ++ tailWord_1834151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834151).length < 2 ^ (prefixWord ++ tailWord_1834151).sum := by decide
  have hdescent : baseEnd_1834151 < baseStart_1834151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834184 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 3, 7]
def baseStart_1834184 : Nat := 118140960795 + 1834184 * 2 ^ 59
def prefixEnd_1834184 : Nat := 4983230072969 + 3 ^ 40 * 1834184 * 2
def baseEnd_1834184 : Nat := 313939333595452326788249

theorem tailTrace_1834184 : CollatzResearch.WordTrace tailWord_1834184 prefixEnd_1834184 313939333595452326788249 := by
  unfold tailWord_1834184
  simp only [CollatzResearch.WordTrace]
  refine ⟨33449093193536048266454803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44598790924714731021939737 33449093193536048266454803)
  ·
    refine ⟨50173639790304072399682205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33449093193536048266454803 50173639790304072399682205)
    ·
      refine ⟨18815114921364027149880827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50173639790304072399682205 18815114921364027149880827)
      ·
        refine ⟨28222672382046040724821241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18815114921364027149880827 28222672382046040724821241)
        ·
          refine ⟨21167004286534530543615931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28222672382046040724821241 21167004286534530543615931)
          ·
            refine ⟨31750506429801795815423897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21167004286534530543615931 31750506429801795815423897)
            ·
              refine ⟨23812879822351346861567923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31750506429801795815423897 23812879822351346861567923)
              ·
                refine ⟨35719319733527020292351885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23812879822351346861567923 35719319733527020292351885)
                ·
                  refine ⟨13394744900072632609631957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35719319733527020292351885 13394744900072632609631957)
                  ·
                    refine ⟨313939333595452326788249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13394744900072632609631957 313939333595452326788249)
                    ·
                      rfl

theorem cell23_1834184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_1834184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834184 prefixEnd_1834184 := by exact prefixLift 1834184
  have htrace : WordTrace (prefixWord ++ tailWord_1834184) baseStart_1834184 baseEnd_1834184 := by
    simpa [prefixWord, tailWord_1834184, baseEnd_1834184] using wordTrace_append hprefix tailTrace_1834184
  have hstable : (prefixWord ++ tailWord_1834184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834184).length < 2 ^ (prefixWord ++ tailWord_1834184).sum := by decide
  have hdescent : baseEnd_1834184 < baseStart_1834184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834191 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 4, 5, 2]
def baseStart_1834191 : Nat := 118140960795 + 1834191 * 2 ^ 59
def prefixEnd_1834191 : Nat := 4983230072969 + 3 ^ 40 * 1834191 * 2
def baseEnd_1834191 : Nat := 941821595150938452977215

theorem tailTrace_1834191 : CollatzResearch.WordTrace tailWord_1834191 prefixEnd_1834191 941821595150938452977215 := by
  unfold tailWord_1834191
  simp only [CollatzResearch.WordTrace]
  refine ⟨66898441698046736728414427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44598961132031157818942951 66898441698046736728414427)
  ·
    refine ⟨100347662547070105092621641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66898441698046736728414427 100347662547070105092621641)
    ·
      refine ⟨75260746910302578819466231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100347662547070105092621641 75260746910302578819466231)
      ·
        refine ⟨112891120365453868229199347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75260746910302578819466231 112891120365453868229199347)
        ·
          refine ⟨169336680548180802343799021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112891120365453868229199347 169336680548180802343799021)
          ·
            refine ⟨63501255205567800878924633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169336680548180802343799021 63501255205567800878924633)
            ·
              refine ⟨47625941404175850659193475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63501255205567800878924633 47625941404175850659193475)
              ·
                refine ⟨71438912106263775988790213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47625941404175850659193475 71438912106263775988790213)
                ·
                  refine ⟨13394796019924457997898165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71438912106263775988790213 13394796019924457997898165)
                  ·
                    refine ⟨1255762126867917937302953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13394796019924457997898165 1255762126867917937302953)
                    ·
                      refine ⟨941821595150938452977215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255762126867917937302953 941821595150938452977215)
                      ·
                        rfl

theorem cell23_1834191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 5, 2].length) (baseStart_1834191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834191 prefixEnd_1834191 := by exact prefixLift 1834191
  have htrace : WordTrace (prefixWord ++ tailWord_1834191) baseStart_1834191 baseEnd_1834191 := by
    simpa [prefixWord, tailWord_1834191, baseEnd_1834191] using wordTrace_append hprefix tailTrace_1834191
  have hstable : (prefixWord ++ tailWord_1834191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834191).length < 2 ^ (prefixWord ++ tailWord_1834191).sum := by decide
  have hdescent : baseEnd_1834191 < baseStart_1834191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834282 : List Nat := [3, 1, 4, 2, 1, 1, 2, 4, 1, 4]
def baseStart_1834282 : Nat := 118140960795 + 1834282 * 2 ^ 59
def prefixEnd_1834282 : Nat := 4983230072969 + 3 ^ 40 * 1834282 * 2
def baseEnd_1834282 : Nat := 313956107296832532313099

theorem tailTrace_1834282 : CollatzResearch.WordTrace tailWord_1834282 prefixEnd_1834282 313956107296832532313099 := by
  unfold tailWord_1834282
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725440185179264817494275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44601173827144706179984733 16725440185179264817494275)
  ·
    refine ⟨25088160277768897226241413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16725440185179264817494275 25088160277768897226241413)
    ·
      refine ⟨4704030052081668229920265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25088160277768897226241413 4704030052081668229920265)
      ·
        refine ⟨3528022539061251172440199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4704030052081668229920265 3528022539061251172440199)
        ·
          refine ⟨5292033808591876758660299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528022539061251172440199 5292033808591876758660299)
          ·
            refine ⟨7938050712887815137990449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292033808591876758660299 7938050712887815137990449)
            ·
              refine ⟨5953538034665861353492837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7938050712887815137990449 5953538034665861353492837)
              ·
                refine ⟨1116288381499849003779907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5953538034665861353492837 1116288381499849003779907)
                ·
                  refine ⟨1674432572249773505669861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116288381499849003779907 1674432572249773505669861)
                  ·
                    refine ⟨313956107296832532313099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674432572249773505669861 313956107296832532313099)
                    ·
                      rfl

theorem cell23_1834282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_1834282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834282 prefixEnd_1834282 := by exact prefixLift 1834282
  have htrace : WordTrace (prefixWord ++ tailWord_1834282) baseStart_1834282 baseEnd_1834282 := by
    simpa [prefixWord, tailWord_1834282, baseEnd_1834282] using wordTrace_append hprefix tailTrace_1834282
  have hstable : (prefixWord ++ tailWord_1834282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834282).length < 2 ^ (prefixWord ++ tailWord_1834282).sum := by decide
  have hdescent : baseEnd_1834282 < baseStart_1834282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834298 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2]
def baseStart_1834298 : Nat := 118140960795 + 1834298 * 2 ^ 59
def prefixEnd_1834298 : Nat := 4983230072969 + 3 ^ 40 * 1834298 * 2
def baseEnd_1834298 : Nat := 941876537580969534339223

theorem tailTrace_1834298 : CollatzResearch.WordTrace tailWord_1834298 prefixEnd_1834298 941876537580969534339223 := by
  unfold tailWord_1834298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725586077164773500639887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44601562872439396001706365 16725586077164773500639887)
  ·
    refine ⟨25088379115747160250959831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16725586077164773500639887 25088379115747160250959831)
    ·
      refine ⟨37632568673620740376439747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25088379115747160250959831 37632568673620740376439747)
      ·
        refine ⟨56448853010431110564659621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37632568673620740376439747 56448853010431110564659621)
        ·
          refine ⟨10584159939455833230873679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56448853010431110564659621 10584159939455833230873679)
          ·
            refine ⟨15876239909183749846310519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584159939455833230873679 15876239909183749846310519)
            ·
              refine ⟨23814359863775624769465779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15876239909183749846310519 23814359863775624769465779)
              ·
                refine ⟨35721539795663437154198669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23814359863775624769465779 35721539795663437154198669)
                ·
                  refine ⟨13395577423373788932824501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35721539795663437154198669 13395577423373788932824501)
                  ·
                    refine ⟨1255835383441292712452297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13395577423373788932824501 1255835383441292712452297)
                    ·
                      refine ⟨941876537580969534339223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255835383441292712452297 941876537580969534339223)
                      ·
                        rfl

theorem cell23_1834298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_1834298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834298 prefixEnd_1834298 := by exact prefixLift 1834298
  have htrace : WordTrace (prefixWord ++ tailWord_1834298) baseStart_1834298 baseEnd_1834298 := by
    simpa [prefixWord, tailWord_1834298, baseEnd_1834298] using wordTrace_append hprefix tailTrace_1834298
  have hstable : (prefixWord ++ tailWord_1834298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834298).length < 2 ^ (prefixWord ++ tailWord_1834298).sum := by decide
  have hdescent : baseEnd_1834298 < baseStart_1834298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834321 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_1834321 : Nat := 118140960795 + 1834321 * 2 ^ 59
def prefixEnd_1834321 : Nat := 4983230072969 + 3 ^ 40 * 1834321 * 2
def baseEnd_1834321 : Nat := 313962782545340981450539

theorem tailTrace_1834321 : CollatzResearch.WordTrace tailWord_1834321 prefixEnd_1834321 313962782545340981450539 := by
  unfold tailWord_1834321
  simp only [CollatzResearch.WordTrace]
  refine ⟨66903183187575768930646817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44602122125050512620431211 66903183187575768930646817)
  ·
    refine ⟨50177387390681826697985113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66903183187575768930646817 50177387390681826697985113)
    ·
      refine ⟨37633040543011370023488835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50177387390681826697985113 37633040543011370023488835)
      ·
        refine ⟨56449560814517055035233253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37633040543011370023488835 56449560814517055035233253)
        ·
          refine ⟨10584292652721947819106235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56449560814517055035233253 10584292652721947819106235)
          ·
            refine ⟨15876438979082921728659353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584292652721947819106235 15876438979082921728659353)
            ·
              refine ⟨11907329234312191296494515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15876438979082921728659353 11907329234312191296494515)
              ·
                refine ⟨17860993851468286944741773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11907329234312191296494515 17860993851468286944741773)
                ·
                  refine ⟨6697872694300607604278165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17860993851468286944741773 6697872694300607604278165)
                  ·
                    refine ⟨313962782545340981450539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6697872694300607604278165 313962782545340981450539)
                    ·
                      rfl

theorem cell23_1834321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_1834321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834321 prefixEnd_1834321 := by exact prefixLift 1834321
  have htrace : WordTrace (prefixWord ++ tailWord_1834321) baseStart_1834321 baseEnd_1834321 := by
    simpa [prefixWord, tailWord_1834321, baseEnd_1834321] using wordTrace_append hprefix tailTrace_1834321
  have hstable : (prefixWord ++ tailWord_1834321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834321).length < 2 ^ (prefixWord ++ tailWord_1834321).sum := by decide
  have hdescent : baseEnd_1834321 < baseStart_1834321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834326 : List Nat := [5, 2, 3, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1834326 : Nat := 118140960795 + 1834326 * 2 ^ 59
def prefixEnd_1834326 : Nat := 4983230072969 + 3 ^ 40 * 1834326 * 2
def baseEnd_1834326 : Nat := 941890915039295424789095

theorem tailTrace_1834326 : CollatzResearch.WordTrace tailWord_1834326 prefixEnd_1834326 941890915039295424789095 := by
  unfold tailWord_1834326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4181460347034853424036177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44602243701705103189719221 4181460347034853424036177)
  ·
    refine ⟨3136095260276140068027133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4181460347034853424036177 3136095260276140068027133)
    ·
      refine ⟨1176035722603552525510175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3136095260276140068027133 1176035722603552525510175)
      ·
        refine ⟨1764053583905328788265263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176035722603552525510175 1764053583905328788265263)
        ·
          refine ⟨2646080375857993182397895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764053583905328788265263 2646080375857993182397895)
          ·
            refine ⟨3969120563786989773596843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646080375857993182397895 3969120563786989773596843)
            ·
              refine ⟨5953680845680484660395265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969120563786989773596843 5953680845680484660395265)
              ·
                refine ⟨4465260634260363495296449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5953680845680484660395265 4465260634260363495296449)
                ·
                  refine ⟨3348945475695272621472337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465260634260363495296449 3348945475695272621472337)
                  ·
                    refine ⟨2511709106771454466104253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3348945475695272621472337 2511709106771454466104253)
                    ·
                      refine ⟨941890915039295424789095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2511709106771454466104253 941890915039295424789095)
                      ·
                        rfl

theorem cell23_1834326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1834326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834326 prefixEnd_1834326 := by exact prefixLift 1834326
  have htrace : WordTrace (prefixWord ++ tailWord_1834326) baseStart_1834326 baseEnd_1834326 := by
    simpa [prefixWord, tailWord_1834326, baseEnd_1834326] using wordTrace_append hprefix tailTrace_1834326
  have hstable : (prefixWord ++ tailWord_1834326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834326).length < 2 ^ (prefixWord ++ tailWord_1834326).sum := by decide
  have hdescent : baseEnd_1834326 < baseStart_1834326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834328 : List Nat := [2, 1, 2, 2, 1, 1, 3, 5, 1, 1, 4]
def baseStart_1834328 : Nat := 118140960795 + 1834328 * 2 ^ 59
def prefixEnd_1834328 : Nat := 4983230072969 + 3 ^ 40 * 1834328 * 2
def baseEnd_1834328 : Nat := 941891942000604416964085

theorem tailTrace_1834328 : CollatzResearch.WordTrace tailWord_1834328 prefixEnd_1834328 941891942000604416964085 := by
  unfold tailWord_1834328
  simp only [CollatzResearch.WordTrace]
  refine ⟨33451719249275204563075819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44602292332366939417434425 33451719249275204563075819)
  ·
    refine ⟨50177578873912806844613729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33451719249275204563075819 50177578873912806844613729)
    ·
      refine ⟨37633184155434605133460297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50177578873912806844613729 37633184155434605133460297)
      ·
        refine ⟨28224888116575953850095223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37633184155434605133460297 28224888116575953850095223)
        ·
          refine ⟨42337332174863930775142835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28224888116575953850095223 42337332174863930775142835)
          ·
            refine ⟨63505998262295896162714253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42337332174863930775142835 63505998262295896162714253)
            ·
              refine ⟨23814749348360961061017845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63505998262295896162714253 23814749348360961061017845)
              ·
                refine ⟨2232632751408840099470423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23814749348360961061017845 2232632751408840099470423)
                ·
                  refine ⟨3348949127113260149205635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232632751408840099470423 3348949127113260149205635)
                  ·
                    refine ⟨5023423690669890223808453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3348949127113260149205635 5023423690669890223808453)
                    ·
                      refine ⟨941891942000604416964085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5023423690669890223808453 941891942000604416964085)
                      ·
                        rfl

theorem cell23_1834328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 5, 1, 1, 4].length) (baseStart_1834328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834328 prefixEnd_1834328 := by exact prefixLift 1834328
  have htrace : WordTrace (prefixWord ++ tailWord_1834328) baseStart_1834328 baseEnd_1834328 := by
    simpa [prefixWord, tailWord_1834328, baseEnd_1834328] using wordTrace_append hprefix tailTrace_1834328
  have hstable : (prefixWord ++ tailWord_1834328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834328).length < 2 ^ (prefixWord ++ tailWord_1834328).sum := by decide
  have hdescent : baseEnd_1834328 < baseStart_1834328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834333 : List Nat := [1, 4, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1834333 : Nat := 118140960795 + 1834333 * 2 ^ 59
def prefixEnd_1834333 : Nat := 4983230072969 + 3 ^ 40 * 1834333 * 2
def baseEnd_1834333 : Nat := 313964836467958965800521

theorem tailTrace_1834333 : CollatzResearch.WordTrace tailWord_1834333 prefixEnd_1834333 313964836467958965800521 := by
  unfold tailWord_1834333
  simp only [CollatzResearch.WordTrace]
  refine ⟨66903620863532294980083653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44602413909021529986722435 66903620863532294980083653)
  ·
    refine ⟨12544428911912305308765685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66903620863532294980083653 12544428911912305308765685)
    ·
      refine ⟨1176040210491778622696783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12544428911912305308765685 1176040210491778622696783)
      ·
        refine ⟨1764060315737667934045175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176040210491778622696783 1764060315737667934045175)
        ·
          refine ⟨2646090473606501901067763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764060315737667934045175 2646090473606501901067763)
          ·
            refine ⟨3969135710409752851601645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646090473606501901067763 3969135710409752851601645)
            ·
              refine ⟨1488425891403657319350617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3969135710409752851601645 1488425891403657319350617)
              ·
                refine ⟨1116319418552742989512963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488425891403657319350617 1116319418552742989512963)
                ·
                  refine ⟨1674479127829114484269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116319418552742989512963 1674479127829114484269445)
                  ·
                    refine ⟨313964836467958965800521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674479127829114484269445 313964836467958965800521)
                    ·
                      rfl

theorem cell23_1834333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1834333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834333 prefixEnd_1834333 := by exact prefixLift 1834333
  have htrace : WordTrace (prefixWord ++ tailWord_1834333) baseStart_1834333 baseEnd_1834333 := by
    simpa [prefixWord, tailWord_1834333, baseEnd_1834333] using wordTrace_append hprefix tailTrace_1834333
  have hstable : (prefixWord ++ tailWord_1834333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834333).length < 2 ^ (prefixWord ++ tailWord_1834333).sum := by decide
  have hdescent : baseEnd_1834333 < baseStart_1834333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834339 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 1, 1, 3]
def baseStart_1834339 : Nat := 118140960795 + 1834339 * 2 ^ 59
def prefixEnd_1834339 : Nat := 4983230072969 + 3 ^ 40 * 1834339 * 2
def baseEnd_1834339 : Nat := 941897590287803873926535

theorem tailTrace_1834339 : CollatzResearch.WordTrace tailWord_1834339 prefixEnd_1834339 941897590287803873926535 := by
  unfold tailWord_1834339
  simp only [CollatzResearch.WordTrace]
  refine ⟨66903839701510558004802071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44602559801007038669868047 66903839701510558004802071)
  ·
    refine ⟨100355759552265837007203107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66903839701510558004802071 100355759552265837007203107)
    ·
      refine ⟨150533639328398755510804661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100355759552265837007203107 150533639328398755510804661)
      ·
        refine ⟨14112528687037383329137937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150533639328398755510804661 14112528687037383329137937)
        ·
          refine ⟨10584396515278037496853453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14112528687037383329137937 10584396515278037496853453)
          ·
            refine ⟨3969148693229264061320045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10584396515278037496853453 3969148693229264061320045)
            ·
              refine ⟨1488430759960974022995017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3969148693229264061320045 1488430759960974022995017)
              ·
                refine ⟨1116323069970730517246263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488430759960974022995017 1116323069970730517246263)
                ·
                  refine ⟨1674484604956095775869395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116323069970730517246263 1674484604956095775869395)
                  ·
                    refine ⟨2511726907434143663804093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1674484604956095775869395 2511726907434143663804093)
                    ·
                      refine ⟨941897590287803873926535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2511726907434143663804093 941897590287803873926535)
                      ·
                        rfl

theorem cell23_1834339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 1, 1, 3].length) (baseStart_1834339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834339 prefixEnd_1834339 := by exact prefixLift 1834339
  have htrace : WordTrace (prefixWord ++ tailWord_1834339) baseStart_1834339 baseEnd_1834339 := by
    simpa [prefixWord, tailWord_1834339, baseEnd_1834339] using wordTrace_append hprefix tailTrace_1834339
  have hstable : (prefixWord ++ tailWord_1834339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834339).length < 2 ^ (prefixWord ++ tailWord_1834339).sum := by decide
  have hdescent : baseEnd_1834339 < baseStart_1834339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834341 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_1834341 : Nat := 118140960795 + 1834341 * 2 ^ 59
def prefixEnd_1834341 : Nat := 4983230072969 + 3 ^ 40 * 1834341 * 2
def baseEnd_1834341 : Nat := 941898617249112866101525

theorem tailTrace_1834341 : CollatzResearch.WordTrace tailWord_1834341 prefixEnd_1834341 941898617249112866101525 := by
  unfold tailWord_1834341
  simp only [CollatzResearch.WordTrace]
  refine ⟨66903912647503312346374877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44602608431668874897583251 66903912647503312346374877)
  ·
    refine ⟨25088967242813742129890579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66903912647503312346374877 25088967242813742129890579)
    ·
      refine ⟨37633450864220613194835869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25088967242813742129890579 37633450864220613194835869)
      ·
        refine ⟨14112544074082729948063451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37633450864220613194835869 14112544074082729948063451)
        ·
          refine ⟨21168816111124094922095177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14112544074082729948063451 21168816111124094922095177)
          ·
            refine ⟨15876612083343071191571383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21168816111124094922095177 15876612083343071191571383)
            ·
              refine ⟨23814918125014606787357075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15876612083343071191571383 23814918125014606787357075)
              ·
                refine ⟨35722377187521910181035613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23814918125014606787357075 35722377187521910181035613)
                ·
                  refine ⟨13395891445320716317888355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35722377187521910181035613 13395891445320716317888355)
                  ·
                    refine ⟨20093837167981074476832533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13395891445320716317888355 20093837167981074476832533)
                    ·
                      refine ⟨941898617249112866101525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20093837167981074476832533 941898617249112866101525)
                      ·
                        rfl

theorem cell23_1834341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_1834341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834341 prefixEnd_1834341 := by exact prefixLift 1834341
  have htrace : WordTrace (prefixWord ++ tailWord_1834341) baseStart_1834341 baseEnd_1834341 := by
    simpa [prefixWord, tailWord_1834341, baseEnd_1834341] using wordTrace_append hprefix tailTrace_1834341
  have hstable : (prefixWord ++ tailWord_1834341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834341).length < 2 ^ (prefixWord ++ tailWord_1834341).sum := by decide
  have hdescent : baseEnd_1834341 < baseStart_1834341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834345 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 3, 2, 2]
def baseStart_1834345 : Nat := 118140960795 + 1834345 * 2 ^ 59
def prefixEnd_1834345 : Nat := 4983230072969 + 3 ^ 40 * 1834345 * 2
def baseEnd_1834345 : Nat := 941900671171730850451507

theorem tailTrace_1834345 : CollatzResearch.WordTrace tailWord_1834345 prefixEnd_1834345 941900671171730850451507 := by
  unfold tailWord_1834345
  simp only [CollatzResearch.WordTrace]
  refine ⟨66904058539488821029520489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44602705692992547353013659 66904058539488821029520489)
  ·
    refine ⟨50178043904616615772140367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66904058539488821029520489 50178043904616615772140367)
    ·
      refine ⟨75267065856924923658210551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50178043904616615772140367 75267065856924923658210551)
      ·
        refine ⟨112900598785387385487315827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75267065856924923658210551 112900598785387385487315827)
        ·
          refine ⟨169350898178081078230973741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112900598785387385487315827 169350898178081078230973741)
          ·
            refine ⟨63506586816780404336615153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169350898178081078230973741 63506586816780404336615153)
            ·
              refine ⟨47629940112585303252461365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63506586816780404336615153 47629940112585303252461365)
              ·
                refine ⟨4465306885554872179918253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47629940112585303252461365 4465306885554872179918253)
                ·
                  refine ⟨1674490082083077067469345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4465306885554872179918253 1674490082083077067469345)
                  ·
                    refine ⟨1255867561562307800602009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1674490082083077067469345 1255867561562307800602009)
                    ·
                      refine ⟨941900671171730850451507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255867561562307800602009 941900671171730850451507)
                      ·
                        rfl

theorem cell23_1834345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 3, 2, 2].length) (baseStart_1834345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834345 prefixEnd_1834345 := by exact prefixLift 1834345
  have htrace : WordTrace (prefixWord ++ tailWord_1834345) baseStart_1834345 baseEnd_1834345 := by
    simpa [prefixWord, tailWord_1834345, baseEnd_1834345] using wordTrace_append hprefix tailTrace_1834345
  have hstable : (prefixWord ++ tailWord_1834345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834345).length < 2 ^ (prefixWord ++ tailWord_1834345).sum := by decide
  have hdescent : baseEnd_1834345 < baseStart_1834345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834348 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 5]
def baseStart_1834348 : Nat := 118140960795 + 1834348 * 2 ^ 59
def prefixEnd_1834348 : Nat := 4983230072969 + 3 ^ 40 * 1834348 * 2
def baseEnd_1834348 : Nat := 941902211613694338713993

theorem tailTrace_1834348 : CollatzResearch.WordTrace tailWord_1834348 prefixEnd_1834348 941902211613694338713993 := by
  unfold tailWord_1834348
  simp only [CollatzResearch.WordTrace]
  refine ⟨33452083979238976270939849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44602778638985301694586465 33452083979238976270939849)
  ·
    refine ⟨25089062984429232203204887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33452083979238976270939849 25089062984429232203204887)
    ·
      refine ⟨37633594476643848304807331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25089062984429232203204887 37633594476643848304807331)
      ·
        refine ⟨56450391714965772457210997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37633594476643848304807331 56450391714965772457210997)
        ·
          refine ⟨5292224223278041167863531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56450391714965772457210997 5292224223278041167863531)
          ·
            refine ⟨7938336334917061751795297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292224223278041167863531 7938336334917061751795297)
            ·
              refine ⟨5953752251187796313846473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7938336334917061751795297 5953752251187796313846473)
              ·
                refine ⟨4465314188390847235384855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5953752251187796313846473 4465314188390847235384855)
                ·
                  refine ⟨6697971282586270853077283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465314188390847235384855 6697971282586270853077283)
                  ·
                    refine ⟨10046956923879406279615925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697971282586270853077283 10046956923879406279615925)
                    ·
                      refine ⟨941902211613694338713993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10046956923879406279615925 941902211613694338713993)
                      ·
                        rfl

theorem cell23_1834348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 5].length) (baseStart_1834348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834348 prefixEnd_1834348 := by exact prefixLift 1834348
  have htrace : WordTrace (prefixWord ++ tailWord_1834348) baseStart_1834348 baseEnd_1834348 := by
    simpa [prefixWord, tailWord_1834348, baseEnd_1834348] using wordTrace_append hprefix tailTrace_1834348
  have hstable : (prefixWord ++ tailWord_1834348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834348).length < 2 ^ (prefixWord ++ tailWord_1834348).sum := by decide
  have hdescent : baseEnd_1834348 < baseStart_1834348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834351 : List Nat := [1, 1, 2, 1, 3, 1, 6, 8]
def baseStart_1834351 : Nat := 118140960795 + 1834351 * 2 ^ 59
def prefixEnd_1834351 : Nat := 4983230072969 + 3 ^ 40 * 1834351 * 2
def baseEnd_1834351 : Nat := 34885324150209549147277

theorem tailTrace_1834351 : CollatzResearch.WordTrace tailWord_1834351 prefixEnd_1834351 34885324150209549147277 := by
  unfold tailWord_1834351
  simp only [CollatzResearch.WordTrace]
  refine ⟨66904277377467084054238907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44602851584978056036159271 66904277377467084054238907)
  ·
    refine ⟨100356416066200626081358361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66904277377467084054238907 100356416066200626081358361)
    ·
      refine ⟨75267312049650469561018771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100356416066200626081358361 75267312049650469561018771)
      ·
        refine ⟨112900968074475704341528157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75267312049650469561018771 112900968074475704341528157)
        ·
          refine ⟨42337863027928389128073059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112900968074475704341528157 42337863027928389128073059)
          ·
            refine ⟨63506794541892583692109589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42337863027928389128073059 63506794541892583692109589)
            ·
              refine ⟨2976880994151214860567637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63506794541892583692109589 2976880994151214860567637)
              ·
                refine ⟨34885324150209549147277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2976880994151214860567637 34885324150209549147277)
                ·
                  rfl

theorem cell23_1834351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 8].length) (baseStart_1834351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834351 prefixEnd_1834351 := by exact prefixLift 1834351
  have htrace : WordTrace (prefixWord ++ tailWord_1834351) baseStart_1834351 baseEnd_1834351 := by
    simpa [prefixWord, tailWord_1834351, baseEnd_1834351] using wordTrace_append hprefix tailTrace_1834351
  have hstable : (prefixWord ++ tailWord_1834351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834351).length < 2 ^ (prefixWord ++ tailWord_1834351).sum := by decide
  have hdescent : baseEnd_1834351 < baseStart_1834351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834366 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1834366 : Nat := 118140960795 + 1834366 * 2 ^ 59
def prefixEnd_1834366 : Nat := 4983230072969 + 3 ^ 40 * 1834366 * 2
def baseEnd_1834366 : Nat := 941911454265475268288911

theorem tailTrace_1834366 : CollatzResearch.WordTrace tailWord_1834366 prefixEnd_1834366 941911454265475268288911 := by
  unfold tailWord_1834366
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363103059051592702004369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44603216314941827744023301 8363103059051592702004369)
  ·
    refine ⟨6272327294288694526503277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8363103059051592702004369 6272327294288694526503277)
    ·
      refine ⟨2352122735358260447438729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6272327294288694526503277 2352122735358260447438729)
      ·
        refine ⟨1764092051518695335579047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2352122735358260447438729 1764092051518695335579047)
        ·
          refine ⟨2646138077278043003368571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764092051518695335579047 2646138077278043003368571)
          ·
            refine ⟨3969207115917064505052857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646138077278043003368571 3969207115917064505052857)
            ·
              refine ⟨2976905336937798378789643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3969207115917064505052857 2976905336937798378789643)
              ·
                refine ⟨4465358005406697568184465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976905336937798378789643 4465358005406697568184465)
                ·
                  refine ⟨3349018504055023176138349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465358005406697568184465 3349018504055023176138349)
                  ·
                    refine ⟨1255881939020633691051881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3349018504055023176138349 1255881939020633691051881)
                    ·
                      refine ⟨941911454265475268288911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255881939020633691051881 941911454265475268288911)
                      ·
                        rfl

theorem cell23_1834366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1834366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834366 prefixEnd_1834366 := by exact prefixLift 1834366
  have htrace : WordTrace (prefixWord ++ tailWord_1834366) baseStart_1834366 baseEnd_1834366 := by
    simpa [prefixWord, tailWord_1834366, baseEnd_1834366] using wordTrace_append hprefix tailTrace_1834366
  have hstable : (prefixWord ++ tailWord_1834366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834366).length < 2 ^ (prefixWord ++ tailWord_1834366).sum := by decide
  have hdescent : baseEnd_1834366 < baseStart_1834366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834382 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5]
def baseStart_1834382 : Nat := 118140960795 + 1834382 * 2 ^ 59
def prefixEnd_1834382 : Nat := 4983230072969 + 3 ^ 40 * 1834382 * 2
def baseEnd_1834382 : Nat := 941919669955947205688837

theorem tailTrace_1834382 : CollatzResearch.WordTrace tailWord_1834382 prefixEnd_1834382 941919669955947205688837 := by
  unfold tailWord_1834382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363176005044347043577175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44603605360236517565744933 8363176005044347043577175)
  ·
    refine ⟨12544764007566520565365763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8363176005044347043577175 12544764007566520565365763)
    ·
      refine ⟨18817146011349780848048645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12544764007566520565365763 18817146011349780848048645)
      ·
        refine ⟨3528214877128083909009121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18817146011349780848048645 3528214877128083909009121)
        ·
          refine ⟨2646161157846062931756841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3528214877128083909009121 2646161157846062931756841)
          ·
            refine ⟨1984620868384547198817631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2646161157846062931756841 1984620868384547198817631)
            ·
              refine ⟨2976931302576820798226447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984620868384547198817631 2976931302576820798226447)
              ·
                refine ⟨4465396953865231197339671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2976931302576820798226447 4465396953865231197339671)
                ·
                  refine ⟨6698095430797846796009507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465396953865231197339671 6698095430797846796009507)
                  ·
                    refine ⟨10047143146196770194014261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6698095430797846796009507 10047143146196770194014261)
                    ·
                      refine ⟨941919669955947205688837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10047143146196770194014261 941919669955947205688837)
                      ·
                        rfl

theorem cell23_1834382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_1834382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834382 prefixEnd_1834382 := by exact prefixLift 1834382
  have htrace : WordTrace (prefixWord ++ tailWord_1834382) baseStart_1834382 baseEnd_1834382 := by
    simpa [prefixWord, tailWord_1834382, baseEnd_1834382] using wordTrace_append hprefix tailTrace_1834382
  have hstable : (prefixWord ++ tailWord_1834382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834382).length < 2 ^ (prefixWord ++ tailWord_1834382).sum := by decide
  have hdescent : baseEnd_1834382 < baseStart_1834382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834435 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 1, 4, 2]
def baseStart_1834435 : Nat := 118140960795 + 1834435 * 2 ^ 59
def prefixEnd_1834435 : Nat := 4983230072969 + 3 ^ 40 * 1834435 * 2
def baseEnd_1834435 : Nat := 941946884430635498326093

theorem tailTrace_1834435 : CollatzResearch.WordTrace tailWord_1834435 prefixEnd_1834435 941946884430635498326093 := by
  unfold tailWord_1834435
  simp only [CollatzResearch.WordTrace]
  refine ⟨66907341109162766400296759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44604894072775177600197839 66907341109162766400296759)
  ·
    refine ⟨100361011663744149600445139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66907341109162766400296759 100361011663744149600445139)
    ·
      refine ⟨150541517495616224400667709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100361011663744149600445139 150541517495616224400667709)
      ·
        refine ⟨56453069060856084150250391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150541517495616224400667709 56453069060856084150250391)
        ·
          refine ⟨84679603591284126225375587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56453069060856084150250391 84679603591284126225375587)
          ·
            refine ⟨127019405386926189338063381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84679603591284126225375587 127019405386926189338063381)
            ·
              refine ⟨5954034627512165125221721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127019405386926189338063381 5954034627512165125221721)
              ·
                refine ⟨4465525970634123843916291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954034627512165125221721 4465525970634123843916291)
                ·
                  refine ⟨6698288955951185765874437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465525970634123843916291 6698288955951185765874437)
                  ·
                    refine ⟨1255929179240847331101457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698288955951185765874437 1255929179240847331101457)
                    ·
                      refine ⟨941946884430635498326093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255929179240847331101457 941946884430635498326093)
                      ·
                        rfl

theorem cell23_1834435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 4, 2].length) (baseStart_1834435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834435 prefixEnd_1834435 := by exact prefixLift 1834435
  have htrace : WordTrace (prefixWord ++ tailWord_1834435) baseStart_1834435 baseEnd_1834435 := by
    simpa [prefixWord, tailWord_1834435, baseEnd_1834435] using wordTrace_append hprefix tailTrace_1834435
  have hstable : (prefixWord ++ tailWord_1834435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834435).length < 2 ^ (prefixWord ++ tailWord_1834435).sum := by decide
  have hdescent : baseEnd_1834435 < baseStart_1834435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834441 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 11]
def baseStart_1834441 : Nat := 118140960795 + 1834441 * 2 ^ 59
def prefixEnd_1834441 : Nat := 4983230072969 + 3 ^ 40 * 1834441 * 2
def baseEnd_1834441 : Nat := 104661107257173608316785

theorem tailTrace_1834441 : CollatzResearch.WordTrace tailWord_1834441 prefixEnd_1834441 104661107257173608316785 := by
  unfold tailWord_1834441
  simp only [CollatzResearch.WordTrace]
  refine ⟨66907559947141029425015177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44605039964760686283343451 66907559947141029425015177)
  ·
    refine ⟨50180669960355772068761383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66907559947141029425015177 50180669960355772068761383)
    ·
      refine ⟨75271004940533658103142075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50180669960355772068761383 75271004940533658103142075)
      ·
        refine ⟨112906507410800487154713113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75271004940533658103142075 112906507410800487154713113)
        ·
          refine ⟨84679880558100365366034835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112906507410800487154713113 84679880558100365366034835)
          ·
            refine ⟨127019820837150548049052253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84679880558100365366034835 127019820837150548049052253)
            ·
              refine ⟨47632432813931455518394595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127019820837150548049052253 47632432813931455518394595)
              ·
                refine ⟨71448649220897183277591893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47632432813931455518394595 71448649220897183277591893)
                ·
                  refine ⟨104661107257173608316785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 71448649220897183277591893 104661107257173608316785)
                  ·
                    rfl

theorem cell23_1834441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_1834441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834441 prefixEnd_1834441 := by exact prefixLift 1834441
  have htrace : WordTrace (prefixWord ++ tailWord_1834441) baseStart_1834441 baseEnd_1834441 := by
    simpa [prefixWord, tailWord_1834441, baseEnd_1834441] using wordTrace_append hprefix tailTrace_1834441
  have hstable : (prefixWord ++ tailWord_1834441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834441).length < 2 ^ (prefixWord ++ tailWord_1834441).sum := by decide
  have hdescent : baseEnd_1834441 < baseStart_1834441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834458 : List Nat := [3, 1, 1, 2, 3, 2, 1, 3, 7]
def baseStart_1834458 : Nat := 118140960795 + 1834458 * 2 ^ 59
def prefixEnd_1834458 : Nat := 4983230072969 + 3 ^ 40 * 1834458 * 2
def baseEnd_1834458 : Nat := 104662077165076545370943

theorem tailTrace_1834458 : CollatzResearch.WordTrace tailWord_1834458 prefixEnd_1834458 104662077165076545370943 := by
  unfold tailWord_1834458
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727044997019860332096007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44605453325386294218922685 16727044997019860332096007)
  ·
    refine ⟨25090567495529790498144011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16727044997019860332096007 25090567495529790498144011)
    ·
      refine ⟨37635851243294685747216017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25090567495529790498144011 37635851243294685747216017)
      ·
        refine ⟨28226888432471014310412013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37635851243294685747216017 28226888432471014310412013)
        ·
          refine ⟨10585083162176630366404505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28226888432471014310412013 10585083162176630366404505)
          ·
            refine ⟨7938812371632472774803379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10585083162176630366404505 7938812371632472774803379)
            ·
              refine ⟨11908218557448709162205069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938812371632472774803379 11908218557448709162205069)
              ·
                refine ⟨4465581959043265935826901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11908218557448709162205069 4465581959043265935826901)
                ·
                  refine ⟨104662077165076545370943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4465581959043265935826901 104662077165076545370943)
                  ·
                    rfl

theorem cell23_1834458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_1834458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834458 prefixEnd_1834458 := by exact prefixLift 1834458
  have htrace : WordTrace (prefixWord ++ tailWord_1834458) baseStart_1834458 baseEnd_1834458 := by
    simpa [prefixWord, tailWord_1834458, baseEnd_1834458] using wordTrace_append hprefix tailTrace_1834458
  have hstable : (prefixWord ++ tailWord_1834458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834458).length < 2 ^ (prefixWord ++ tailWord_1834458).sum := by decide
  have hdescent : baseEnd_1834458 < baseStart_1834458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834469 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1834469 : Nat := 118140960795 + 1834469 * 2 ^ 59
def prefixEnd_1834469 : Nat := 4983230072969 + 3 ^ 40 * 1834469 * 2
def baseEnd_1834469 : Nat := 941964342772888365300937

theorem tailTrace_1834469 : CollatzResearch.WordTrace tailWord_1834469 prefixEnd_1834469 941964342772888365300937 := by
  unfold tailWord_1834469
  simp only [CollatzResearch.WordTrace]
  refine ⟨66908581191039590207034461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44605720794026393471356307 66908581191039590207034461)
  ·
    refine ⟨25090717946639846327637923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66908581191039590207034461 25090717946639846327637923)
    ·
      refine ⟨37636076919959769491456885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25090717946639846327637923 37636076919959769491456885)
      ·
        refine ⟨3528382211246228389824083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37636076919959769491456885 3528382211246228389824083)
        ·
          refine ⟨5292573316869342584736125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528382211246228389824083 5292573316869342584736125)
          ·
            refine ⟨1984714993826003469276047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5292573316869342584736125 1984714993826003469276047)
            ·
              refine ⟨2977072490739005203914071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984714993826003469276047 2977072490739005203914071)
              ·
                refine ⟨4465608736108507805871107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977072490739005203914071 4465608736108507805871107)
                ·
                  refine ⟨6698413104162761708806661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465608736108507805871107 6698413104162761708806661)
                  ·
                    refine ⟨1255952457030517820401249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698413104162761708806661 1255952457030517820401249)
                    ·
                      refine ⟨941964342772888365300937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1255952457030517820401249 941964342772888365300937)
                      ·
                        rfl

theorem cell23_1834469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1834469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834469 prefixEnd_1834469 := by exact prefixLift 1834469
  have htrace : WordTrace (prefixWord ++ tailWord_1834469) baseStart_1834469 baseEnd_1834469 := by
    simpa [prefixWord, tailWord_1834469, baseEnd_1834469] using wordTrace_append hprefix tailTrace_1834469
  have hstable : (prefixWord ++ tailWord_1834469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834469).length < 2 ^ (prefixWord ++ tailWord_1834469).sum := by decide
  have hdescent : baseEnd_1834469 < baseStart_1834469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834488 : List Nat := [2, 1, 2, 1, 1, 5, 2, 1, 1, 7]
def baseStart_1834488 : Nat := 118140960795 + 1834488 * 2 ^ 59
def prefixEnd_1834488 : Nat := 4983230072969 + 3 ^ 40 * 1834488 * 2
def baseEnd_1834488 : Nat := 313991366301774596987783

theorem tailTrace_1834488 : CollatzResearch.WordTrace tailWord_1834488 prefixEnd_1834488 313991366301774596987783 := by
  unfold tailWord_1834488
  simp only [CollatzResearch.WordTrace]
  refine ⟨33454637088985378225988059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44606182785313837634650745 33454637088985378225988059)
  ·
    refine ⟨50181955633478067338982089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33454637088985378225988059 50181955633478067338982089)
    ·
      refine ⟨37636466725108550504236567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50181955633478067338982089 37636466725108550504236567)
      ·
        refine ⟨56454700087662825756354851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37636466725108550504236567 56454700087662825756354851)
        ·
          refine ⟨84682050131494238634532277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56454700087662825756354851 84682050131494238634532277)
          ·
            refine ⟨7938942199827584871987401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84682050131494238634532277 7938942199827584871987401)
            ·
              refine ⟨5954206649870688653990551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7938942199827584871987401 5954206649870688653990551)
              ·
                refine ⟨8931309974806032980985827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954206649870688653990551 8931309974806032980985827)
                ·
                  refine ⟨13396964962209049471478741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8931309974806032980985827 13396964962209049471478741)
                  ·
                    refine ⟨313991366301774596987783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13396964962209049471478741 313991366301774596987783)
                    ·
                      rfl

theorem cell23_1834488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_1834488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834488 prefixEnd_1834488 := by exact prefixLift 1834488
  have htrace : WordTrace (prefixWord ++ tailWord_1834488) baseStart_1834488 baseEnd_1834488 := by
    simpa [prefixWord, tailWord_1834488, baseEnd_1834488] using wordTrace_append hprefix tailTrace_1834488
  have hstable : (prefixWord ++ tailWord_1834488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834488).length < 2 ^ (prefixWord ++ tailWord_1834488).sum := by decide
  have hdescent : baseEnd_1834488 < baseStart_1834488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834525 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_1834525 : Nat := 118140960795 + 1834525 * 2 ^ 59
def prefixEnd_1834525 : Nat := 4983230072969 + 3 ^ 40 * 1834525 * 2
def baseEnd_1834525 : Nat := 941993097689540146200679

theorem tailTrace_1834525 : CollatzResearch.WordTrace tailWord_1834525 prefixEnd_1834525 941993097689540146200679 := by
  unfold tailWord_1834525
  simp only [CollatzResearch.WordTrace]
  refine ⟨66910623678836711771073029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44607082452557807847382019 66910623678836711771073029)
  ·
    refine ⟨12545741939781883457076193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66910623678836711771073029 12545741939781883457076193)
    ·
      refine ⟨9409306454836412592807145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12545741939781883457076193 9409306454836412592807145)
      ·
        refine ⟨7056979841127309444605359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9409306454836412592807145 7056979841127309444605359)
        ·
          refine ⟨10585469761690964166908039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056979841127309444605359 10585469761690964166908039)
          ·
            refine ⟨15878204642536446250362059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10585469761690964166908039 15878204642536446250362059)
            ·
              refine ⟨23817306963804669375543089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15878204642536446250362059 23817306963804669375543089)
              ·
                refine ⟨17862980222853502031657317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23817306963804669375543089 17862980222853502031657317)
                ·
                  refine ⟨3349308791785031630935747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17862980222853502031657317 3349308791785031630935747)
                  ·
                    refine ⟨5023963187677547446403621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3349308791785031630935747 5023963187677547446403621)
                    ·
                      refine ⟨941993097689540146200679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5023963187677547446403621 941993097689540146200679)
                      ·
                        rfl

theorem cell23_1834525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_1834525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834525 prefixEnd_1834525 := by exact prefixLift 1834525
  have htrace : WordTrace (prefixWord ++ tailWord_1834525) baseStart_1834525 baseEnd_1834525 := by
    simpa [prefixWord, tailWord_1834525, baseEnd_1834525] using wordTrace_append hprefix tailTrace_1834525
  have hstable : (prefixWord ++ tailWord_1834525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834525).length < 2 ^ (prefixWord ++ tailWord_1834525).sum := by decide
  have hdescent : baseEnd_1834525 < baseStart_1834525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834542 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1834542 : Nat := 118140960795 + 1834542 * 2 ^ 59
def prefixEnd_1834542 : Nat := 4983230072969 + 3 ^ 40 * 1834542 * 2
def baseEnd_1834542 : Nat := 942001826860666579688101

theorem tailTrace_1834542 : CollatzResearch.WordTrace tailWord_1834542 prefixEnd_1834542 942001826860666579688101 := by
  unfold tailWord_1834542
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363905464971890459305235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44607495813183415782961253 8363905464971890459305235)
  ·
    refine ⟨12545858197457835688957853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8363905464971890459305235 12545858197457835688957853)
    ·
      refine ⟨4704696824046688383359195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12545858197457835688957853 4704696824046688383359195)
      ·
        refine ⟨7057045236070032575038793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704696824046688383359195 7057045236070032575038793)
        ·
          refine ⟨5292783927052524431279095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057045236070032575038793 5292783927052524431279095)
          ·
            refine ⟨7939175890578786646918643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292783927052524431279095 7939175890578786646918643)
            ·
              refine ⟨11908763835868179970377965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939175890578786646918643 11908763835868179970377965)
              ·
                refine ⟨4465786438450567488891737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11908763835868179970377965 4465786438450567488891737)
                ·
                  refine ⟨3349339828837925616668803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4465786438450567488891737 3349339828837925616668803)
                  ·
                    refine ⟨5024009743256888425003205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3349339828837925616668803 5024009743256888425003205)
                    ·
                      refine ⟨942001826860666579688101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5024009743256888425003205 942001826860666579688101)
                      ·
                        rfl

theorem cell23_1834542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1834542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834542 prefixEnd_1834542 := by exact prefixLift 1834542
  have htrace : WordTrace (prefixWord ++ tailWord_1834542) baseStart_1834542 baseEnd_1834542 := by
    simpa [prefixWord, tailWord_1834542, baseEnd_1834542] using wordTrace_append hprefix tailTrace_1834542
  have hstable : (prefixWord ++ tailWord_1834542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834542).length < 2 ^ (prefixWord ++ tailWord_1834542).sum := by decide
  have hdescent : baseEnd_1834542 < baseStart_1834542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834565 : List Nat := [1, 3, 1, 1, 1, 4, 4, 2, 6]
def baseStart_1834565 : Nat := 118140960795 + 1834565 * 2 ^ 59
def prefixEnd_1834565 : Nat := 4983230072969 + 3 ^ 40 * 1834565 * 2
def baseEnd_1834565 : Nat := 104668181879524443300055

theorem tailTrace_1834565 : CollatzResearch.WordTrace tailWord_1834565 prefixEnd_1834565 104668181879524443300055 := by
  unfold tailWord_1834565
  simp only [CollatzResearch.WordTrace]
  refine ⟨66912082598691798602529149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44608055065794532401686099 66912082598691798602529149)
  ·
    refine ⟨25092030974509424475948431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66912082598691798602529149 25092030974509424475948431)
    ·
      refine ⟨37638046461764136713922647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25092030974509424475948431 37638046461764136713922647)
      ·
        refine ⟨56457069692646205070883971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37638046461764136713922647 56457069692646205070883971)
        ·
          refine ⟨84685604538969307606325957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56457069692646205070883971 84685604538969307606325957)
          ·
            refine ⟨15878550851056745176186117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84685604538969307606325957 15878550851056745176186117)
            ·
              refine ⟨2977228284573139720534897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15878550851056745176186117 2977228284573139720534897)
              ·
                refine ⟨2232921213429854790401173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977228284573139720534897 2232921213429854790401173)
                ·
                  refine ⟨104668181879524443300055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2232921213429854790401173 104668181879524443300055)
                  ·
                    rfl

theorem cell23_1834565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_1834565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834565 prefixEnd_1834565 := by exact prefixLift 1834565
  have htrace : WordTrace (prefixWord ++ tailWord_1834565) baseStart_1834565 baseEnd_1834565 := by
    simpa [prefixWord, tailWord_1834565, baseEnd_1834565] using wordTrace_append hprefix tailTrace_1834565
  have hstable : (prefixWord ++ tailWord_1834565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834565).length < 2 ^ (prefixWord ++ tailWord_1834565).sum := by decide
  have hdescent : baseEnd_1834565 < baseStart_1834565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834595 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 3, 5]
def baseStart_1834595 : Nat := 118140960795 + 1834595 * 2 ^ 59
def prefixEnd_1834595 : Nat := 4983230072969 + 3 ^ 40 * 1834595 * 2
def baseEnd_1834595 : Nat := 314009680445118290775119

theorem tailTrace_1834595 : CollatzResearch.WordTrace tailWord_1834595 prefixEnd_1834595 314009680445118290775119 := by
  unfold tailWord_1834595
  simp only [CollatzResearch.WordTrace]
  refine ⟨66913176788583113726121239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44608784525722075817414159 66913176788583113726121239)
  ·
    refine ⟨100369765182874670589181859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66913176788583113726121239 100369765182874670589181859)
    ·
      refine ⟨150554647774312005883772789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100369765182874670589181859 150554647774312005883772789)
      ·
        refine ⟨14114498228841750551603699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150554647774312005883772789 14114498228841750551603699)
        ·
          refine ⟨21171747343262625827405549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14114498228841750551603699 21171747343262625827405549)
          ·
            refine ⟨7939405253723484685277081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21171747343262625827405549 7939405253723484685277081)
            ·
              refine ⟨5954553940292613513957811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939405253723484685277081 5954553940292613513957811)
              ·
                refine ⟨8931830910438920270936717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954553940292613513957811 8931830910438920270936717)
                ·
                  refine ⟨3349436591414595101601269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8931830910438920270936717 3349436591414595101601269)
                  ·
                    refine ⟨314009680445118290775119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3349436591414595101601269 314009680445118290775119)
                    ·
                      rfl

theorem cell23_1834595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 3, 5].length) (baseStart_1834595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834595 prefixEnd_1834595 := by exact prefixLift 1834595
  have htrace : WordTrace (prefixWord ++ tailWord_1834595) baseStart_1834595 baseEnd_1834595 := by
    simpa [prefixWord, tailWord_1834595, baseEnd_1834595] using wordTrace_append hprefix tailTrace_1834595
  have hstable : (prefixWord ++ tailWord_1834595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834595).length < 2 ^ (prefixWord ++ tailWord_1834595).sum := by decide
  have hdescent : baseEnd_1834595 < baseStart_1834595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834635 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5]
def baseStart_1834635 : Nat := 118140960795 + 1834635 * 2 ^ 59
def prefixEnd_1834635 : Nat := 4983230072969 + 3 ^ 40 * 1834635 * 2
def baseEnd_1834635 : Nat := 942049580561534715825173

theorem tailTrace_1834635 : CollatzResearch.WordTrace tailWord_1834635 prefixEnd_1834635 942049580561534715825173 := by
  unfold tailWord_1834635
  simp only [CollatzResearch.WordTrace]
  refine ⟨66914635708438200557577359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44609757138958800371718239 66914635708438200557577359)
  ·
    refine ⟨100371953562657300836366039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66914635708438200557577359 100371953562657300836366039)
    ·
      refine ⟨150557930343985951254549059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100371953562657300836366039 150557930343985951254549059)
      ·
        refine ⟨225836895515978926881823589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150557930343985951254549059 225836895515978926881823589)
        ·
          refine ⟨42344417909246048790341923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225836895515978926881823589 42344417909246048790341923)
          ·
            refine ⟨63516626863869073185512885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42344417909246048790341923 63516626863869073185512885)
            ·
              refine ⟨5954683768487725611141833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63516626863869073185512885 5954683768487725611141833)
              ·
                refine ⟨4466012826365794208356375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954683768487725611141833 4466012826365794208356375)
                ·
                  refine ⟨6699019239548691312534563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466012826365794208356375 6699019239548691312534563)
                  ·
                    refine ⟨10048528859323036968801845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6699019239548691312534563 10048528859323036968801845)
                    ·
                      refine ⟨942049580561534715825173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10048528859323036968801845 942049580561534715825173)
                      ·
                        rfl

theorem cell23_1834635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 5].length) (baseStart_1834635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834635 prefixEnd_1834635 := by exact prefixLift 1834635
  have htrace : WordTrace (prefixWord ++ tailWord_1834635) baseStart_1834635 baseEnd_1834635 := by
    simpa [prefixWord, tailWord_1834635, baseEnd_1834635] using wordTrace_append hprefix tailTrace_1834635
  have hstable : (prefixWord ++ tailWord_1834635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834635).length < 2 ^ (prefixWord ++ tailWord_1834635).sum := by decide
  have hdescent : baseEnd_1834635 < baseStart_1834635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834669 : List Nat := [1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 3]
def baseStart_1834669 : Nat := 118140960795 + 1834669 * 2 ^ 59
def prefixEnd_1834669 : Nat := 4983230072969 + 3 ^ 40 * 1834669 * 2
def baseEnd_1834669 : Nat := 942067038903787582800017

theorem tailTrace_1834669 : CollatzResearch.WordTrace tailWord_1834669 prefixEnd_1834669 942067038903787582800017 := by
  unfold tailWord_1834669
  simp only [CollatzResearch.WordTrace]
  refine ⟨66915875790315024364315061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44610583860210016242876707 66915875790315024364315061)
  ·
    refine ⟨6273363355342033534154537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66915875790315024364315061 6273363355342033534154537)
    ·
      refine ⟨4705022516506525150615903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6273363355342033534154537 4705022516506525150615903)
      ·
        refine ⟨7057533774759787725923855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705022516506525150615903 7057533774759787725923855)
        ·
          refine ⟨10586300662139681588885783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057533774759787725923855 10586300662139681588885783)
          ·
            refine ⟨15879450993209522383328675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10586300662139681588885783 15879450993209522383328675)
            ·
              refine ⟨23819176489814283574993013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15879450993209522383328675 23819176489814283574993013)
              ·
                refine ⟨2233047795920089085155595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23819176489814283574993013 2233047795920089085155595)
                ·
                  refine ⟨3349571693880133627733393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233047795920089085155595 3349571693880133627733393)
                  ·
                    refine ⟨2512178770410100220800045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3349571693880133627733393 2512178770410100220800045)
                    ·
                      refine ⟨942067038903787582800017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512178770410100220800045 942067038903787582800017)
                      ·
                        rfl

theorem cell23_1834669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_1834669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834669 prefixEnd_1834669 := by exact prefixLift 1834669
  have htrace : WordTrace (prefixWord ++ tailWord_1834669) baseStart_1834669 baseEnd_1834669 := by
    simpa [prefixWord, tailWord_1834669, baseEnd_1834669] using wordTrace_append hprefix tailTrace_1834669
  have hstable : (prefixWord ++ tailWord_1834669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834669).length < 2 ^ (prefixWord ++ tailWord_1834669).sum := by decide
  have hdescent : baseEnd_1834669 < baseStart_1834669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834685 : List Nat := [1, 4, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1834685 : Nat := 118140960795 + 1834685 * 2 ^ 59
def prefixEnd_1834685 : Nat := 4983230072969 + 3 ^ 40 * 1834685 * 2
def baseEnd_1834685 : Nat := 314025084864753173399981

theorem tailTrace_1834685 : CollatzResearch.WordTrace tailWord_1834685 prefixEnd_1834685 314025084864753173399981 := by
  unfold tailWord_1834685
  simp only [CollatzResearch.WordTrace]
  refine ⟨66916459358257059096897509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44610972905504706064598339 66916459358257059096897509)
  ·
    refine ⟨12546836129673198580668283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66916459358257059096897509 12546836129673198580668283)
    ·
      refine ⟨18820254194509797871002425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12546836129673198580668283 18820254194509797871002425)
      ·
        refine ⟨14115190645882348403251819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18820254194509797871002425 14115190645882348403251819)
        ·
          refine ⟨21172785968823522604877729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14115190645882348403251819 21172785968823522604877729)
          ·
            refine ⟨15879589476617641953658297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21172785968823522604877729 15879589476617641953658297)
            ·
              refine ⟨11909692107463231465243723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15879589476617641953658297 11909692107463231465243723)
              ·
                refine ⟨17864538161194847197865585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11909692107463231465243723 17864538161194847197865585)
                ·
                  refine ⟨13398403620896135398399189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17864538161194847197865585 13398403620896135398399189)
                  ·
                    refine ⟨314025084864753173399981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13398403620896135398399189 314025084864753173399981)
                    ·
                      rfl

theorem cell23_1834685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1834685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834685 prefixEnd_1834685 := by exact prefixLift 1834685
  have htrace : WordTrace (prefixWord ++ tailWord_1834685) baseStart_1834685 baseEnd_1834685 := by
    simpa [prefixWord, tailWord_1834685, baseEnd_1834685] using wordTrace_append hprefix tailTrace_1834685
  have hstable : (prefixWord ++ tailWord_1834685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834685).length < 2 ^ (prefixWord ++ tailWord_1834685).sum := by decide
  have hdescent : baseEnd_1834685 < baseStart_1834685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834716 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1834716 : Nat := 118140960795 + 1834716 * 2 ^ 59
def prefixEnd_1834716 : Nat := 4983230072969 + 3 ^ 40 * 1834716 * 2
def baseEnd_1834716 : Nat := 942091172494548898912301

theorem tailTrace_1834716 : CollatzResearch.WordTrace tailWord_1834716 prefixEnd_1834716 942091172494548898912301 := by
  unfold tailWord_1834716
  simp only [CollatzResearch.WordTrace]
  refine ⟨33458795010572375695638001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44611726680763167594184001 33458795010572375695638001)
  ·
    refine ⟨25094096257929281771728501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33458795010572375695638001 25094096257929281771728501)
    ·
      refine ⟨2352571524180870166099547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25094096257929281771728501 2352571524180870166099547)
      ·
        refine ⟨3528857286271305249149321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352571524180870166099547 3528857286271305249149321)
        ·
          refine ⟨2646642964703478936861991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3528857286271305249149321 2646642964703478936861991)
          ·
            refine ⟨3969964447055218405292987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646642964703478936861991 3969964447055218405292987)
            ·
              refine ⟨5954946670582827607939481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969964447055218405292987 5954946670582827607939481)
              ·
                refine ⟨4466210002937120705954611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954946670582827607939481 4466210002937120705954611)
                ·
                  refine ⟨6699315004405681058931917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466210002937120705954611 6699315004405681058931917)
                  ·
                    refine ⟨2512243126652130397099469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6699315004405681058931917 2512243126652130397099469)
                    ·
                      refine ⟨942091172494548898912301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512243126652130397099469 942091172494548898912301)
                      ·
                        rfl

theorem cell23_1834716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1834716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834716 prefixEnd_1834716 := by exact prefixLift 1834716
  have htrace : WordTrace (prefixWord ++ tailWord_1834716) baseStart_1834716 baseEnd_1834716 := by
    simpa [prefixWord, tailWord_1834716, baseEnd_1834716] using wordTrace_append hprefix tailTrace_1834716
  have hstable : (prefixWord ++ tailWord_1834716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834716).length < 2 ^ (prefixWord ++ tailWord_1834716).sum := by decide
  have hdescent : baseEnd_1834716 < baseStart_1834716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834739 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 4, 2, 2]
def baseStart_1834739 : Nat := 118140960795 + 1834739 * 2 ^ 59
def prefixEnd_1834739 : Nat := 4983230072969 + 3 ^ 40 * 1834739 * 2
def baseEnd_1834739 : Nat := 942102982549602308924695

theorem tailTrace_1834739 : CollatzResearch.WordTrace tailWord_1834739 prefixEnd_1834739 942102982549602308924695 := by
  unfold tailWord_1834739
  simp only [CollatzResearch.WordTrace]
  refine ⟨66918428900061426319363271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44612285933374284212908847 66918428900061426319363271)
  ·
    refine ⟨100377643350092139479044907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66918428900061426319363271 100377643350092139479044907)
    ·
      refine ⟨150566465025138209218567361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100377643350092139479044907 150566465025138209218567361)
      ·
        refine ⟨112924848768853656913925521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150566465025138209218567361 112924848768853656913925521)
        ·
          refine ⟨84693636576640242685444141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112924848768853656913925521 84693636576640242685444141)
          ·
            refine ⟨31760113716240091007041553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84693636576640242685444141 31760113716240091007041553)
            ·
              refine ⟨23820085287180068255281165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31760113716240091007041553 23820085287180068255281165)
              ·
                refine ⟨8932531982692525595730437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23820085287180068255281165 8932531982692525595730437)
                ·
                  refine ⟨1674849746754848549199457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8932531982692525595730437 1674849746754848549199457)
                  ·
                    refine ⟨1256137310066136411899593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1674849746754848549199457 1256137310066136411899593)
                    ·
                      refine ⟨942102982549602308924695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256137310066136411899593 942102982549602308924695)
                      ·
                        rfl

theorem cell23_1834739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 2, 2].length) (baseStart_1834739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834739 prefixEnd_1834739 := by exact prefixLift 1834739
  have htrace : WordTrace (prefixWord ++ tailWord_1834739) baseStart_1834739 baseEnd_1834739 := by
    simpa [prefixWord, tailWord_1834739, baseEnd_1834739] using wordTrace_append hprefix tailTrace_1834739
  have hstable : (prefixWord ++ tailWord_1834739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834739).length < 2 ^ (prefixWord ++ tailWord_1834739).sum := by decide
  have hdescent : baseEnd_1834739 < baseStart_1834739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834756 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 1, 4, 2]
def baseStart_1834756 : Nat := 118140960795 + 1834756 * 2 ^ 59
def prefixEnd_1834756 : Nat := 4983230072969 + 3 ^ 40 * 1834756 * 2
def baseEnd_1834756 : Nat := 942111711720728742412117

theorem tailTrace_1834756 : CollatzResearch.WordTrace tailWord_1834756 prefixEnd_1834756 942111711720728742412117 := by
  unfold tailWord_1834756
  simp only [CollatzResearch.WordTrace]
  refine ⟨33459524470499919111366061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44612699293999892148488081 33459524470499919111366061)
  ·
    refine ⟨12547321676437469666762273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33459524470499919111366061 12547321676437469666762273)
    ·
      refine ⟨9410491257328102250071705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12547321676437469666762273 9410491257328102250071705)
      ·
        refine ⟨7057868442996076687553779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9410491257328102250071705 7057868442996076687553779)
        ·
          refine ⟨10586802664494115031330669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057868442996076687553779 10586802664494115031330669)
          ·
            refine ⟨3970050999185293136749001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10586802664494115031330669 3970050999185293136749001)
            ·
              refine ⟨2977538249388969852561751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970050999185293136749001 2977538249388969852561751)
              ·
                refine ⟨4466307374083454778842627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977538249388969852561751 4466307374083454778842627)
                ·
                  refine ⟨6699461061125182168263941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466307374083454778842627 6699461061125182168263941)
                  ·
                    refine ⟨1256148948960971656549489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6699461061125182168263941 1256148948960971656549489)
                    ·
                      refine ⟨942111711720728742412117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256148948960971656549489 942111711720728742412117)
                      ·
                        rfl

theorem cell23_1834756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_1834756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834756 prefixEnd_1834756 := by exact prefixLift 1834756
  have htrace : WordTrace (prefixWord ++ tailWord_1834756) baseStart_1834756 baseEnd_1834756 := by
    simpa [prefixWord, tailWord_1834756, baseEnd_1834756] using wordTrace_append hprefix tailTrace_1834756
  have hstable : (prefixWord ++ tailWord_1834756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834756).length < 2 ^ (prefixWord ++ tailWord_1834756).sum := by decide
  have hdescent : baseEnd_1834756 < baseStart_1834756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834762 : List Nat := [3, 1, 2, 2, 1, 4, 1, 2, 7]
def baseStart_1834762 : Nat := 118140960795 + 1834762 * 2 ^ 59
def prefixEnd_1834762 : Nat := 4983230072969 + 3 ^ 40 * 1834762 * 2
def baseEnd_1834762 : Nat := 104679421400517302104121

theorem tailTrace_1834762 : CollatzResearch.WordTrace tailWord_1834762 prefixEnd_1834762 104679421400517302104121 := by
  unfold tailWord_1834762
  simp only [CollatzResearch.WordTrace]
  refine ⟨16729816944744525311862635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44612845185985400831633693 16729816944744525311862635)
  ·
    refine ⟨25094725417116787967793953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16729816944744525311862635 25094725417116787967793953)
    ·
      refine ⟨18821044062837590975845465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25094725417116787967793953 18821044062837590975845465)
      ·
        refine ⟨14115783047128193231884099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18821044062837590975845465 14115783047128193231884099)
        ·
          refine ⟨21173674570692289847826149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14115783047128193231884099 21173674570692289847826149)
          ·
            refine ⟨3970063982004804346467403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21173674570692289847826149 3970063982004804346467403)
            ·
              refine ⟨5955095973007206519701105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970063982004804346467403 5955095973007206519701105)
              ·
                refine ⟨4466321979755404889775829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955095973007206519701105 4466321979755404889775829)
                ·
                  refine ⟨104679421400517302104121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4466321979755404889775829 104679421400517302104121)
                  ·
                    rfl

theorem cell23_1834762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 7].length) (baseStart_1834762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834762 prefixEnd_1834762 := by exact prefixLift 1834762
  have htrace : WordTrace (prefixWord ++ tailWord_1834762) baseStart_1834762 baseEnd_1834762 := by
    simpa [prefixWord, tailWord_1834762, baseEnd_1834762] using wordTrace_append hprefix tailTrace_1834762
  have hstable : (prefixWord ++ tailWord_1834762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834762).length < 2 ^ (prefixWord ++ tailWord_1834762).sum := by decide
  have hdescent : baseEnd_1834762 < baseStart_1834762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834806 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1834806 : Nat := 118140960795 + 1834806 * 2 ^ 59
def prefixEnd_1834806 : Nat := 4983230072969 + 3 ^ 40 * 1834806 * 2
def baseEnd_1834806 : Nat := 942137385753453546786887

theorem tailTrace_1834806 : CollatzResearch.WordTrace tailWord_1834806 prefixEnd_1834806 942137385753453546786887 := by
  unfold tailWord_1834806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4182554536926168547628267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44613915060545797841368181 4182554536926168547628267)
  ·
    refine ⟨6273831805389252821442401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4182554536926168547628267 6273831805389252821442401)
    ·
      refine ⟨4705373854041939616081801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6273831805389252821442401 4705373854041939616081801)
      ·
        refine ⟨3529030390531454712061351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4705373854041939616081801 3529030390531454712061351)
        ·
          refine ⟨5293545585797182068092027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529030390531454712061351 5293545585797182068092027)
          ·
            refine ⟨7940318378695773102138041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5293545585797182068092027 7940318378695773102138041)
            ·
              refine ⟨5955238784021829826603531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940318378695773102138041 5955238784021829826603531)
              ·
                refine ⟨8932858176032744739905297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955238784021829826603531 8932858176032744739905297)
                ·
                  refine ⟨6699643632024558554928973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8932858176032744739905297 6699643632024558554928973)
                  ·
                    refine ⟨2512366362009209458098365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6699643632024558554928973 2512366362009209458098365)
                    ·
                      refine ⟨942137385753453546786887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512366362009209458098365 942137385753453546786887)
                      ·
                        rfl

theorem cell23_1834806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1834806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834806 prefixEnd_1834806 := by exact prefixLift 1834806
  have htrace : WordTrace (prefixWord ++ tailWord_1834806) baseStart_1834806 baseEnd_1834806 := by
    simpa [prefixWord, tailWord_1834806, baseEnd_1834806] using wordTrace_append hprefix tailTrace_1834806
  have hstable : (prefixWord ++ tailWord_1834806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834806).length < 2 ^ (prefixWord ++ tailWord_1834806).sum := by decide
  have hdescent : baseEnd_1834806 < baseStart_1834806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834812 : List Nat := [2, 2, 2, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1834812 : Nat := 118140960795 + 1834812 * 2 ^ 59
def prefixEnd_1834812 : Nat := 4983230072969 + 3 ^ 40 * 1834812 * 2
def baseEnd_1834812 : Nat := 942140466637380523311859

theorem tailTrace_1834812 : CollatzResearch.WordTrace tailWord_1834812 prefixEnd_1834812 942140466637380523311859 := by
  unfold tailWord_1834812
  simp only [CollatzResearch.WordTrace]
  refine ⟨33460545714398479893385345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44614060952531306524513793 33460545714398479893385345)
  ·
    refine ⟨25095409285798859920039009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33460545714398479893385345 25095409285798859920039009)
    ·
      refine ⟨18821556964349144940029257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25095409285798859920039009 18821556964349144940029257)
      ·
        refine ⟨14116167723261858705021943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18821556964349144940029257 14116167723261858705021943)
        ·
          refine ⟨21174251584892788057532915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14116167723261858705021943 21174251584892788057532915)
          ·
            refine ⟨31761377377339182086299373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21174251584892788057532915 31761377377339182086299373)
            ·
              refine ⟨11910516516502193282362265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31761377377339182086299373 11910516516502193282362265)
              ·
                refine ⟨8932887387376644961771699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11910516516502193282362265 8932887387376644961771699)
                ·
                  refine ⟨13399331081064967442657549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8932887387376644961771699 13399331081064967442657549)
                  ·
                    refine ⟨5024749155399362790996581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13399331081064967442657549 5024749155399362790996581)
                    ·
                      refine ⟨942140466637380523311859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5024749155399362790996581 942140466637380523311859)
                      ·
                        rfl

theorem cell23_1834812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1834812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834812 prefixEnd_1834812 := by exact prefixLift 1834812
  have htrace : WordTrace (prefixWord ++ tailWord_1834812) baseStart_1834812 baseEnd_1834812 := by
    simpa [prefixWord, tailWord_1834812, baseEnd_1834812] using wordTrace_append hprefix tailTrace_1834812
  have hstable : (prefixWord ++ tailWord_1834812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834812).length < 2 ^ (prefixWord ++ tailWord_1834812).sum := by decide
  have hdescent : baseEnd_1834812 < baseStart_1834812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834849 : List Nat := [1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 3]
def baseStart_1834849 : Nat := 118140960795 + 1834849 * 2 ^ 59
def prefixEnd_1834849 : Nat := 4983230072969 + 3 ^ 40 * 1834849 * 2
def baseEnd_1834849 : Nat := 942159465421596878549189

theorem tailTrace_1834849 : CollatzResearch.WordTrace tailWord_1834849 prefixEnd_1834849 942159465421596878549189 := by
  unfold tailWord_1834849
  simp only [CollatzResearch.WordTrace]
  refine ⟨66922440929662915105867601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44614960619775276737245067 66922440929662915105867601)
  ·
    refine ⟨50191830697247186329400701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66922440929662915105867601 50191830697247186329400701)
    ·
      refine ⟨18821936511467694873525263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50191830697247186329400701 18821936511467694873525263)
      ·
        refine ⟨28232904767201542310287895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18821936511467694873525263 28232904767201542310287895)
        ·
          refine ⟨42349357150802313465431843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28232904767201542310287895 42349357150802313465431843)
          ·
            refine ⟨63524035726203470198147765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42349357150802313465431843 63524035726203470198147765)
            ·
              refine ⟨5955378349331575331076353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63524035726203470198147765 5955378349331575331076353)
              ·
                refine ⟨4466533761998681498307265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955378349331575331076353 4466533761998681498307265)
                ·
                  refine ⟨3349900321499011123730449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4466533761998681498307265 3349900321499011123730449)
                  ·
                    refine ⟨2512425241124258342797837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3349900321499011123730449 2512425241124258342797837)
                    ·
                      refine ⟨942159465421596878549189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512425241124258342797837 942159465421596878549189)
                      ·
                        rfl

theorem cell23_1834849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_1834849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834849 prefixEnd_1834849 := by exact prefixLift 1834849
  have htrace : WordTrace (prefixWord ++ tailWord_1834849) baseStart_1834849 baseEnd_1834849 := by
    simpa [prefixWord, tailWord_1834849, baseEnd_1834849] using wordTrace_append hprefix tailTrace_1834849
  have hstable : (prefixWord ++ tailWord_1834849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834849).length < 2 ^ (prefixWord ++ tailWord_1834849).sum := by decide
  have hdescent : baseEnd_1834849 < baseStart_1834849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834869 : List Nat := [1, 3, 4, 1, 1, 1, 3, 3, 6]
def baseStart_1834869 : Nat := 118140960795 + 1834869 * 2 ^ 59
def prefixEnd_1834869 : Nat := 4983230072969 + 3 ^ 40 * 1834869 * 2
def baseEnd_1834869 : Nat := 104685526114965200033233

theorem tailTrace_1834869 : CollatzResearch.WordTrace tailWord_1834869 prefixEnd_1834869 104685526114965200033233 := by
  unfold tailWord_1834869
  simp only [CollatzResearch.WordTrace]
  refine ⟨66923170389590458521595661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44615446926393639014397107 66923170389590458521595661)
  ·
    refine ⟨25096188896096421945598373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66923170389590458521595661 25096188896096421945598373)
    ·
      refine ⟨4705535418018079114799695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25096188896096421945598373 4705535418018079114799695)
      ·
        refine ⟨7058303127027118672199543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705535418018079114799695 7058303127027118672199543)
        ·
          refine ⟨10587454690540678008299315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7058303127027118672199543 10587454690540678008299315)
          ·
            refine ⟨15881182035811017012448973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10587454690540678008299315 15881182035811017012448973)
            ·
              refine ⟨5955443263429131379668365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15881182035811017012448973 5955443263429131379668365)
              ·
                refine ⟨2233291223785924267375637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5955443263429131379668365 2233291223785924267375637)
                ·
                  refine ⟨104685526114965200033233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2233291223785924267375637 104685526114965200033233)
                  ·
                    rfl

theorem cell23_1834869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_1834869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834869 prefixEnd_1834869 := by exact prefixLift 1834869
  have htrace : WordTrace (prefixWord ++ tailWord_1834869) baseStart_1834869 baseEnd_1834869 := by
    simpa [prefixWord, tailWord_1834869, baseEnd_1834869] using wordTrace_append hprefix tailTrace_1834869
  have hstable : (prefixWord ++ tailWord_1834869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834869).length < 2 ^ (prefixWord ++ tailWord_1834869).sum := by decide
  have hdescent : baseEnd_1834869 < baseStart_1834869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834879 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 3]
def baseStart_1834879 : Nat := 118140960795 + 1834879 * 2 ^ 59
def prefixEnd_1834879 : Nat := 4983230072969 + 3 ^ 40 * 1834879 * 2
def baseEnd_1834879 : Nat := 942174869841231761174051

theorem tailTrace_1834879 : CollatzResearch.WordTrace tailWord_1834879 prefixEnd_1834879 942174869841231761174051 := by
  unfold tailWord_1834879
  simp only [CollatzResearch.WordTrace]
  refine ⟨66923535119554230229459691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44615690079702820152973127 66923535119554230229459691)
  ·
    refine ⟨100385302679331345344189537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66923535119554230229459691 100385302679331345344189537)
    ·
      refine ⟨75288977009498509008142153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100385302679331345344189537 75288977009498509008142153)
      ·
        refine ⟨56466732757123881756106615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75288977009498509008142153 56466732757123881756106615)
        ·
          refine ⟨84700099135685822634159923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56466732757123881756106615 84700099135685822634159923)
          ·
            refine ⟨127050148703528733951239885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84700099135685822634159923 127050148703528733951239885)
            ·
              refine ⟨47643805763823275231714957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127050148703528733951239885 47643805763823275231714957)
              ·
                refine ⟨17866427161433728211893109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47643805763823275231714957 17866427161433728211893109)
                ·
                  refine ⟨1674977546384412019864979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17866427161433728211893109 1674977546384412019864979)
                  ·
                    refine ⟨2512466319576618029797469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1674977546384412019864979 2512466319576618029797469)
                    ·
                      refine ⟨942174869841231761174051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512466319576618029797469 942174869841231761174051)
                      ·
                        rfl

theorem cell23_1834879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_1834879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834879 prefixEnd_1834879 := by exact prefixLift 1834879
  have htrace : WordTrace (prefixWord ++ tailWord_1834879) baseStart_1834879 baseEnd_1834879 := by
    simpa [prefixWord, tailWord_1834879, baseEnd_1834879] using wordTrace_append hprefix tailTrace_1834879
  have hstable : (prefixWord ++ tailWord_1834879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834879).length < 2 ^ (prefixWord ++ tailWord_1834879).sum := by decide
  have hdescent : baseEnd_1834879 < baseStart_1834879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834912 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 5, 6]
def baseStart_1834912 : Nat := 118140960795 + 1834912 * 2 ^ 59
def prefixEnd_1834912 : Nat := 4983230072969 + 3 ^ 40 * 1834912 * 2
def baseEnd_1834912 : Nat := 314063938234276710687133

theorem tailTrace_1834912 : CollatzResearch.WordTrace tailWord_1834912 prefixEnd_1834912 314063938234276710687133 := by
  unfold tailWord_1834912
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462369364217338432705495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44616492485623117910273993 33462369364217338432705495)
  ·
    refine ⟨50193554046326007649058243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462369364217338432705495 50193554046326007649058243)
    ·
      refine ⟨75290331069489011473587365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193554046326007649058243 75290331069489011473587365)
      ·
        refine ⟨14116937075529189651297631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75290331069489011473587365 14116937075529189651297631)
        ·
          refine ⟨21175405613293784476946447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14116937075529189651297631 21175405613293784476946447)
          ·
            refine ⟨31763108419940676715419671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21175405613293784476946447 31763108419940676715419671)
            ·
              refine ⟨47644662629911015073129507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31763108419940676715419671 47644662629911015073129507)
              ·
                refine ⟨71466993944866522609694261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47644662629911015073129507 71466993944866522609694261)
                ·
                  refine ⟨6700030682331236494658837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71466993944866522609694261 6700030682331236494658837)
                  ·
                    refine ⟨314063938234276710687133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6700030682331236494658837 314063938234276710687133)
                    ·
                      rfl

theorem cell23_1834912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 5, 6].length) (baseStart_1834912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834912 prefixEnd_1834912 := by exact prefixLift 1834912
  have htrace : WordTrace (prefixWord ++ tailWord_1834912) baseStart_1834912 baseEnd_1834912 := by
    simpa [prefixWord, tailWord_1834912, baseEnd_1834912] using wordTrace_append hprefix tailTrace_1834912
  have hstable : (prefixWord ++ tailWord_1834912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834912).length < 2 ^ (prefixWord ++ tailWord_1834912).sum := by decide
  have hdescent : baseEnd_1834912 < baseStart_1834912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834929 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_1834929 : Nat := 118140960795 + 1834929 * 2 ^ 59
def prefixEnd_1834929 : Nat := 4983230072969 + 3 ^ 40 * 1834929 * 2
def baseEnd_1834929 : Nat := 314066847957985521849607

theorem tailTrace_1834929 : CollatzResearch.WordTrace tailWord_1834929 prefixEnd_1834929 314066847957985521849607 := by
  unfold tailWord_1834929
  simp only [CollatzResearch.WordTrace]
  refine ⟨66925358769373088768779841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44616905846248725845853227 66925358769373088768779841)
  ·
    refine ⟨50194019077029816576584881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66925358769373088768779841 50194019077029816576584881)
    ·
      refine ⟨37645514307772362432438661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50194019077029816576584881 37645514307772362432438661)
      ·
        refine ⟨7058533932707317956082249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37645514307772362432438661 7058533932707317956082249)
        ·
          refine ⟨5293900449530488467061687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7058533932707317956082249 5293900449530488467061687)
          ·
            refine ⟨7940850674295732700592531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5293900449530488467061687 7940850674295732700592531)
            ·
              refine ⟨11911276011443599050888797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7940850674295732700592531 11911276011443599050888797)
              ·
                refine ⟨4466728504291349644083299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11911276011443599050888797 4466728504291349644083299)
                ·
                  refine ⟨6700092756437024466124949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466728504291349644083299 6700092756437024466124949)
                  ·
                    refine ⟨314066847957985521849607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6700092756437024466124949 314066847957985521849607)
                    ·
                      rfl

theorem cell23_1834929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_1834929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834929 prefixEnd_1834929 := by exact prefixLift 1834929
  have htrace : WordTrace (prefixWord ++ tailWord_1834929) baseStart_1834929 baseEnd_1834929 := by
    simpa [prefixWord, tailWord_1834929, baseEnd_1834929] using wordTrace_append hprefix tailTrace_1834929
  have hstable : (prefixWord ++ tailWord_1834929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834929).length < 2 ^ (prefixWord ++ tailWord_1834929).sum := by decide
  have hdescent : baseEnd_1834929 < baseStart_1834929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834970 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2]
def baseStart_1834970 : Nat := 118140960795 + 1834970 * 2 ^ 59
def prefixEnd_1834970 : Nat := 4983230072969 + 3 ^ 40 * 1834970 * 2
def baseEnd_1834970 : Nat := 942221596580790905136133

theorem tailTrace_1834970 : CollatzResearch.WordTrace tailWord_1834970 prefixEnd_1834970 942221596580790905136133 := by
  unfold tailWord_1834970
  simp only [CollatzResearch.WordTrace]
  refine ⟨16731713540556138192755591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44617902774816368514014909 16731713540556138192755591)
  ·
    refine ⟨25097570310834207289133387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16731713540556138192755591 25097570310834207289133387)
    ·
      refine ⟨37646355466251310933700081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25097570310834207289133387 37646355466251310933700081)
      ·
        refine ⟨28234766599688483200275061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37646355466251310933700081 28234766599688483200275061)
        ·
          refine ⟨2647009368720795300025787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28234766599688483200275061 2647009368720795300025787)
          ·
            refine ⟨3970514053081192950038681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647009368720795300025787 3970514053081192950038681)
            ·
              refine ⟨2977885539810894712529011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970514053081192950038681 2977885539810894712529011)
              ·
                refine ⟨4466828309716342068793517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977885539810894712529011 4466828309716342068793517)
                ·
                  refine ⟨1675060616143628275797569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4466828309716342068793517 1675060616143628275797569)
                  ·
                    refine ⟨1256295462107721206848177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675060616143628275797569 1256295462107721206848177)
                    ·
                      refine ⟨942221596580790905136133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256295462107721206848177 942221596580790905136133)
                      ·
                        rfl

theorem cell23_1834970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 2, 2].length) (baseStart_1834970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834970 prefixEnd_1834970 := by exact prefixLift 1834970
  have htrace : WordTrace (prefixWord ++ tailWord_1834970) baseStart_1834970 baseEnd_1834970 := by
    simpa [prefixWord, tailWord_1834970, baseEnd_1834970] using wordTrace_append hprefix tailTrace_1834970
  have hstable : (prefixWord ++ tailWord_1834970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834970).length < 2 ^ (prefixWord ++ tailWord_1834970).sum := by decide
  have hdescent : baseEnd_1834970 < baseStart_1834970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834983 : List Nat := [1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1834983 : Nat := 118140960795 + 1834983 * 2 ^ 59
def prefixEnd_1834983 : Nat := 4983230072969 + 3 ^ 40 * 1834983 * 2
def baseEnd_1834983 : Nat := 942228271829299354273573

theorem tailTrace_1834983 : CollatzResearch.WordTrace tailWord_1834983 prefixEnd_1834983 942228271829299354273573 := by
  unfold tailWord_1834983
  simp only [CollatzResearch.WordTrace]
  refine ⟨66927328311177455991245603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44618218874118303994163735 66927328311177455991245603)
  ·
    refine ⟨100390992466766183986868405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66927328311177455991245603 100390992466766183986868405)
    ·
      refine ⟨9411655543759329748768913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100390992466766183986868405 9411655543759329748768913)
      ·
        refine ⟨7058741657819497311576685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9411655543759329748768913 7058741657819497311576685)
        ·
          refine ⟨2647028121682311491841257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7058741657819497311576685 2647028121682311491841257)
          ·
            refine ⟨1985271091261733618880943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647028121682311491841257 1985271091261733618880943)
            ·
              refine ⟨2977906636892600428321415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985271091261733618880943 2977906636892600428321415)
              ·
                refine ⟨4466859955338900642482123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977906636892600428321415 4466859955338900642482123)
                ·
                  refine ⟨6700289933008350963723185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466859955338900642482123 6700289933008350963723185)
                  ·
                    refine ⟨5025217449756263222792389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6700289933008350963723185 5025217449756263222792389)
                    ·
                      refine ⟨942228271829299354273573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5025217449756263222792389 942228271829299354273573)
                      ·
                        rfl

theorem cell23_1834983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1834983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834983 prefixEnd_1834983 := by exact prefixLift 1834983
  have htrace : WordTrace (prefixWord ++ tailWord_1834983) baseStart_1834983 baseEnd_1834983 := by
    simpa [prefixWord, tailWord_1834983, baseEnd_1834983] using wordTrace_append hprefix tailTrace_1834983
  have hstable : (prefixWord ++ tailWord_1834983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834983).length < 2 ^ (prefixWord ++ tailWord_1834983).sum := by decide
  have hdescent : baseEnd_1834983 < baseStart_1834983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1834993 : List Nat := [1, 2, 2, 2, 6, 1, 2, 7]
def baseStart_1834993 : Nat := 118140960795 + 1834993 * 2 ^ 59
def prefixEnd_1834993 : Nat := 4983230072969 + 3 ^ 40 * 1834993 * 2
def baseEnd_1834993 : Nat := 34897533579105345005501

theorem tailTrace_1834993 : CollatzResearch.WordTrace tailWord_1834993 prefixEnd_1834993 34897533579105345005501 := by
  unfold tailWord_1834993
  simp only [CollatzResearch.WordTrace]
  refine ⟨66927693041141227699109633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44618462027427485132739755 66927693041141227699109633)
  ·
    refine ⟨50195769780855920774332225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66927693041141227699109633 50195769780855920774332225)
    ·
      refine ⟨37646827335641940580749169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50195769780855920774332225 37646827335641940580749169)
      ·
        refine ⟨28235120501731455435561877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37646827335641940580749169 28235120501731455435561877)
        ·
          refine ⟨1323521273518661973541963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28235120501731455435561877 1323521273518661973541963)
          ·
            refine ⟨1985281910277992960312945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323521273518661973541963 1985281910277992960312945)
            ·
              refine ⟨1488961432708494720234709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985281910277992960312945 1488961432708494720234709)
              ·
                refine ⟨34897533579105345005501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1488961432708494720234709 34897533579105345005501)
                ·
                  rfl

theorem cell23_1834993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 7].length) (baseStart_1834993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1834993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1834993 prefixEnd_1834993 := by exact prefixLift 1834993
  have htrace : WordTrace (prefixWord ++ tailWord_1834993) baseStart_1834993 baseEnd_1834993 := by
    simpa [prefixWord, tailWord_1834993, baseEnd_1834993] using wordTrace_append hprefix tailTrace_1834993
  have hstable : (prefixWord ++ tailWord_1834993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1834993).length < 2 ^ (prefixWord ++ tailWord_1834993).sum := by decide
  have hdescent : baseEnd_1834993 < baseStart_1834993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1834993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835013 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 1, 3, 2]
def baseStart_1835013 : Nat := 118140960795 + 1835013 * 2 ^ 59
def prefixEnd_1835013 : Nat := 4983230072969 + 3 ^ 40 * 1835013 * 2
def baseEnd_1835013 : Nat := 942243676248934236898435

theorem tailTrace_1835013 : CollatzResearch.WordTrace tailWord_1835013 prefixEnd_1835013 942243676248934236898435 := by
  unfold tailWord_1835013
  simp only [CollatzResearch.WordTrace]
  refine ⟨66928422501068771114837693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44618948334045847409891795 66928422501068771114837693)
  ·
    refine ⟨25098158437900789168064135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66928422501068771114837693 25098158437900789168064135)
    ·
      refine ⟨37647237656851183752096203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25098158437900789168064135 37647237656851183752096203)
      ·
        refine ⟨56470856485276775628144305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37647237656851183752096203 56470856485276775628144305)
        ·
          refine ⟨42353142363957581721108229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56470856485276775628144305 42353142363957581721108229)
          ·
            refine ⟨7941214193242046572707793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42353142363957581721108229 7941214193242046572707793)
            ·
              refine ⟨5955910644931534929530845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941214193242046572707793 5955910644931534929530845)
              ·
                refine ⟨2233466491849325598574067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5955910644931534929530845 2233466491849325598574067)
                ·
                  refine ⟨3350199737773988397861101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233466491849325598574067 3350199737773988397861101)
                  ·
                    refine ⟨1256324901665245649197913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3350199737773988397861101 1256324901665245649197913)
                    ·
                      refine ⟨942243676248934236898435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256324901665245649197913 942243676248934236898435)
                      ·
                        rfl

theorem cell23_1835013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_1835013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835013 prefixEnd_1835013 := by exact prefixLift 1835013
  have htrace : WordTrace (prefixWord ++ tailWord_1835013) baseStart_1835013 baseEnd_1835013 := by
    simpa [prefixWord, tailWord_1835013, baseEnd_1835013] using wordTrace_append hprefix tailTrace_1835013
  have hstable : (prefixWord ++ tailWord_1835013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835013).length < 2 ^ (prefixWord ++ tailWord_1835013).sum := by decide
  have hdescent : baseEnd_1835013 < baseStart_1835013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835021 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1835021 : Nat := 118140960795 + 1835021 * 2 ^ 59
def prefixEnd_1835021 : Nat := 4983230072969 + 3 ^ 40 * 1835021 * 2
def baseEnd_1835021 : Nat := 942247784094170205598399

theorem tailTrace_1835021 : CollatzResearch.WordTrace tailWord_1835021 prefixEnd_1835021 942247784094170205598399 := by
  unfold tailWord_1835021
  simp only [CollatzResearch.WordTrace]
  refine ⟨66928714285039788481128917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44619142856693192320752611 66928714285039788481128917)
  ·
    refine ⟨1568641741055620042526459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 66928714285039788481128917 1568641741055620042526459)
    ·
      refine ⟨2352962611583430063789689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1568641741055620042526459 2352962611583430063789689)
      ·
        refine ⟨1764721958687572547842267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2352962611583430063789689 1764721958687572547842267)
        ·
          refine ⟨2647082938031358821763401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1764721958687572547842267 2647082938031358821763401)
          ·
            refine ⟨1985312203523519116322551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2647082938031358821763401 1985312203523519116322551)
            ·
              refine ⟨2977968305285278674483827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985312203523519116322551 2977968305285278674483827)
              ·
                refine ⟨4466952457927918011725741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2977968305285278674483827 4466952457927918011725741)
                ·
                  refine ⟨1675107171722969254397153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4466952457927918011725741 1675107171722969254397153)
                  ·
                    refine ⟨1256330378792226940797865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675107171722969254397153 1256330378792226940797865)
                    ·
                      refine ⟨942247784094170205598399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256330378792226940797865 942247784094170205598399)
                      ·
                        rfl

theorem cell23_1835021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1835021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835021 prefixEnd_1835021 := by exact prefixLift 1835021
  have htrace : WordTrace (prefixWord ++ tailWord_1835021) baseStart_1835021 baseEnd_1835021 := by
    simpa [prefixWord, tailWord_1835021, baseEnd_1835021] using wordTrace_append hprefix tailTrace_1835021
  have hstable : (prefixWord ++ tailWord_1835021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835021).length < 2 ^ (prefixWord ++ tailWord_1835021).sum := by decide
  have hdescent : baseEnd_1835021 < baseStart_1835021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835037 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 2, 1, 3]
def baseStart_1835037 : Nat := 118140960795 + 1835037 * 2 ^ 59
def prefixEnd_1835037 : Nat := 4983230072969 + 3 ^ 40 * 1835037 * 2
def baseEnd_1835037 : Nat := 942255999784642142998325

theorem tailTrace_1835037 : CollatzResearch.WordTrace tailWord_1835037 prefixEnd_1835037 942255999784642142998325 := by
  unfold tailWord_1835037
  simp only [CollatzResearch.WordTrace]
  refine ⟨66929297852981823213711365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44619531901987882142474243 66929297852981823213711365)
  ·
    refine ⟨12549243347434091852570881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66929297852981823213711365 12549243347434091852570881)
    ·
      refine ⟨9411932510575568889428161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12549243347434091852570881 9411932510575568889428161)
      ·
        refine ⟨7058949382931676667071121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9411932510575568889428161 7058949382931676667071121)
        ·
          refine ⟨5294212037198757500303341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7058949382931676667071121 5294212037198757500303341)
          ·
            refine ⟨1985329513949534062613753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5294212037198757500303341 1985329513949534062613753)
            ·
              refine ⟨1488997135462150546960315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985329513949534062613753 1488997135462150546960315)
              ·
                refine ⟨2233495703193225820440473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488997135462150546960315 2233495703193225820440473)
                ·
                  refine ⟨1675121777394919365330355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233495703193225820440473 1675121777394919365330355)
                  ·
                    refine ⟨2512682666092379047995533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675121777394919365330355 2512682666092379047995533)
                    ·
                      refine ⟨942255999784642142998325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512682666092379047995533 942255999784642142998325)
                      ·
                        rfl

theorem cell23_1835037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 2, 1, 3].length) (baseStart_1835037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835037 prefixEnd_1835037 := by exact prefixLift 1835037
  have htrace : WordTrace (prefixWord ++ tailWord_1835037) baseStart_1835037 baseEnd_1835037 := by
    simpa [prefixWord, tailWord_1835037, baseEnd_1835037] using wordTrace_append hprefix tailTrace_1835037
  have hstable : (prefixWord ++ tailWord_1835037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835037).length < 2 ^ (prefixWord ++ tailWord_1835037).sum := by decide
  have hdescent : baseEnd_1835037 < baseStart_1835037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835039 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 4]
def baseStart_1835039 : Nat := 118140960795 + 1835039 * 2 ^ 59
def prefixEnd_1835039 : Nat := 4983230072969 + 3 ^ 40 * 1835039 * 2
def baseEnd_1835039 : Nat := 942257026745951135173315

theorem tailTrace_1835039 : CollatzResearch.WordTrace tailWord_1835039 prefixEnd_1835039 942257026745951135173315 := by
  unfold tailWord_1835039
  simp only [CollatzResearch.WordTrace]
  refine ⟨66929370798974577555284171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44619580532649718370189447 66929370798974577555284171)
  ·
    refine ⟨100394056198461866332926257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66929370798974577555284171 100394056198461866332926257)
    ·
      refine ⟨75295542148846399749694693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100394056198461866332926257 75295542148846399749694693)
      ·
        refine ⟨14117914152908699953067755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75295542148846399749694693 14117914152908699953067755)
        ·
          refine ⟨21176871229363049929601633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14117914152908699953067755 21176871229363049929601633)
          ·
            refine ⟨15882653422022287447201225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21176871229363049929601633 15882653422022287447201225)
            ·
              refine ⟨11911990066516715585400919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15882653422022287447201225 11911990066516715585400919)
              ·
                refine ⟨17867985099775073378101379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11911990066516715585400919 17867985099775073378101379)
                ·
                  refine ⟨26801977649662610067152069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17867985099775073378101379 26801977649662610067152069)
                  ·
                    refine ⟨5025370809311739387591013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26801977649662610067152069 5025370809311739387591013)
                    ·
                      refine ⟨942257026745951135173315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5025370809311739387591013 942257026745951135173315)
                      ·
                        rfl

theorem cell23_1835039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_1835039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835039 prefixEnd_1835039 := by exact prefixLift 1835039
  have htrace : WordTrace (prefixWord ++ tailWord_1835039) baseStart_1835039 baseEnd_1835039 := by
    simpa [prefixWord, tailWord_1835039, baseEnd_1835039] using wordTrace_append hprefix tailTrace_1835039
  have hstable : (prefixWord ++ tailWord_1835039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835039).length < 2 ^ (prefixWord ++ tailWord_1835039).sum := by decide
  have hdescent : baseEnd_1835039 < baseStart_1835039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835066 : List Nat := [3, 1, 1, 1, 3, 1, 1, 7, 5]
def baseStart_1835066 : Nat := 118140960795 + 1835066 * 2 ^ 59
def prefixEnd_1835066 : Nat := 4983230072969 + 3 ^ 40 * 1835066 * 2
def baseEnd_1835066 : Nat := 104696765635958058837299

theorem tailTrace_1835066 : CollatzResearch.WordTrace tailWord_1835066 prefixEnd_1835066 104696765635958058837299 := by
  unfold tailWord_1835066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732588892469190291629263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44620237046584507444344701 16732588892469190291629263)
  ·
    refine ⟨25098883338703785437443895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16732588892469190291629263 25098883338703785437443895)
    ·
      refine ⟨37648325008055678156165843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25098883338703785437443895 37648325008055678156165843)
      ·
        refine ⟨56472487512083517234248765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37648325008055678156165843 56472487512083517234248765)
        ·
          refine ⟨21177182817031318962843287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56472487512083517234248765 21177182817031318962843287)
          ·
            refine ⟨31765774225546978444264931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21177182817031318962843287 31765774225546978444264931)
            ·
              refine ⟨47648661338320467666397397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31765774225546978444264931 47648661338320467666397397)
              ·
                refine ⟨1116765500116885960931189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47648661338320467666397397 1116765500116885960931189)
                ·
                  refine ⟨104696765635958058837299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1116765500116885960931189 104696765635958058837299)
                  ·
                    rfl

theorem cell23_1835066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 7, 5].length) (baseStart_1835066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835066 prefixEnd_1835066 := by exact prefixLift 1835066
  have htrace : WordTrace (prefixWord ++ tailWord_1835066) baseStart_1835066 baseEnd_1835066 := by
    simpa [prefixWord, tailWord_1835066, baseEnd_1835066] using wordTrace_append hprefix tailTrace_1835066
  have hstable : (prefixWord ++ tailWord_1835066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835066).length < 2 ^ (prefixWord ++ tailWord_1835066).sum := by decide
  have hdescent : baseEnd_1835066 < baseStart_1835066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835094 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_1835094 : Nat := 118140960795 + 1835094 * 2 ^ 59
def prefixEnd_1835094 : Nat := 4983230072969 + 3 ^ 40 * 1835094 * 2
def baseEnd_1835094 : Nat := 942285268181948419985563

theorem tailTrace_1835094 : CollatzResearch.WordTrace tailWord_1835094 prefixEnd_1835094 942285268181948419985563 := by
  unfold tailWord_1835094
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183211050860957621783521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44620917875850214632357557 4183211050860957621783521)
  ·
    refine ⟨3137408288145718216337641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4183211050860957621783521 3137408288145718216337641)
    ·
      refine ⟨2353056216109288662253231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3137408288145718216337641 2353056216109288662253231)
      ·
        refine ⟨3529584324163932993379847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353056216109288662253231 3529584324163932993379847)
        ·
          refine ⟨5294376486245899490069771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529584324163932993379847 5294376486245899490069771)
          ·
            refine ⟨7941564729368849235104657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294376486245899490069771 7941564729368849235104657)
            ·
              refine ⟨5956173547026636926328493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941564729368849235104657 5956173547026636926328493)
              ·
                refine ⟨2233565080134988847373185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5956173547026636926328493 2233565080134988847373185)
                ·
                  refine ⟨1675173810101241635529889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233565080134988847373185 1675173810101241635529889)
                  ·
                    refine ⟨1256380357575931226647417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675173810101241635529889 1256380357575931226647417)
                    ·
                      refine ⟨942285268181948419985563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256380357575931226647417 942285268181948419985563)
                      ·
                        rfl

theorem cell23_1835094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_1835094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835094 prefixEnd_1835094 := by exact prefixLift 1835094
  have htrace : WordTrace (prefixWord ++ tailWord_1835094) baseStart_1835094 baseEnd_1835094 := by
    simpa [prefixWord, tailWord_1835094, baseEnd_1835094] using wordTrace_append hprefix tailTrace_1835094
  have hstable : (prefixWord ++ tailWord_1835094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835094).length < 2 ^ (prefixWord ++ tailWord_1835094).sum := by decide
  have hdescent : baseEnd_1835094 < baseStart_1835094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835116 : List Nat := [2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 4]
def baseStart_1835116 : Nat := 118140960795 + 1835116 * 2 ^ 59
def prefixEnd_1835116 : Nat := 4983230072969 + 3 ^ 40 * 1835116 * 2
def baseEnd_1835116 : Nat := 942296564756347333910461

theorem tailTrace_1835116 : CollatzResearch.WordTrace tailWord_1835116 prefixEnd_1835116 942296564756347333910461 := by
  unfold tailWord_1835116
  simp only [CollatzResearch.WordTrace]
  refine ⟨33466089609847809852918601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44621452813130413137224801 33466089609847809852918601)
  ·
    refine ⟨25099567207385857389688951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33466089609847809852918601 25099567207385857389688951)
    ·
      refine ⟨37649350811078786084533427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25099567207385857389688951 37649350811078786084533427)
      ·
        refine ⟨56474026216618179126800141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37649350811078786084533427 56474026216618179126800141)
        ·
          refine ⟨21177759831231817172550053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56474026216618179126800141 21177759831231817172550053)
          ·
            refine ⟨3970829968355965719853135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21177759831231817172550053 3970829968355965719853135)
            ·
              refine ⟨5956244952533948579779703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3970829968355965719853135 5956244952533948579779703)
              ·
                refine ⟨8934367428800922869669555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956244952533948579779703 8934367428800922869669555)
                ·
                  refine ⟨13401551143201384304504333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934367428800922869669555 13401551143201384304504333)
                  ·
                    refine ⟨5025581678700519114189125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13401551143201384304504333 5025581678700519114189125)
                    ·
                      refine ⟨942296564756347333910461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5025581678700519114189125 942296564756347333910461)
                      ·
                        rfl

theorem cell23_1835116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 4].length) (baseStart_1835116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835116 prefixEnd_1835116 := by exact prefixLift 1835116
  have htrace : WordTrace (prefixWord ++ tailWord_1835116) baseStart_1835116 baseEnd_1835116 := by
    simpa [prefixWord, tailWord_1835116, baseEnd_1835116] using wordTrace_append hprefix tailTrace_1835116
  have hstable : (prefixWord ++ tailWord_1835116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835116).length < 2 ^ (prefixWord ++ tailWord_1835116).sum := by decide
  have hdescent : baseEnd_1835116 < baseStart_1835116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835133 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 2, 4, 2]
def baseStart_1835133 : Nat := 118140960795 + 1835133 * 2 ^ 59
def prefixEnd_1835133 : Nat := 4983230072969 + 3 ^ 40 * 1835133 * 2
def baseEnd_1835133 : Nat := 942305293927473767397883

theorem tailTrace_1835133 : CollatzResearch.WordTrace tailWord_1835133 prefixEnd_1835133 942305293927473767397883 := by
  unfold tailWord_1835133
  simp only [CollatzResearch.WordTrace]
  refine ⟨66932799260634031609206053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44621866173756021072804035 66932799260634031609206053)
  ·
    refine ⟨12549899861368880926726135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66932799260634031609206053 12549899861368880926726135)
    ·
      refine ⟨18824849792053321390089203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12549899861368880926726135 18824849792053321390089203)
      ·
        refine ⟨28237274688079982085133805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18824849792053321390089203 28237274688079982085133805)
        ·
          refine ⟨10588978008029993281925177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28237274688079982085133805 10588978008029993281925177)
          ·
            refine ⟨7941733506022494961443883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10588978008029993281925177 7941733506022494961443883)
            ·
              refine ⟨11912600259033742442165825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941733506022494961443883 11912600259033742442165825)
              ·
                refine ⟨8934450194275306831624369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11912600259033742442165825 8934450194275306831624369)
                ·
                  refine ⟨6700837645706480123718277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8934450194275306831624369 6700837645706480123718277)
                  ·
                    refine ⟨1256407058569965023197177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6700837645706480123718277 1256407058569965023197177)
                    ·
                      refine ⟨942305293927473767397883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256407058569965023197177 942305293927473767397883)
                      ·
                        rfl

theorem cell23_1835133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 4, 2].length) (baseStart_1835133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835133 prefixEnd_1835133 := by exact prefixLift 1835133
  have htrace : WordTrace (prefixWord ++ tailWord_1835133) baseStart_1835133 baseEnd_1835133 := by
    simpa [prefixWord, tailWord_1835133, baseEnd_1835133] using wordTrace_append hprefix tailTrace_1835133
  have hstable : (prefixWord ++ tailWord_1835133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835133).length < 2 ^ (prefixWord ++ tailWord_1835133).sum := by decide
  have hdescent : baseEnd_1835133 < baseStart_1835133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835136 : List Nat := [2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3]
def baseStart_1835136 : Nat := 118140960795 + 1835136 * 2 ^ 59
def prefixEnd_1835136 : Nat := 4983230072969 + 3 ^ 40 * 1835136 * 2
def baseEnd_1835136 : Nat := 942306834369437255660369

theorem tailTrace_1835136 : CollatzResearch.WordTrace tailWord_1835136 prefixEnd_1835136 942306834369437255660369 := by
  unfold tailWord_1835136
  simp only [CollatzResearch.WordTrace]
  refine ⟨33466454339811581560782631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44621939119748775414376841 33466454339811581560782631)
  ·
    refine ⟨50199681509717372341173947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33466454339811581560782631 50199681509717372341173947)
    ·
      refine ⟨75299522264576058511760921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50199681509717372341173947 75299522264576058511760921)
      ·
        refine ⟨56474641698432043883820691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75299522264576058511760921 56474641698432043883820691)
        ·
          refine ⟨84711962547648065825731037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56474641698432043883820691 84711962547648065825731037)
          ·
            refine ⟨31766985955368024684649139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84711962547648065825731037 31766985955368024684649139)
            ·
              refine ⟨47650478933052037026973709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31766985955368024684649139 47650478933052037026973709)
              ·
                refine ⟨17868929599894513885115141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47650478933052037026973709 17868929599894513885115141)
                ·
                  refine ⟨3350424299980221353459089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17868929599894513885115141 3350424299980221353459089)
                  ·
                    refine ⟨2512818224985166015094317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3350424299980221353459089 2512818224985166015094317)
                    ·
                      refine ⟨942306834369437255660369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512818224985166015094317 942306834369437255660369)
                      ·
                        rfl

theorem cell23_1835136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_1835136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835136 prefixEnd_1835136 := by exact prefixLift 1835136
  have htrace : WordTrace (prefixWord ++ tailWord_1835136) baseStart_1835136 baseEnd_1835136 := by
    simpa [prefixWord, tailWord_1835136, baseEnd_1835136] using wordTrace_append hprefix tailTrace_1835136
  have hstable : (prefixWord ++ tailWord_1835136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835136).length < 2 ^ (prefixWord ++ tailWord_1835136).sum := by decide
  have hdescent : baseEnd_1835136 < baseStart_1835136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835179 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7]
def baseStart_1835179 : Nat := 118140960795 + 1835179 * 2 ^ 59
def prefixEnd_1835179 : Nat := 4983230072969 + 3 ^ 40 * 1835179 * 2
def baseEnd_1835179 : Nat := 942328914037580587422671

theorem tailTrace_1835179 : CollatzResearch.WordTrace tailWord_1835179 prefixEnd_1835179 942328914037580587422671 := by
  unfold tailWord_1835179
  simp only [CollatzResearch.WordTrace]
  refine ⟨66934477018467381465380591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44622984678978254310253727 66934477018467381465380591)
  ·
    refine ⟨100401715527701072198070887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66934477018467381465380591 100401715527701072198070887)
    ·
      refine ⟨150602573291551608297106331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100401715527701072198070887 150602573291551608297106331)
      ·
        refine ⟨225903859937327412445659497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150602573291551608297106331 225903859937327412445659497)
        ·
          refine ⟨169427894952995559334244623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225903859937327412445659497 169427894952995559334244623)
          ·
            refine ⟨254141842429493339001366935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169427894952995559334244623 254141842429493339001366935)
            ·
              refine ⟨381212763644240008502050403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254141842429493339001366935 381212763644240008502050403)
              ·
                refine ⟨571819145466360012753075605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381212763644240008502050403 571819145466360012753075605)
                ·
                  refine ⟨26804022443735625597800419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 571819145466360012753075605 26804022443735625597800419)
                  ·
                    refine ⟨40206033665603438396700629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26804022443735625597800419 40206033665603438396700629)
                    ·
                      refine ⟨942328914037580587422671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40206033665603438396700629 942328914037580587422671)
                      ·
                        rfl

theorem cell23_1835179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 7].length) (baseStart_1835179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835179 prefixEnd_1835179 := by exact prefixLift 1835179
  have htrace : WordTrace (prefixWord ++ tailWord_1835179) baseStart_1835179 baseEnd_1835179 := by
    simpa [prefixWord, tailWord_1835179, baseEnd_1835179] using wordTrace_append hprefix tailTrace_1835179
  have hstable : (prefixWord ++ tailWord_1835179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835179).length < 2 ^ (prefixWord ++ tailWord_1835179).sum := by decide
  have hdescent : baseEnd_1835179 < baseStart_1835179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835200 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 3, 1, 3]
def baseStart_1835200 : Nat := 118140960795 + 1835200 * 2 ^ 59
def prefixEnd_1835200 : Nat := 4983230072969 + 3 ^ 40 * 1835200 * 2
def baseEnd_1835200 : Nat := 942339697131325005260075

theorem tailTrace_1835200 : CollatzResearch.WordTrace tailWord_1835200 prefixEnd_1835200 942339697131325005260075 := by
  unfold tailWord_1835200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33467621475695651025947527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44623495300927534701263369 33467621475695651025947527)
  ·
    refine ⟨50201432213543476538921291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33467621475695651025947527 50201432213543476538921291)
    ·
      refine ⟨75302148320315214808381937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50201432213543476538921291 75302148320315214808381937)
      ·
        refine ⟨56476611240236411106286453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75302148320315214808381937 56476611240236411106286453)
        ·
          refine ⟨5294682303772163541214355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56476611240236411106286453 5294682303772163541214355)
          ·
            refine ⟨7942023455658245311821533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294682303772163541214355 7942023455658245311821533)
            ·
              refine ⟨2978258795871841991933075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7942023455658245311821533 2978258795871841991933075)
              ·
                refine ⟨4467388193807762987899613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978258795871841991933075 4467388193807762987899613)
                ·
                  refine ⟨1675270572677911120462355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4467388193807762987899613 1675270572677911120462355)
                  ·
                    refine ⟨2512905859016866680693533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675270572677911120462355 2512905859016866680693533)
                    ·
                      refine ⟨942339697131325005260075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2512905859016866680693533 942339697131325005260075)
                      ·
                        rfl

theorem cell23_1835200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_1835200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835200 prefixEnd_1835200 := by exact prefixLift 1835200
  have htrace : WordTrace (prefixWord ++ tailWord_1835200) baseStart_1835200 baseEnd_1835200 := by
    simpa [prefixWord, tailWord_1835200, baseEnd_1835200] using wordTrace_append hprefix tailTrace_1835200
  have hstable : (prefixWord ++ tailWord_1835200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835200).length < 2 ^ (prefixWord ++ tailWord_1835200).sum := by decide
  have hdescent : baseEnd_1835200 < baseStart_1835200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835226 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1835226 : Nat := 118140960795 + 1835226 * 2 ^ 59
def prefixEnd_1835226 : Nat := 4983230072969 + 3 ^ 40 * 1835226 * 2
def baseEnd_1835226 : Nat := 942353047628341903534955

theorem tailTrace_1835226 : CollatzResearch.WordTrace tailWord_1835226 prefixEnd_1835226 942353047628341903534955 := by
  unfold tailWord_1835226
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734047812324277123085383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44624127499531405661561021 16734047812324277123085383)
  ·
    refine ⟨25101071718486415684628075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16734047812324277123085383 25101071718486415684628075)
    ·
      refine ⟨37651607577729623526942113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25101071718486415684628075 37651607577729623526942113)
      ·
        refine ⟨28238705683297217645206585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37651607577729623526942113 28238705683297217645206585)
        ·
          refine ⟨21179029262472913233904939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28238705683297217645206585 21179029262472913233904939)
          ·
            refine ⟨31768543893709369850857409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21179029262472913233904939 31768543893709369850857409)
            ·
              refine ⟨23826407920282027388143057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31768543893709369850857409 23826407920282027388143057)
              ·
                refine ⟨17869805940211520541107293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23826407920282027388143057 17869805940211520541107293)
                ·
                  refine ⟨6701177227579320202915235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17869805940211520541107293 6701177227579320202915235)
                  ·
                    refine ⟨10051765841368980304372853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6701177227579320202915235 10051765841368980304372853)
                    ·
                      refine ⟨942353047628341903534955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10051765841368980304372853 942353047628341903534955)
                      ·
                        rfl

theorem cell23_1835226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1835226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835226 prefixEnd_1835226 := by exact prefixLift 1835226
  have htrace : WordTrace (prefixWord ++ tailWord_1835226) baseStart_1835226 baseEnd_1835226 := by
    simpa [prefixWord, tailWord_1835226, baseEnd_1835226] using wordTrace_append hprefix tailTrace_1835226
  have hstable : (prefixWord ++ tailWord_1835226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835226).length < 2 ^ (prefixWord ++ tailWord_1835226).sum := by decide
  have hdescent : baseEnd_1835226 < baseStart_1835226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835250 : List Nat := [3, 2, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_1835250 : Nat := 118140960795 + 1835250 * 2 ^ 59
def prefixEnd_1835250 : Nat := 4983230072969 + 3 ^ 40 * 1835250 * 2
def baseEnd_1835250 : Nat := 314121790388016603211615

theorem tailTrace_1835250 : CollatzResearch.WordTrace tailWord_1835250 prefixEnd_1835250 314121790388016603211615 := by
  unfold tailWord_1835250
  simp only [CollatzResearch.WordTrace]
  refine ⟨16734266650302540147803801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44624711067473440394143469 16734266650302540147803801)
  ·
    refine ⟨12550699987726905110852851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16734266650302540147803801 12550699987726905110852851)
    ·
      refine ⟨18826049981590357666279277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12550699987726905110852851 18826049981590357666279277)
      ·
        refine ⟨7059768743096384124854729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18826049981590357666279277 7059768743096384124854729)
        ·
          refine ⟨5294826557322288093641047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7059768743096384124854729 5294826557322288093641047)
          ·
            refine ⟨7942239835983432140461571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294826557322288093641047 7942239835983432140461571)
            ·
              refine ⟨11913359753975148210692357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942239835983432140461571 11913359753975148210692357)
              ·
                refine ⟨2233754953870340289504817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11913359753975148210692357 2233754953870340289504817)
                ·
                  refine ⟨1675316215402755217128613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233754953870340289504817 1675316215402755217128613)
                  ·
                    refine ⟨314121790388016603211615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1675316215402755217128613 314121790388016603211615)
                    ·
                      rfl

theorem cell23_1835250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_1835250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835250 prefixEnd_1835250 := by exact prefixLift 1835250
  have htrace : WordTrace (prefixWord ++ tailWord_1835250) baseStart_1835250 baseEnd_1835250 := by
    simpa [prefixWord, tailWord_1835250, baseEnd_1835250] using wordTrace_append hprefix tailTrace_1835250
  have hstable : (prefixWord ++ tailWord_1835250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835250).length < 2 ^ (prefixWord ++ tailWord_1835250).sum := by decide
  have hdescent : baseEnd_1835250 < baseStart_1835250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835273 : List Nat := [1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 3]
def baseStart_1835273 : Nat := 118140960795 + 1835273 * 2 ^ 59
def prefixEnd_1835273 : Nat := 4983230072969 + 3 ^ 40 * 1835273 * 2
def baseEnd_1835273 : Nat := 942377181219103219647239

theorem tailTrace_1835273 : CollatzResearch.WordTrace tailWord_1835273 prefixEnd_1835273 942377181219103219647239 := by
  unfold tailWord_1835273
  simp only [CollatzResearch.WordTrace]
  refine ⟨66937905480126835519302473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44625270320084557012868315 66937905480126835519302473)
  ·
    refine ⟨50203429110095126639476855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66937905480126835519302473 50203429110095126639476855)
    ·
      refine ⟨75305143665142689959215283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50203429110095126639476855 75305143665142689959215283)
      ·
        refine ⟨112957715497714034938822925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75305143665142689959215283 112957715497714034938822925)
        ·
          refine ⟨42359143311642763102058597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112957715497714034938822925 42359143311642763102058597)
          ·
            refine ⟨7942339370933018081635987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42359143311642763102058597 7942339370933018081635987)
            ·
              refine ⟨11913509056399527122453981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7942339370933018081635987 11913509056399527122453981)
              ·
                refine ⟨4467565896149822670920243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11913509056399527122453981 4467565896149822670920243)
                ·
                  refine ⟨6701348844224734006380365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4467565896149822670920243 6701348844224734006380365)
                  ·
                    refine ⟨2513005816584275252392637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6701348844224734006380365 2513005816584275252392637)
                    ·
                      refine ⟨942377181219103219647239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513005816584275252392637 942377181219103219647239)
                      ·
                        rfl

theorem cell23_1835273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 3, 3].length) (baseStart_1835273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835273 prefixEnd_1835273 := by exact prefixLift 1835273
  have htrace : WordTrace (prefixWord ++ tailWord_1835273) baseStart_1835273 baseEnd_1835273 := by
    simpa [prefixWord, tailWord_1835273, baseEnd_1835273] using wordTrace_append hprefix tailTrace_1835273
  have hstable : (prefixWord ++ tailWord_1835273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835273).length < 2 ^ (prefixWord ++ tailWord_1835273).sum := by decide
  have hdescent : baseEnd_1835273 < baseStart_1835273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835276 : List Nat := [2, 2, 1, 2, 2, 2, 1, 2, 2, 7]
def baseStart_1835276 : Nat := 118140960795 + 1835276 * 2 ^ 59
def prefixEnd_1835276 : Nat := 4983230072969 + 3 ^ 40 * 1835276 * 2
def baseEnd_1835276 : Nat := 314126240553688902636575

theorem tailTrace_1835276 : CollatzResearch.WordTrace tailWord_1835276 prefixEnd_1835276 314126240553688902636575 := by
  unfold tailWord_1835276
  simp only [CollatzResearch.WordTrace]
  refine ⟨33469007449557983515830841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44625343266077311354441121 33469007449557983515830841)
  ·
    refine ⟨25101755587168487636873131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33469007449557983515830841 25101755587168487636873131)
    ·
      refine ⟨37652633380752731455309697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25101755587168487636873131 37652633380752731455309697)
      ·
        refine ⟨28239475035564548591482273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37652633380752731455309697 28239475035564548591482273)
        ·
          refine ⟨21179606276673411443611705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28239475035564548591482273 21179606276673411443611705)
          ·
            refine ⟨15884704707505058582708779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21179606276673411443611705 15884704707505058582708779)
            ·
              refine ⟨23827057061257587874063169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15884704707505058582708779 23827057061257587874063169)
              ·
                refine ⟨17870292795943190905547377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23827057061257587874063169 17870292795943190905547377)
                ·
                  refine ⟨13402719596957393179160533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17870292795943190905547377 13402719596957393179160533)
                  ·
                    refine ⟨314126240553688902636575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13402719596957393179160533 314126240553688902636575)
                    ·
                      rfl

theorem cell23_1835276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 7].length) (baseStart_1835276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835276 prefixEnd_1835276 := by exact prefixLift 1835276
  have htrace : WordTrace (prefixWord ++ tailWord_1835276) baseStart_1835276 baseEnd_1835276 := by
    simpa [prefixWord, tailWord_1835276, baseEnd_1835276] using wordTrace_append hprefix tailTrace_1835276
  have hstable : (prefixWord ++ tailWord_1835276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835276).length < 2 ^ (prefixWord ++ tailWord_1835276).sum := by decide
  have hdescent : baseEnd_1835276 < baseStart_1835276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835294 : List Nat := [4, 3, 2, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_1835294 : Nat := 118140960795 + 1835294 * 2 ^ 59
def prefixEnd_1835294 : Nat := 4983230072969 + 3 ^ 40 * 1835294 * 2
def baseEnd_1835294 : Nat := 942387964312847637484643

theorem tailTrace_1835294 : CollatzResearch.WordTrace tailWord_1835294 prefixEnd_1835294 942387964312847637484643 := by
  unfold tailWord_1835294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8367333926631344513227117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44625780942033837403877957 8367333926631344513227117)
  ·
    refine ⟨3137750222486754192460169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8367333926631344513227117 3137750222486754192460169)
    ·
      refine ⟨2353312666865065644345127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3137750222486754192460169 2353312666865065644345127)
      ·
        refine ⟨3529969000297598466517691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353312666865065644345127 3529969000297598466517691)
        ·
          refine ⟨5294953500446397699776537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529969000297598466517691 5294953500446397699776537)
          ·
            refine ⟨3971215125334798274832403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5294953500446397699776537 3971215125334798274832403)
            ·
              refine ⟨5956822688002197412248605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971215125334798274832403 5956822688002197412248605)
              ·
                refine ⟨2233808508000824029593227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5956822688002197412248605 2233808508000824029593227)
                ·
                  refine ⟨3350712762001236044389841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233808508000824029593227 3350712762001236044389841)
                  ·
                    refine ⟨2513034571500927033292381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3350712762001236044389841 2513034571500927033292381)
                    ·
                      refine ⟨942387964312847637484643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513034571500927033292381 942387964312847637484643)
                      ·
                        rfl

theorem cell23_1835294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_1835294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835294 prefixEnd_1835294 := by exact prefixLift 1835294
  have htrace : WordTrace (prefixWord ++ tailWord_1835294) baseStart_1835294 baseEnd_1835294 := by
    simpa [prefixWord, tailWord_1835294, baseEnd_1835294] using wordTrace_append hprefix tailTrace_1835294
  have hstable : (prefixWord ++ tailWord_1835294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835294).length < 2 ^ (prefixWord ++ tailWord_1835294).sum := by decide
  have hdescent : baseEnd_1835294 < baseStart_1835294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835370 : List Nat := [3, 1, 3, 3, 1, 1, 3, 1, 7]
def baseStart_1835370 : Nat := 118140960795 + 1835370 * 2 ^ 59
def prefixEnd_1835370 : Nat := 4983230072969 + 3 ^ 40 * 1835370 * 2
def baseEnd_1835370 : Nat := 104714109871398815570477

theorem tailTrace_1835370 : CollatzResearch.WordTrace tailWord_1835370 prefixEnd_1835370 104714109871398815570477 := by
  unfold tailWord_1835370
  simp only [CollatzResearch.WordTrace]
  refine ⟨16735360840193855271395891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44627628907183614057055709 16735360840193855271395891)
  ·
    refine ⟨25103041260290782907093837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16735360840193855271395891 25103041260290782907093837)
    ·
      refine ⟨9413640472609043590160189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25103041260290782907093837 9413640472609043590160189)
      ·
        refine ⟨3530115177228391346310071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9413640472609043590160189 3530115177228391346310071)
        ·
          refine ⟨5295172765842587019465107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530115177228391346310071 5295172765842587019465107)
          ·
            refine ⟨7942759148763880529197661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295172765842587019465107 7942759148763880529197661)
            ·
              refine ⟨2978534680786455198449123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7942759148763880529197661 2978534680786455198449123)
              ·
                refine ⟨4467802021179682797673685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978534680786455198449123 4467802021179682797673685)
                ·
                  refine ⟨104714109871398815570477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4467802021179682797673685 104714109871398815570477)
                  ·
                    rfl

theorem cell23_1835370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_1835370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835370 prefixEnd_1835370 := by exact prefixLift 1835370
  have htrace : WordTrace (prefixWord ++ tailWord_1835370) baseStart_1835370 baseEnd_1835370 := by
    simpa [prefixWord, tailWord_1835370, baseEnd_1835370] using wordTrace_append hprefix tailTrace_1835370
  have hstable : (prefixWord ++ tailWord_1835370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835370).length < 2 ^ (prefixWord ++ tailWord_1835370).sum := by decide
  have hdescent : baseEnd_1835370 < baseStart_1835370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835381 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_1835381 : Nat := 118140960795 + 1835381 * 2 ^ 59
def prefixEnd_1835381 : Nat := 4983230072969 + 3 ^ 40 * 1835381 * 2
def baseEnd_1835381 : Nat := 942432637129788797096743

theorem tailTrace_1835381 : CollatzResearch.WordTrace tailWord_1835381 prefixEnd_1835381 942432637129788797096743 := by
  unfold tailWord_1835381
  simp only [CollatzResearch.WordTrace]
  refine ⟨66941844563735569964233997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44627896375823713309489331 66941844563735569964233997)
  ·
    refine ⟨25103191711400838736587749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66941844563735569964233997 25103191711400838736587749)
    ·
      refine ⟨4706848445887657263110203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25103191711400838736587749 4706848445887657263110203)
      ·
        refine ⟨7060272668831485894665305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4706848445887657263110203 7060272668831485894665305)
        ·
          refine ⟨5295204501623614420998979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7060272668831485894665305 5295204501623614420998979)
          ·
            refine ⟨7942806752435421631498469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295204501623614420998979 7942806752435421631498469)
            ·
              refine ⟨1489276266081641555905963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7942806752435421631498469 1489276266081641555905963)
              ·
                refine ⟨2233914399122462333858945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489276266081641555905963 2233914399122462333858945)
                ·
                  refine ⟨1675435799341846750394209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2233914399122462333858945 1675435799341846750394209)
                  ·
                    refine ⟨1256576849506385062795657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675435799341846750394209 1256576849506385062795657)
                    ·
                      refine ⟨942432637129788797096743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256576849506385062795657 942432637129788797096743)
                      ·
                        rfl

theorem cell23_1835381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_1835381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835381 prefixEnd_1835381 := by exact prefixLift 1835381
  have htrace : WordTrace (prefixWord ++ tailWord_1835381) baseStart_1835381 baseEnd_1835381 := by
    simpa [prefixWord, tailWord_1835381, baseEnd_1835381] using wordTrace_append hprefix tailTrace_1835381
  have hstable : (prefixWord ++ tailWord_1835381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835381).length < 2 ^ (prefixWord ++ tailWord_1835381).sum := by decide
  have hdescent : baseEnd_1835381 < baseStart_1835381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835400 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 2, 5]
def baseStart_1835400 : Nat := 118140960795 + 1835400 * 2 ^ 59
def prefixEnd_1835400 : Nat := 4983230072969 + 3 ^ 40 * 1835400 * 2
def baseEnd_1835400 : Nat := 314147464420741407586385

theorem tailTrace_1835400 : CollatzResearch.WordTrace tailWord_1835400 prefixEnd_1835400 314147464420741407586385 := by
  unfold tailWord_1835400
  simp only [CollatzResearch.WordTrace]
  refine ⟨33471268775333368104587827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44628358367111157472783769 33471268775333368104587827)
  ·
    refine ⟨50206903163000052156881741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33471268775333368104587827 50206903163000052156881741)
    ·
      refine ⟨18827588686125019558830653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50206903163000052156881741 18827588686125019558830653)
      ·
        refine ⟨7060345757296882334561495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18827588686125019558830653 7060345757296882334561495)
        ·
          refine ⟨10590518635945323501842243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060345757296882334561495 10590518635945323501842243)
          ·
            refine ⟨15885777953917985252763365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590518635945323501842243 15885777953917985252763365)
            ·
              refine ⟨2978583366359622234893131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15885777953917985252763365 2978583366359622234893131)
              ·
                refine ⟨4467875049539433352339697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978583366359622234893131 4467875049539433352339697)
                ·
                  refine ⟨3350906287154575014254773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4467875049539433352339697 3350906287154575014254773)
                  ·
                    refine ⟨314147464420741407586385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3350906287154575014254773 314147464420741407586385)
                    ·
                      rfl

theorem cell23_1835400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_1835400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835400 prefixEnd_1835400 := by exact prefixLift 1835400
  have htrace : WordTrace (prefixWord ++ tailWord_1835400) baseStart_1835400 baseEnd_1835400 := by
    simpa [prefixWord, tailWord_1835400, baseEnd_1835400] using wordTrace_append hprefix tailTrace_1835400
  have hstable : (prefixWord ++ tailWord_1835400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835400).length < 2 ^ (prefixWord ++ tailWord_1835400).sum := by decide
  have hdescent : baseEnd_1835400 < baseStart_1835400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835421 : List Nat := [1, 4, 2, 1, 5, 1, 2, 2, 5]
def baseStart_1835421 : Nat := 118140960795 + 1835421 * 2 ^ 59
def prefixEnd_1835421 : Nat := 4983230072969 + 3 ^ 40 * 1835421 * 2
def baseEnd_1835421 : Nat := 104717019595107626732951

theorem tailTrace_1835421 : CollatzResearch.WordTrace tailWord_1835421 prefixEnd_1835421 104717019595107626732951 := by
  unfold tailWord_1835421
  simp only [CollatzResearch.WordTrace]
  refine ⟨66943303483590656795690117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44628868989060437863793411 66943303483590656795690117)
  ·
    refine ⟨12551869403173248149191897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66943303483590656795690117 12551869403173248149191897)
    ·
      refine ⟨9413902052379936111893923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12551869403173248149191897 9413902052379936111893923)
      ·
        refine ⟨14120853078569904167840885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9413902052379936111893923 14120853078569904167840885)
        ·
          refine ⟨1323829976115928515735083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14120853078569904167840885 1323829976115928515735083)
          ·
            refine ⟨1985744964173892773602625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323829976115928515735083 1985744964173892773602625)
            ·
              refine ⟨1489308723130419580201969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985744964173892773602625 1489308723130419580201969)
              ·
                refine ⟨1116981542347814685151477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489308723130419580201969 1116981542347814685151477)
                ·
                  refine ⟨104717019595107626732951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1116981542347814685151477 104717019595107626732951)
                  ·
                    rfl

theorem cell23_1835421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_1835421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835421 prefixEnd_1835421 := by exact prefixLift 1835421
  have htrace : WordTrace (prefixWord ++ tailWord_1835421) baseStart_1835421 baseEnd_1835421 := by
    simpa [prefixWord, tailWord_1835421, baseEnd_1835421] using wordTrace_append hprefix tailTrace_1835421
  have hstable : (prefixWord ++ tailWord_1835421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835421).length < 2 ^ (prefixWord ++ tailWord_1835421).sum := by decide
  have hdescent : baseEnd_1835421 < baseStart_1835421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835423 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 5]
def baseStart_1835423 : Nat := 118140960795 + 1835423 * 2 ^ 59
def prefixEnd_1835423 : Nat := 4983230072969 + 3 ^ 40 * 1835423 * 2
def baseEnd_1835423 : Nat := 942454203317277632771549

theorem tailTrace_1835423 : CollatzResearch.WordTrace tailWord_1835423 prefixEnd_1835423 942454203317277632771549 := by
  unfold tailWord_1835423
  simp only [CollatzResearch.WordTrace]
  refine ⟨66943376429583411137262923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44628917619722274091508615 66943376429583411137262923)
  ·
    refine ⟨100415064644375116705894385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66943376429583411137262923 100415064644375116705894385)
    ·
      refine ⟨75311298483281337529420789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100415064644375116705894385 75311298483281337529420789)
      ·
        refine ⟨7060434232807625393383199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75311298483281337529420789 7060434232807625393383199)
        ·
          refine ⟨10590651349211438090074799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060434232807625393383199 10590651349211438090074799)
          ·
            refine ⟨15885977023817157135112199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10590651349211438090074799 15885977023817157135112199)
            ·
              refine ⟨23828965535725735702668299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15885977023817157135112199 23828965535725735702668299)
              ·
                refine ⟨35743448303588603554002449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23828965535725735702668299 35743448303588603554002449)
                ·
                  refine ⟨26807586227691452665501837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35743448303588603554002449 26807586227691452665501837)
                  ·
                    refine ⟨10052844835384294749563189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26807586227691452665501837 10052844835384294749563189)
                    ·
                      refine ⟨942454203317277632771549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10052844835384294749563189 942454203317277632771549)
                      ·
                        rfl

theorem cell23_1835423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_1835423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835423 prefixEnd_1835423 := by exact prefixLift 1835423
  have htrace : WordTrace (prefixWord ++ tailWord_1835423) baseStart_1835423 baseEnd_1835423 := by
    simpa [prefixWord, tailWord_1835423, baseEnd_1835423] using wordTrace_append hprefix tailTrace_1835423
  have hstable : (prefixWord ++ tailWord_1835423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835423).length < 2 ^ (prefixWord ++ tailWord_1835423).sum := by decide
  have hdescent : baseEnd_1835423 < baseStart_1835423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835464 : List Nat := [2, 1, 3, 1, 3, 3, 2, 3, 1, 4]
def baseStart_1835464 : Nat := 118140960795 + 1835464 * 2 ^ 59
def prefixEnd_1835464 : Nat := 4983230072969 + 3 ^ 40 * 1835464 * 2
def baseEnd_1835464 : Nat := 314158418674703990786287

theorem tailTrace_1835464 : CollatzResearch.WordTrace tailWord_1835464 prefixEnd_1835464 314158418674703990786287 := by
  unfold tailWord_1835464
  simp only [CollatzResearch.WordTrace]
  refine ⟨33472435911217437569752723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44629914548289916759670297 33472435911217437569752723)
  ·
    refine ⟨50208653866826156354629085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33472435911217437569752723 50208653866826156354629085)
    ·
      refine ⟨18828245200059808632985907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50208653866826156354629085 18828245200059808632985907)
      ·
        refine ⟨28242367800089712949478861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18828245200059808632985907 28242367800089712949478861)
        ·
          refine ⟨10590887925033642356054573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28242367800089712949478861 10590887925033642356054573)
          ·
            refine ⟨3971582971887615883520465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10590887925033642356054573 3971582971887615883520465)
            ·
              refine ⟨2978687228915711912640349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971582971887615883520465 2978687228915711912640349)
              ·
                refine ⟨1117007710843391967240131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2978687228915711912640349 1117007710843391967240131)
                ·
                  refine ⟨1675511566265087950860197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117007710843391967240131 1675511566265087950860197)
                  ·
                    refine ⟨314158418674703990786287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1675511566265087950860197 314158418674703990786287)
                    ·
                      rfl

theorem cell23_1835464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_1835464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835464 prefixEnd_1835464 := by exact prefixLift 1835464
  have htrace : WordTrace (prefixWord ++ tailWord_1835464) baseStart_1835464 baseEnd_1835464 := by
    simpa [prefixWord, tailWord_1835464, baseEnd_1835464] using wordTrace_append hprefix tailTrace_1835464
  have hstable : (prefixWord ++ tailWord_1835464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835464).length < 2 ^ (prefixWord ++ tailWord_1835464).sum := by decide
  have hdescent : baseEnd_1835464 < baseStart_1835464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835477 : List Nat := [1, 3, 2, 3, 1, 4, 1, 2, 6]
def baseStart_1835477 : Nat := 118140960795 + 1835477 * 2 ^ 59
def prefixEnd_1835477 : Nat := 4983230072969 + 3 ^ 40 * 1835477 * 2
def baseEnd_1835477 : Nat := 104720214585846713499589

theorem tailTrace_1835477 : CollatzResearch.WordTrace tailWord_1835477 prefixEnd_1835477 104720214585846713499589 := by
  unfold tailWord_1835477
  simp only [CollatzResearch.WordTrace]
  refine ⟨66945345971387778359728685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44630230647591852239819123 66945345971387778359728685)
  ·
    refine ⟨25104504739270416884898257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66945345971387778359728685 25104504739270416884898257)
    ·
      refine ⟨18828378554452812663673693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25104504739270416884898257 18828378554452812663673693)
      ·
        refine ⟨7060641957919804748877635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18828378554452812663673693 7060641957919804748877635)
        ·
          refine ⟨10590962936879707123316453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7060641957919804748877635 10590962936879707123316453)
          ·
            refine ⟨1985805550664945085621835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10590962936879707123316453 1985805550664945085621835)
            ·
              refine ⟨2978708325997417628432753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985805550664945085621835 2978708325997417628432753)
              ·
                refine ⟨2234031244498063221324565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978708325997417628432753 2234031244498063221324565)
                ·
                  refine ⟨104720214585846713499589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2234031244498063221324565 104720214585846713499589)
                  ·
                    rfl

theorem cell23_1835477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_1835477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835477 prefixEnd_1835477 := by exact prefixLift 1835477
  have htrace : WordTrace (prefixWord ++ tailWord_1835477) baseStart_1835477 baseEnd_1835477 := by
    simpa [prefixWord, tailWord_1835477, baseEnd_1835477] using wordTrace_append hprefix tailTrace_1835477
  have hstable : (prefixWord ++ tailWord_1835477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835477).length < 2 ^ (prefixWord ++ tailWord_1835477).sum := by decide
  have hdescent : baseEnd_1835477 < baseStart_1835477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835487 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 3]
def baseStart_1835487 : Nat := 118140960795 + 1835487 * 2 ^ 59
def prefixEnd_1835487 : Nat := 4983230072969 + 3 ^ 40 * 1835487 * 2
def baseEnd_1835487 : Nat := 942487066079165382371255

theorem tailTrace_1835487 : CollatzResearch.WordTrace tailWord_1835487 prefixEnd_1835487 942487066079165382371255 := by
  unfold tailWord_1835487
  simp only [CollatzResearch.WordTrace]
  refine ⟨66945710701351550067592715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44630473800901033378395143 66945710701351550067592715)
  ·
    refine ⟨100418566052027325101389073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66945710701351550067592715 100418566052027325101389073)
    ·
      refine ⟨75313924539020493826041805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100418566052027325101389073 75313924539020493826041805)
      ·
        refine ⟨28242721702132685184765677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75313924539020493826041805 28242721702132685184765677)
        ·
          refine ⟨10591020638299756944287129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28242721702132685184765677 10591020638299756944287129)
          ·
            refine ⟨7943265478724817708215347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10591020638299756944287129 7943265478724817708215347)
            ·
              refine ⟨11914898218087226562323021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943265478724817708215347 11914898218087226562323021)
              ·
                refine ⟨4468086831782709960871133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11914898218087226562323021 4468086831782709960871133)
                ·
                  refine ⟨1675532561918516235326675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4468086831782709960871133 1675532561918516235326675)
                  ·
                    refine ⟨2513298842877774352990013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675532561918516235326675 2513298842877774352990013)
                    ·
                      refine ⟨942487066079165382371255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513298842877774352990013 942487066079165382371255)
                      ·
                        rfl

theorem cell23_1835487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_1835487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835487 prefixEnd_1835487 := by exact prefixLift 1835487
  have htrace : WordTrace (prefixWord ++ tailWord_1835487) baseStart_1835487 baseEnd_1835487 := by
    simpa [prefixWord, tailWord_1835487, baseEnd_1835487] using wordTrace_append hprefix tailTrace_1835487
  have hstable : (prefixWord ++ tailWord_1835487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835487).length < 2 ^ (prefixWord ++ tailWord_1835487).sum := by decide
  have hdescent : baseEnd_1835487 < baseStart_1835487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835521 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_1835521 : Nat := 118140960795 + 1835521 * 2 ^ 59
def prefixEnd_1835521 : Nat := 4983230072969 + 3 ^ 40 * 1835521 * 2
def baseEnd_1835521 : Nat := 942504524421418249346099

theorem tailTrace_1835521 : CollatzResearch.WordTrace tailWord_1835521 prefixEnd_1835521 942504524421418249346099 := by
  unfold tailWord_1835521
  simp only [CollatzResearch.WordTrace]
  refine ⟨66946950783228373874330417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44631300522152249249553611 66946950783228373874330417)
  ·
    refine ⟨50210213087421280405747813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66946950783228373874330417 50210213087421280405747813)
    ·
      refine ⟨9414414953891490076077715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50210213087421280405747813 9414414953891490076077715)
      ·
        refine ⟨14121622430837235114116573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9414414953891490076077715 14121622430837235114116573)
        ·
          refine ⟨5295608411563963167793715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14121622430837235114116573 5295608411563963167793715)
          ·
            refine ⟨7943412617345944751690573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295608411563963167793715 7943412617345944751690573)
            ·
              refine ⟨2978779731504729281883965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7943412617345944751690573 2978779731504729281883965)
              ·
                refine ⟨1117042399314273480706487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2978779731504729281883965 1117042399314273480706487)
                ·
                  refine ⟨1675563598971410221059731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117042399314273480706487 1675563598971410221059731)
                  ·
                    refine ⟨2513345398457115331589597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675563598971410221059731 2513345398457115331589597)
                    ·
                      refine ⟨942504524421418249346099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513345398457115331589597 942504524421418249346099)
                      ·
                        rfl

theorem cell23_1835521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_1835521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835521 prefixEnd_1835521 := by exact prefixLift 1835521
  have htrace : WordTrace (prefixWord ++ tailWord_1835521) baseStart_1835521 baseEnd_1835521 := by
    simpa [prefixWord, tailWord_1835521, baseEnd_1835521] using wordTrace_append hprefix tailTrace_1835521
  have hstable : (prefixWord ++ tailWord_1835521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835521).length < 2 ^ (prefixWord ++ tailWord_1835521).sum := by decide
  have hdescent : baseEnd_1835521 < baseStart_1835521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835565 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1835565 : Nat := 118140960795 + 1835565 * 2 ^ 59
def prefixEnd_1835565 : Nat := 4983230072969 + 3 ^ 40 * 1835565 * 2
def baseEnd_1835565 : Nat := 942527117570216077195897

theorem tailTrace_1835565 : CollatzResearch.WordTrace tailWord_1835565 prefixEnd_1835565 942527117570216077195897 := by
  unfold tailWord_1835565
  simp only [CollatzResearch.WordTrace]
  refine ⟨66948555595068969388932149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44632370396712646259288099 66948555595068969388932149)
  ·
    refine ⟨6276427087037715880212389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66948555595068969388932149 6276427087037715880212389)
    ·
      refine ⟨1176830078819571727539823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6276427087037715880212389 1176830078819571727539823)
      ·
        refine ⟨1765245118229357591309735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1176830078819571727539823 1765245118229357591309735)
        ·
          refine ⟨2647867677344036386964603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765245118229357591309735 2647867677344036386964603)
          ·
            refine ⟨3971801516016054580446905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647867677344036386964603 3971801516016054580446905)
            ·
              refine ⟨2978851137012040935335179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971801516016054580446905 2978851137012040935335179)
              ·
                refine ⟨4468276705518061403002769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978851137012040935335179 4468276705518061403002769)
                ·
                  refine ⟨3351207529138546052252077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4468276705518061403002769 3351207529138546052252077)
                  ·
                    refine ⟨1256702823426954769594529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351207529138546052252077 1256702823426954769594529)
                    ·
                      refine ⟨942527117570216077195897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256702823426954769594529 942527117570216077195897)
                      ·
                        rfl

theorem cell23_1835565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1835565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835565 prefixEnd_1835565 := by exact prefixLift 1835565
  have htrace : WordTrace (prefixWord ++ tailWord_1835565) baseStart_1835565 baseEnd_1835565 := by
    simpa [prefixWord, tailWord_1835565, baseEnd_1835565] using wordTrace_append hprefix tailTrace_1835565
  have hstable : (prefixWord ++ tailWord_1835565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835565).length < 2 ^ (prefixWord ++ tailWord_1835565).sum := by decide
  have hdescent : baseEnd_1835565 < baseStart_1835565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835574 : List Nat := [5, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1835574 : Nat := 118140960795 + 1835574 * 2 ^ 59
def prefixEnd_1835574 : Nat := 4983230072969 + 3 ^ 40 * 1835574 * 2
def baseEnd_1835574 : Nat := 942531738896106541983355

theorem tailTrace_1835574 : CollatzResearch.WordTrace tailWord_1835574 prefixEnd_1835574 942531738896106541983355 := by
  unfold tailWord_1835574
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184305240752272745375611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44632589234690909284006517 4184305240752272745375611)
  ·
    refine ⟨6276457861128409118063417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4184305240752272745375611 6276457861128409118063417)
    ·
      refine ⟨4707343395846306838547563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6276457861128409118063417 4707343395846306838547563)
      ·
        refine ⟨7061015093769460257821345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707343395846306838547563 7061015093769460257821345)
        ·
          refine ⟨5295761320327095193366009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7061015093769460257821345 5295761320327095193366009)
          ·
            refine ⟨3971820990245321395024507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5295761320327095193366009 3971820990245321395024507)
            ·
              refine ⟨5957731485367982092536761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971820990245321395024507 5957731485367982092536761)
              ·
                refine ⟨4468298614025986569402571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5957731485367982092536761 4468298614025986569402571)
                ·
                  refine ⟨6702447921038979854103857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468298614025986569402571 6702447921038979854103857)
                  ·
                    refine ⟨5026835940779234890577893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6702447921038979854103857 5026835940779234890577893)
                    ·
                      refine ⟨942531738896106541983355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5026835940779234890577893 942531738896106541983355)
                      ·
                        rfl

theorem cell23_1835574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1835574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835574 prefixEnd_1835574 := by exact prefixLift 1835574
  have htrace : WordTrace (prefixWord ++ tailWord_1835574) baseStart_1835574 baseEnd_1835574 := by
    simpa [prefixWord, tailWord_1835574, baseEnd_1835574] using wordTrace_append hprefix tailTrace_1835574
  have hstable : (prefixWord ++ tailWord_1835574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835574).length < 2 ^ (prefixWord ++ tailWord_1835574).sum := by decide
  have hdescent : baseEnd_1835574 < baseStart_1835574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835577 : List Nat := [1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1835577 : Nat := 118140960795 + 1835577 * 2 ^ 59
def prefixEnd_1835577 : Nat := 4983230072969 + 3 ^ 40 * 1835577 * 2
def baseEnd_1835577 : Nat := 942533279338070030245841

theorem tailTrace_1835577 : CollatzResearch.WordTrace tailWord_1835577 prefixEnd_1835577 942533279338070030245841 := by
  unfold tailWord_1835577
  simp only [CollatzResearch.WordTrace]
  refine ⟨66948993271025495438368985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44632662180683663625579323 66948993271025495438368985)
  ·
    refine ⟨50211744953269121578776739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66948993271025495438368985 50211744953269121578776739)
    ·
      refine ⟨75317617429903682368165109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50211744953269121578776739 75317617429903682368165109)
      ·
        refine ⟨7061026634053470222015479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75317617429903682368165109 7061026634053470222015479)
        ·
          refine ⟨10591539951080205333023219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061026634053470222015479 10591539951080205333023219)
          ·
            refine ⟨15887309926620307999534829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591539951080205333023219 15887309926620307999534829)
            ·
              refine ⟨5957741222482615499825561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15887309926620307999534829 5957741222482615499825561)
              ·
                refine ⟨4468305916861961624869171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5957741222482615499825561 4468305916861961624869171)
                ·
                  refine ⟨6702458875292942437303757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468305916861961624869171 6702458875292942437303757)
                  ·
                    refine ⟨2513422078234853413988909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6702458875292942437303757 2513422078234853413988909)
                    ·
                      refine ⟨942533279338070030245841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513422078234853413988909 942533279338070030245841)
                      ·
                        rfl

theorem cell23_1835577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1835577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835577 prefixEnd_1835577 := by exact prefixLift 1835577
  have htrace : WordTrace (prefixWord ++ tailWord_1835577) baseStart_1835577 baseEnd_1835577 := by
    simpa [prefixWord, tailWord_1835577, baseEnd_1835577] using wordTrace_append hprefix tailTrace_1835577
  have hstable : (prefixWord ++ tailWord_1835577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835577).length < 2 ^ (prefixWord ++ tailWord_1835577).sum := by decide
  have hdescent : baseEnd_1835577 < baseStart_1835577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835581 : List Nat := [1, 4, 1, 3, 2, 2, 3, 1, 1, 2, 3]
def baseStart_1835581 : Nat := 118140960795 + 1835581 * 2 ^ 59
def prefixEnd_1835581 : Nat := 4983230072969 + 3 ^ 40 * 1835581 * 2
def baseEnd_1835581 : Nat := 942535333260688014595823

theorem tailTrace_1835581 : CollatzResearch.WordTrace tailWord_1835581 prefixEnd_1835581 942535333260688014595823 := by
  unfold tailWord_1835581
  simp only [CollatzResearch.WordTrace]
  refine ⟨66949139163011004121514597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44632759442007336081009731 66949139163011004121514597)
  ·
    refine ⟨12552963593064563272783987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66949139163011004121514597 12552963593064563272783987)
    ·
      refine ⟨18829445389596844909175981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12552963593064563272783987 18829445389596844909175981)
      ·
        refine ⟨7061042021098816840940993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18829445389596844909175981 7061042021098816840940993)
        ·
          refine ⟨5295781515824112630705745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7061042021098816840940993 5295781515824112630705745)
          ·
            refine ⟨3971836136868084473029309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5295781515824112630705745 3971836136868084473029309)
            ·
              refine ⟨1489438551325531677385991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3971836136868084473029309 1489438551325531677385991)
              ·
                refine ⟨2234157826988297516078987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489438551325531677385991 2234157826988297516078987)
                ·
                  refine ⟨3351236740482446274118481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234157826988297516078987 3351236740482446274118481)
                  ·
                    refine ⟨2513427555361834705588861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351236740482446274118481 2513427555361834705588861)
                    ·
                      refine ⟨942535333260688014595823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513427555361834705588861 942535333260688014595823)
                      ·
                        rfl

theorem cell23_1835581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 3, 1, 1, 2, 3].length) (baseStart_1835581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835581 prefixEnd_1835581 := by exact prefixLift 1835581
  have htrace : WordTrace (prefixWord ++ tailWord_1835581) baseStart_1835581 baseEnd_1835581 := by
    simpa [prefixWord, tailWord_1835581, baseEnd_1835581] using wordTrace_append hprefix tailTrace_1835581
  have hstable : (prefixWord ++ tailWord_1835581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835581).length < 2 ^ (prefixWord ++ tailWord_1835581).sum := by decide
  have hdescent : baseEnd_1835581 < baseStart_1835581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835594 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_1835594 : Nat := 118140960795 + 1835594 * 2 ^ 59
def prefixEnd_1835594 : Nat := 4983230072969 + 3 ^ 40 * 1835594 * 2
def baseEnd_1835594 : Nat := 942542008509196463733263

theorem tailTrace_1835594 : CollatzResearch.WordTrace tailWord_1835594 prefixEnd_1835594 942542008509196463733263 := by
  unfold tailWord_1835594
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737403327990976835434459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44633075541309271561158557 16737403327990976835434459)
  ·
    refine ⟨25106104991986465253151689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16737403327990976835434459 25106104991986465253151689)
    ·
      refine ⟨18829578743989848939863767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25106104991986465253151689 18829578743989848939863767)
      ·
        refine ⟨28244368115984773409795651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18829578743989848939863767 28244368115984773409795651)
        ·
          refine ⟨42366552173977160114693477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28244368115984773409795651 42366552173977160114693477)
          ·
            refine ⟨7943728532620717521505027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42366552173977160114693477 7943728532620717521505027)
            ·
              refine ⟨11915592798931076282257541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943728532620717521505027 11915592798931076282257541)
              ·
                refine ⟨2234173649799576802923289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11915592798931076282257541 2234173649799576802923289)
                ·
                  refine ⟨1675630237349682602192467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2234173649799576802923289 1675630237349682602192467)
                  ·
                    refine ⟨2513445356024523903288701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675630237349682602192467 2513445356024523903288701)
                    ·
                      refine ⟨942542008509196463733263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513445356024523903288701 942542008509196463733263)
                      ·
                        rfl

theorem cell23_1835594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_1835594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835594 prefixEnd_1835594 := by exact prefixLift 1835594
  have htrace : WordTrace (prefixWord ++ tailWord_1835594) baseStart_1835594 baseEnd_1835594 := by
    simpa [prefixWord, tailWord_1835594, baseEnd_1835594] using wordTrace_append hprefix tailTrace_1835594
  have hstable : (prefixWord ++ tailWord_1835594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835594).length < 2 ^ (prefixWord ++ tailWord_1835594).sum := by decide
  have hdescent : baseEnd_1835594 < baseStart_1835594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835597 : List Nat := [1, 6, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1835597 : Nat := 118140960795 + 1835597 * 2 ^ 59
def prefixEnd_1835597 : Nat := 4983230072969 + 3 ^ 40 * 1835597 * 2
def baseEnd_1835597 : Nat := 314181182983719983998583

theorem tailTrace_1835597 : CollatzResearch.WordTrace tailWord_1835597 prefixEnd_1835597 314181182983719983998583 := by
  unfold tailWord_1835597
  simp only [CollatzResearch.WordTrace]
  refine ⟨66949722730953038854097045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44633148487302025902731363 66949722730953038854097045)
  ·
    refine ⟨3138268253013423696285799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66949722730953038854097045 3138268253013423696285799)
    ·
      refine ⟨4707402379520135544428699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3138268253013423696285799 4707402379520135544428699)
      ·
        refine ⟨7061103569280203316643049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707402379520135544428699 7061103569280203316643049)
        ·
          refine ⟨5295827676960152487482287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7061103569280203316643049 5295827676960152487482287)
          ·
            refine ⟨7943741515440228731223431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5295827676960152487482287 7943741515440228731223431)
            ·
              refine ⟨11915612273160343096835147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943741515440228731223431 11915612273160343096835147)
              ·
                refine ⟨17873418409740514645252721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11915612273160343096835147 17873418409740514645252721)
                ·
                  refine ⟨13405063807305385983939541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17873418409740514645252721 13405063807305385983939541)
                  ·
                    refine ⟨314181182983719983998583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13405063807305385983939541 314181182983719983998583)
                    ·
                      rfl

theorem cell23_1835597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1835597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835597 prefixEnd_1835597 := by exact prefixLift 1835597
  have htrace : WordTrace (prefixWord ++ tailWord_1835597) baseStart_1835597 baseEnd_1835597 := by
    simpa [prefixWord, tailWord_1835597, baseEnd_1835597] using wordTrace_append hprefix tailTrace_1835597
  have hstable : (prefixWord ++ tailWord_1835597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835597).length < 2 ^ (prefixWord ++ tailWord_1835597).sum := by decide
  have hdescent : baseEnd_1835597 < baseStart_1835597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835604 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 3, 3, 2]
def baseStart_1835604 : Nat := 118140960795 + 1835604 * 2 ^ 59
def prefixEnd_1835604 : Nat := 4983230072969 + 3 ^ 40 * 1835604 * 2
def baseEnd_1835604 : Nat := 942547143315741424608217

theorem tailTrace_1835604 : CollatzResearch.WordTrace tailWord_1835604 prefixEnd_1835604 942547143315741424608217 := by
  unfold tailWord_1835604
  simp only [CollatzResearch.WordTrace]
  refine ⟨33474989020963839524800933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44633318694618452699734577 33474989020963839524800933)
  ·
    refine ⟨6276560441430719910900175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33474989020963839524800933 6276560441430719910900175)
    ·
      refine ⟨9414840662146079866350263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6276560441430719910900175 9414840662146079866350263)
      ·
        refine ⟨14122260993219119799525395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9414840662146079866350263 14122260993219119799525395)
        ·
          refine ⟨21183391489828679699288093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14122260993219119799525395 21183391489828679699288093)
          ·
            refine ⟨7943771808685754887233035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21183391489828679699288093 7943771808685754887233035)
            ·
              refine ⟨11915657713028632330849553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7943771808685754887233035 11915657713028632330849553)
              ·
                refine ⟨8936743284771474248137165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11915657713028632330849553 8936743284771474248137165)
                ·
                  refine ⟨3351278731789302843051437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8936743284771474248137165 3351278731789302843051437)
                  ·
                    refine ⟨1256729524420988566144289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351278731789302843051437 1256729524420988566144289)
                    ·
                      refine ⟨942547143315741424608217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256729524420988566144289 942547143315741424608217)
                      ·
                        rfl

theorem cell23_1835604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 3, 2].length) (baseStart_1835604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835604 prefixEnd_1835604 := by exact prefixLift 1835604
  have htrace : WordTrace (prefixWord ++ tailWord_1835604) baseStart_1835604 baseEnd_1835604 := by
    simpa [prefixWord, tailWord_1835604, baseEnd_1835604] using wordTrace_append hprefix tailTrace_1835604
  have hstable : (prefixWord ++ tailWord_1835604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835604).length < 2 ^ (prefixWord ++ tailWord_1835604).sum := by decide
  have hdescent : baseEnd_1835604 < baseStart_1835604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835638 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1835638 : Nat := 118140960795 + 1835638 * 2 ^ 59
def prefixEnd_1835638 : Nat := 4983230072969 + 3 ^ 40 * 1835638 * 2
def baseEnd_1835638 : Nat := 942564601657994291583061

theorem tailTrace_1835638 : CollatzResearch.WordTrace tailWord_1835638 prefixEnd_1835638 942564601657994291583061 := by
  unfold tailWord_1835638
  simp only [CollatzResearch.WordTrace]
  refine ⟨4184451132737781428521223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44634145415869668570893045 4184451132737781428521223)
  ·
    refine ⟨6276676699106672142781835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4184451132737781428521223 6276676699106672142781835)
    ·
      refine ⟨9415015048660008214172753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6276676699106672142781835 9415015048660008214172753)
      ·
        refine ⟨7061261286495006160629565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9415015048660008214172753 7061261286495006160629565)
        ·
          refine ⟨2647972982435627310236087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7061261286495006160629565 2647972982435627310236087)
          ·
            refine ⟨3971959473653440965354131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647972982435627310236087 3971959473653440965354131)
            ·
              refine ⟨5957939210480161448031197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3971959473653440965354131 5957939210480161448031197)
              ·
                refine ⟨2234227203930060543011699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5957939210480161448031197 2234227203930060543011699)
                ·
                  refine ⟨3351340805895090814517549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234227203930060543011699 3351340805895090814517549)
                  ·
                    refine ⟨1256752802210659055444081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351340805895090814517549 1256752802210659055444081)
                    ·
                      refine ⟨942564601657994291583061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256752802210659055444081 942564601657994291583061)
                      ·
                        rfl

theorem cell23_1835638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1835638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835638 prefixEnd_1835638 := by exact prefixLift 1835638
  have htrace : WordTrace (prefixWord ++ tailWord_1835638) baseStart_1835638 baseEnd_1835638 := by
    simpa [prefixWord, tailWord_1835638, baseEnd_1835638] using wordTrace_append hprefix tailTrace_1835638
  have hstable : (prefixWord ++ tailWord_1835638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835638).length < 2 ^ (prefixWord ++ tailWord_1835638).sum := by decide
  have hdescent : baseEnd_1835638 < baseStart_1835638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835651 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 2, 2, 2]
def baseStart_1835651 : Nat := 118140960795 + 1835651 * 2 ^ 59
def prefixEnd_1835651 : Nat := 4983230072969 + 3 ^ 40 * 1835651 * 2
def baseEnd_1835651 : Nat := 942571276906502740720501

theorem tailTrace_1835651 : CollatzResearch.WordTrace tailWord_1835651 prefixEnd_1835651 942571276906502740720501 := by
  unfold tailWord_1835651
  simp only [CollatzResearch.WordTrace]
  refine ⟨66951692272757406076562807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44634461515171604051041871 66951692272757406076562807)
  ·
    refine ⟨100427538409136109114844211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66951692272757406076562807 100427538409136109114844211)
    ·
      refine ⟨150641307613704163672266317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100427538409136109114844211 150641307613704163672266317)
      ·
        refine ⟨56490490355139061377099869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150641307613704163672266317 56490490355139061377099869)
        ·
          refine ⟨21183933883177148016412451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56490490355139061377099869 21183933883177148016412451)
          ·
            refine ⟨31775900824765722024618677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21183933883177148016412451 31775900824765722024618677)
            ·
              refine ⟨2978990702321786439808001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31775900824765722024618677 2978990702321786439808001)
              ·
                refine ⟨2234243026741339829856001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978990702321786439808001 2234243026741339829856001)
                ·
                  refine ⟨1675682270056004872392001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2234243026741339829856001 1675682270056004872392001)
                  ·
                    refine ⟨1256761702542003654294001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675682270056004872392001 1256761702542003654294001)
                    ·
                      refine ⟨942571276906502740720501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256761702542003654294001 942571276906502740720501)
                      ·
                        rfl

theorem cell23_1835651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_1835651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835651 prefixEnd_1835651 := by exact prefixLift 1835651
  have htrace : WordTrace (prefixWord ++ tailWord_1835651) baseStart_1835651 baseEnd_1835651 := by
    simpa [prefixWord, tailWord_1835651, baseEnd_1835651] using wordTrace_append hprefix tailTrace_1835651
  have hstable : (prefixWord ++ tailWord_1835651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835651).length < 2 ^ (prefixWord ++ tailWord_1835651).sum := by decide
  have hdescent : baseEnd_1835651 < baseStart_1835651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835668 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1835668 : Nat := 118140960795 + 1835668 * 2 ^ 59
def prefixEnd_1835668 : Nat := 4983230072969 + 3 ^ 40 * 1835668 * 2
def baseEnd_1835668 : Nat := 942580006077629174207923

theorem tailTrace_1835668 : CollatzResearch.WordTrace tailWord_1835668 prefixEnd_1835668 942580006077629174207923 := by
  unfold tailWord_1835668
  simp only [CollatzResearch.WordTrace]
  refine ⟨33476156156847908989965829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44634874875797211986621105 33476156156847908989965829)
  ·
    refine ⟨6276779279408982935618593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33476156156847908989965829 6276779279408982935618593)
    ·
      refine ⟨4707584459556737201713945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6276779279408982935618593 4707584459556737201713945)
      ·
        refine ⟨3530688344667552901285459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4707584459556737201713945 3530688344667552901285459)
        ·
          refine ⟨5296032517001329351928189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3530688344667552901285459 5296032517001329351928189)
          ·
            refine ⟨1986012193875498506973071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5296032517001329351928189 1986012193875498506973071)
            ·
              refine ⟨2979018290813247760459607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986012193875498506973071 2979018290813247760459607)
              ·
                refine ⟨4468527436219871640689411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979018290813247760459607 4468527436219871640689411)
                ·
                  refine ⟨6702791154329807461034117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4468527436219871640689411 6702791154329807461034117)
                  ·
                    refine ⟨1256773341436838898943897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6702791154329807461034117 1256773341436838898943897)
                    ·
                      refine ⟨942580006077629174207923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256773341436838898943897 942580006077629174207923)
                      ·
                        rfl

theorem cell23_1835668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1835668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835668 prefixEnd_1835668 := by exact prefixLift 1835668
  have htrace : WordTrace (prefixWord ++ tailWord_1835668) baseStart_1835668 baseEnd_1835668 := by
    simpa [prefixWord, tailWord_1835668, baseEnd_1835668] using wordTrace_append hprefix tailTrace_1835668
  have hstable : (prefixWord ++ tailWord_1835668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835668).length < 2 ^ (prefixWord ++ tailWord_1835668).sum := by decide
  have hdescent : baseEnd_1835668 < baseStart_1835668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835808 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 1, 1, 3]
def baseStart_1835808 : Nat := 118140960795 + 1835808 * 2 ^ 59
def prefixEnd_1835808 : Nat := 4983230072969 + 3 ^ 40 * 1835808 * 2
def baseEnd_1835808 : Nat := 942651893369258626457279

theorem tailTrace_1835808 : CollatzResearch.WordTrace tailWord_1835808 prefixEnd_1835808 942651893369258626457279 := by
  unfold tailWord_1835808
  simp only [CollatzResearch.WordTrace]
  refine ⟨33478709266594310945014039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44638279022125747926685385 33478709266594310945014039)
  ·
    refine ⟨50218063899891466417521059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33478709266594310945014039 50218063899891466417521059)
    ·
      refine ⟨75327095849837199626281589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50218063899891466417521059 75327095849837199626281589)
      ·
        refine ⟨7061915235922237464963899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75327095849837199626281589 7061915235922237464963899)
        ·
          refine ⟨10592872853883356197445849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061915235922237464963899 10592872853883356197445849)
          ·
            refine ⟨7944654640412517148084387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10592872853883356197445849 7944654640412517148084387)
            ·
              refine ⟨11916981960618775722126581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7944654640412517148084387 11916981960618775722126581)
              ·
                refine ⟨1117217058808010223949367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11916981960618775722126581 1117217058808010223949367)
                ·
                  refine ⟨1675825588212015335924051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117217058808010223949367 1675825588212015335924051)
                  ·
                    refine ⟨2513738382318023003886077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1675825588212015335924051 2513738382318023003886077)
                    ·
                      refine ⟨942651893369258626457279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513738382318023003886077 942651893369258626457279)
                      ·
                        rfl

theorem cell23_1835808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_1835808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835808 prefixEnd_1835808 := by exact prefixLift 1835808
  have htrace : WordTrace (prefixWord ++ tailWord_1835808) baseStart_1835808 baseEnd_1835808 := by
    simpa [prefixWord, tailWord_1835808, baseEnd_1835808] using wordTrace_append hprefix tailTrace_1835808
  have hstable : (prefixWord ++ tailWord_1835808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835808).length < 2 ^ (prefixWord ++ tailWord_1835808).sum := by decide
  have hdescent : baseEnd_1835808 < baseStart_1835808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835864 : List Nat := [2, 1, 2, 2, 1, 1, 1, 6, 1, 3, 3]
def baseStart_1835864 : Nat := 118140960795 + 1835864 * 2 ^ 59
def prefixEnd_1835864 : Nat := 4983230072969 + 3 ^ 40 * 1835864 * 2
def baseEnd_1835864 : Nat := 942680648285910407357021

theorem tailTrace_1835864 : CollatzResearch.WordTrace tailWord_1835864 prefixEnd_1835864 942680648285910407357021 := by
  unfold tailWord_1835864
  simp only [CollatzResearch.WordTrace]
  refine ⟨33479730510492871727033323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44639640680657162302711097 33479730510492871727033323)
  ·
    refine ⟨50219595765739307590549985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33479730510492871727033323 50219595765739307590549985)
    ·
      refine ⟨37664696824304480692912489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50219595765739307590549985 37664696824304480692912489)
      ·
        refine ⟨28248522618228360519684367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37664696824304480692912489 28248522618228360519684367)
        ·
          refine ⟨42372783927342540779526551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28248522618228360519684367 42372783927342540779526551)
          ·
            refine ⟨63559175891013811169289827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42372783927342540779526551 63559175891013811169289827)
            ·
              refine ⟨95338763836520716753934741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63559175891013811169289827 95338763836520716753934741)
              ·
                refine ⟨4469004554836908597840691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95338763836520716753934741 4469004554836908597840691)
                ·
                  refine ⟨6703506832255362896761037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4469004554836908597840691 6703506832255362896761037)
                  ·
                    refine ⟨2513815062095761086285389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6703506832255362896761037 2513815062095761086285389)
                    ·
                      refine ⟨942680648285910407357021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513815062095761086285389 942680648285910407357021)
                      ·
                        rfl

theorem cell23_1835864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_1835864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835864 prefixEnd_1835864 := by exact prefixLift 1835864
  have htrace : WordTrace (prefixWord ++ tailWord_1835864) baseStart_1835864 baseEnd_1835864 := by
    simpa [prefixWord, tailWord_1835864, baseEnd_1835864] using wordTrace_append hprefix tailTrace_1835864
  have hstable : (prefixWord ++ tailWord_1835864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835864).length < 2 ^ (prefixWord ++ tailWord_1835864).sum := by decide
  have hdescent : baseEnd_1835864 < baseStart_1835864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835865 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 1, 2, 2]
def baseStart_1835865 : Nat := 118140960795 + 1835865 * 2 ^ 59
def prefixEnd_1835865 : Nat := 4983230072969 + 3 ^ 40 * 1835865 * 2
def baseEnd_1835865 : Nat := 942681161766564903444517

theorem tailTrace_1835865 : CollatzResearch.WordTrace tailWord_1835865 prefixEnd_1835865 942681161766564903444517 := by
  unfold tailWord_1835865
  simp only [CollatzResearch.WordTrace]
  refine ⟨66959497493982120624853049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44639664995988080416568699 66959497493982120624853049)
  ·
    refine ⟨50219623120486590468639787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66959497493982120624853049 50219623120486590468639787)
    ·
      refine ⟨75329434680729885702959681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50219623120486590468639787 75329434680729885702959681)
      ·
        refine ⟨56497076010547414277219761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75329434680729885702959681 56497076010547414277219761)
        ·
          refine ⟨42372807007910560707914821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56497076010547414277219761 42372807007910560707914821)
          ·
            refine ⟨7944901313983230132734029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42372807007910560707914821 7944901313983230132734029)
            ·
              refine ⟨2979337992743711299775261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7944901313983230132734029 2979337992743711299775261)
              ·
                refine ⟨1117251747278891737415723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2979337992743711299775261 1117251747278891737415723)
                ·
                  refine ⟨1675877620918337606123585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117251747278891737415723 1675877620918337606123585)
                  ·
                    refine ⟨1256908215688753204592689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675877620918337606123585 1256908215688753204592689)
                    ·
                      refine ⟨942681161766564903444517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256908215688753204592689 942681161766564903444517)
                      ·
                        rfl

theorem cell23_1835865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 2, 2].length) (baseStart_1835865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835865 prefixEnd_1835865 := by exact prefixLift 1835865
  have htrace : WordTrace (prefixWord ++ tailWord_1835865) baseStart_1835865 baseEnd_1835865 := by
    simpa [prefixWord, tailWord_1835865, baseEnd_1835865] using wordTrace_append hprefix tailTrace_1835865
  have hstable : (prefixWord ++ tailWord_1835865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835865).length < 2 ^ (prefixWord ++ tailWord_1835865).sum := by decide
  have hdescent : baseEnd_1835865 < baseStart_1835865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835868 : List Nat := [2, 2, 4, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_1835868 : Nat := 118140960795 + 1835868 * 2 ^ 59
def prefixEnd_1835868 : Nat := 4983230072969 + 3 ^ 40 * 1835868 * 2
def baseEnd_1835868 : Nat := 942682702208528391707003

theorem tailTrace_1835868 : CollatzResearch.WordTrace tailWord_1835868 prefixEnd_1835868 942682702208528391707003 := by
  unfold tailWord_1835868
  simp only [CollatzResearch.WordTrace]
  refine ⟨33479803456485626068606129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44639737941980834758141505 33479803456485626068606129)
  ·
    refine ⟨25109852592364219551454597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33479803456485626068606129 25109852592364219551454597)
    ·
      refine ⟨4708097361068291165897737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25109852592364219551454597 4708097361068291165897737)
      ·
        refine ⟨3531073020801218374423303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4708097361068291165897737 3531073020801218374423303)
        ·
          refine ⟨5296609531201827561634955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531073020801218374423303 5296609531201827561634955)
          ·
            refine ⟨7944914296802741342452433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296609531201827561634955 7944914296802741342452433)
            ·
              refine ⟨5958685722602056006839325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7944914296802741342452433 5958685722602056006839325)
              ·
                refine ⟨2234507145975771002564747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5958685722602056006839325 2234507145975771002564747)
                ·
                  refine ⟨3351760718963656503847121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234507145975771002564747 3351760718963656503847121)
                  ·
                    refine ⟨2513820539222742377885341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351760718963656503847121 2513820539222742377885341)
                    ·
                      refine ⟨942682702208528391707003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513820539222742377885341 942682702208528391707003)
                      ·
                        rfl

theorem cell23_1835868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_1835868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835868 prefixEnd_1835868 := by exact prefixLift 1835868
  have htrace : WordTrace (prefixWord ++ tailWord_1835868) baseStart_1835868 baseEnd_1835868 := by
    simpa [prefixWord, tailWord_1835868, baseEnd_1835868] using wordTrace_append hprefix tailTrace_1835868
  have hstable : (prefixWord ++ tailWord_1835868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835868).length < 2 ^ (prefixWord ++ tailWord_1835868).sum := by decide
  have hdescent : baseEnd_1835868 < baseStart_1835868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835902 : List Nat := [4, 2, 3, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1835902 : Nat := 118140960795 + 1835902 * 2 ^ 59
def prefixEnd_1835902 : Nat := 4983230072969 + 3 ^ 40 * 1835902 * 2
def baseEnd_1835902 : Nat := 942700160550781258681847

theorem tailTrace_1835902 : CollatzResearch.WordTrace tailWord_1835902 prefixEnd_1835902 942700160550781258681847 := by
  unfold tailWord_1835902
  simp only [CollatzResearch.WordTrace]
  refine ⟨8370105874356009492993745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44640564663232050629299973 8370105874356009492993745)
  ·
    refine ⟨6277579405767007119745309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8370105874356009492993745 6277579405767007119745309)
    ·
      refine ⟨2354092277162627669904491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6277579405767007119745309 2354092277162627669904491)
      ·
        refine ⟨3531138415743941504856737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354092277162627669904491 3531138415743941504856737)
        ·
          refine ⟨2648353811807956128642553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3531138415743941504856737 2648353811807956128642553)
          ·
            refine ⟨1986265358855967096481915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648353811807956128642553 1986265358855967096481915)
            ·
              refine ⟨2979398038283950644722873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986265358855967096481915 2979398038283950644722873)
              ·
                refine ⟨2234548528712962983542155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979398038283950644722873 2234548528712962983542155)
                ·
                  refine ⟨3351822793069444475313233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234548528712962983542155 3351822793069444475313233)
                  ·
                    refine ⟨2513867094802083356484925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3351822793069444475313233 2513867094802083356484925)
                    ·
                      refine ⟨942700160550781258681847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2513867094802083356484925 942700160550781258681847)
                      ·
                        rfl

theorem cell23_1835902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1835902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835902 prefixEnd_1835902 := by exact prefixLift 1835902
  have htrace : WordTrace (prefixWord ++ tailWord_1835902) baseStart_1835902 baseEnd_1835902 := by
    simpa [prefixWord, tailWord_1835902, baseEnd_1835902] using wordTrace_append hprefix tailTrace_1835902
  have hstable : (prefixWord ++ tailWord_1835902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835902).length < 2 ^ (prefixWord ++ tailWord_1835902).sum := by decide
  have hdescent : baseEnd_1835902 < baseStart_1835902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835925 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_1835925 : Nat := 118140960795 + 1835925 * 2 ^ 59
def prefixEnd_1835925 : Nat := 4983230072969 + 3 ^ 40 * 1835925 * 2
def baseEnd_1835925 : Nat := 942711970605834668694241

theorem tailTrace_1835925 : CollatzResearch.WordTrace tailWord_1835925 prefixEnd_1835925 942711970605834668694241 := by
  unfold tailWord_1835925
  simp only [CollatzResearch.WordTrace]
  refine ⟨66961685873764750872037229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44641123915843167248024819 66961685873764750872037229)
  ·
    refine ⟨25110632202661781577013961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66961685873764750872037229 25110632202661781577013961)
    ·
      refine ⟨18832974151996336182760471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25110632202661781577013961 18832974151996336182760471)
      ·
        refine ⟨28249461227994504274140707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18832974151996336182760471 28249461227994504274140707)
        ·
          refine ⟨42374191841991756411211061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28249461227994504274140707 42374191841991756411211061)
          ·
            refine ⟨3972580485186727163551037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42374191841991756411211061 3972580485186727163551037)
            ·
              refine ⟨1489717681945022686331639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3972580485186727163551037 1489717681945022686331639)
              ·
                refine ⟨2234576522917534029497459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489717681945022686331639 2234576522917534029497459)
                ·
                  refine ⟨3351864784376301044246189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234576522917534029497459 3351864784376301044246189)
                  ·
                    refine ⟨1256949294141112891592321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3351864784376301044246189 1256949294141112891592321)
                    ·
                      refine ⟨942711970605834668694241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256949294141112891592321 942711970605834668694241)
                      ·
                        rfl

theorem cell23_1835925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_1835925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835925 prefixEnd_1835925 := by exact prefixLift 1835925
  have htrace : WordTrace (prefixWord ++ tailWord_1835925) baseStart_1835925 baseEnd_1835925 := by
    simpa [prefixWord, tailWord_1835925, baseEnd_1835925] using wordTrace_append hprefix tailTrace_1835925
  have hstable : (prefixWord ++ tailWord_1835925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835925).length < 2 ^ (prefixWord ++ tailWord_1835925).sum := by decide
  have hdescent : baseEnd_1835925 < baseStart_1835925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1835989 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1835989 : Nat := 118140960795 + 1835989 * 2 ^ 59
def prefixEnd_1835989 : Nat := 4983230072969 + 3 ^ 40 * 1835989 * 2
def baseEnd_1835989 : Nat := 942744833367722418293947

theorem tailTrace_1835989 : CollatzResearch.WordTrace tailWord_1835989 prefixEnd_1835989 942744833367722418293947 := by
  unfold tailWord_1835989
  simp only [CollatzResearch.WordTrace]
  refine ⟨66964020145532889802367021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44642680097021926534911347 66964020145532889802367021)
  ·
    refine ⟨25111507554574833675887633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66964020145532889802367021 25111507554574833675887633)
    ·
      refine ⟨18833630665931125256915725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25111507554574833675887633 18833630665931125256915725)
      ·
        refine ⟨7062611499724171971343397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18833630665931125256915725 7062611499724171971343397)
        ·
          refine ⟨1324239656198282244626887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7062611499724171971343397 1324239656198282244626887)
          ·
            refine ⟨1986359484297423366940331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324239656198282244626887 1986359484297423366940331)
            ·
              refine ⟨2979539226446135050410497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986359484297423366940331 2979539226446135050410497)
              ·
                refine ⟨2234654419834601287807873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2979539226446135050410497 2234654419834601287807873)
                ·
                  refine ⟨1675990814875950965855905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2234654419834601287807873 1675990814875950965855905)
                  ·
                    refine ⟨1256993111156963224391929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1675990814875950965855905 1256993111156963224391929)
                    ·
                      refine ⟨942744833367722418293947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1256993111156963224391929 942744833367722418293947)
                      ·
                        rfl

theorem cell23_1835989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1835989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1835989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1835989 prefixEnd_1835989 := by exact prefixLift 1835989
  have htrace : WordTrace (prefixWord ++ tailWord_1835989) baseStart_1835989 baseEnd_1835989 := by
    simpa [prefixWord, tailWord_1835989, baseEnd_1835989] using wordTrace_append hprefix tailTrace_1835989
  have hstable : (prefixWord ++ tailWord_1835989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1835989).length < 2 ^ (prefixWord ++ tailWord_1835989).sum := by decide
  have hdescent : baseEnd_1835989 < baseStart_1835989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1835989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836024 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 6, 4]
def baseStart_1836024 : Nat := 118140960795 + 1836024 * 2 ^ 59
def prefixEnd_1836024 : Nat := 4983230072969 + 3 ^ 40 * 1836024 * 2
def baseEnd_1836024 : Nat := 942762805190629781356285

theorem tailTrace_1836024 : CollatzResearch.WordTrace tailWord_1836024 prefixEnd_1836024 942762805190629781356285 := by
  unfold tailWord_1836024
  simp only [CollatzResearch.WordTrace]
  refine ⟨33482648350203045389945563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44643531133604060519927417 33482648350203045389945563)
  ·
    refine ⟨50223972525304568084918345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33482648350203045389945563 50223972525304568084918345)
    ·
      refine ⟨37667979393978426063688759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50223972525304568084918345 37667979393978426063688759)
      ·
        refine ⟨56501969090967639095533139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37667979393978426063688759 56501969090967639095533139)
        ·
          refine ⟨84752953636451458643299709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56501969090967639095533139 84752953636451458643299709)
          ·
            refine ⟨31782357613669296991237391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84752953636451458643299709 31782357613669296991237391)
            ·
              refine ⟨47673536420503945486856087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31782357613669296991237391 47673536420503945486856087)
              ·
                refine ⟨71510304630755918230284131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47673536420503945486856087 71510304630755918230284131)
                ·
                  refine ⟨107265456946133877345426197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71510304630755918230284131 107265456946133877345426197)
                  ·
                    refine ⟨5028068294350025500566853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107265456946133877345426197 5028068294350025500566853)
                    ·
                      refine ⟨942762805190629781356285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5028068294350025500566853 942762805190629781356285)
                      ·
                        rfl

theorem cell23_1836024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 6, 4].length) (baseStart_1836024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836024 prefixEnd_1836024 := by exact prefixLift 1836024
  have htrace : WordTrace (prefixWord ++ tailWord_1836024) baseStart_1836024 baseEnd_1836024 := by
    simpa [prefixWord, tailWord_1836024, baseEnd_1836024] using wordTrace_append hprefix tailTrace_1836024
  have hstable : (prefixWord ++ tailWord_1836024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836024).length < 2 ^ (prefixWord ++ tailWord_1836024).sum := by decide
  have hdescent : baseEnd_1836024 < baseStart_1836024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836055 : List Nat := [1, 1, 3, 5, 1, 3, 1, 1, 3, 4]
def baseStart_1836055 : Nat := 118140960795 + 1836055 * 2 ^ 59
def prefixEnd_1836055 : Nat := 4983230072969 + 3 ^ 40 * 1836055 * 2
def baseEnd_1836055 : Nat := 314259574363639720022881

theorem tailTrace_1836055 : CollatzResearch.WordTrace tailWord_1836055 prefixEnd_1836055 314259574363639720022881 := by
  unfold tailWord_1836055
  simp only [CollatzResearch.WordTrace]
  refine ⟨66966427363293783074269619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44644284908862522049513079 66966427363293783074269619)
  ·
    refine ⟨100449641044940674611404429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66966427363293783074269619 100449641044940674611404429)
    ·
      refine ⟨37668615391852752979276661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100449641044940674611404429 37668615391852752979276661)
      ·
        refine ⟨3531432692986195591807187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37668615391852752979276661 3531432692986195591807187)
        ·
          refine ⟨5297149039479293387710781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531432692986195591807187 5297149039479293387710781)
          ·
            refine ⟨1986430889804735020391543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5297149039479293387710781 1986430889804735020391543)
            ·
              refine ⟨2979646334707102530587315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986430889804735020391543 2979646334707102530587315)
              ·
                refine ⟨4469469502060653795880973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979646334707102530587315 4469469502060653795880973)
                ·
                  refine ⟨1676051063272745173455365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4469469502060653795880973 1676051063272745173455365)
                  ·
                    refine ⟨314259574363639720022881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676051063272745173455365 314259574363639720022881)
                    ·
                      rfl

theorem cell23_1836055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 1, 3, 4].length) (baseStart_1836055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836055 prefixEnd_1836055 := by exact prefixLift 1836055
  have htrace : WordTrace (prefixWord ++ tailWord_1836055) baseStart_1836055 baseEnd_1836055 := by
    simpa [prefixWord, tailWord_1836055, baseEnd_1836055] using wordTrace_append hprefix tailTrace_1836055
  have hstable : (prefixWord ++ tailWord_1836055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836055).length < 2 ^ (prefixWord ++ tailWord_1836055).sum := by decide
  have hdescent : baseEnd_1836055 < baseStart_1836055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836068 : List Nat := [2, 3, 1, 4, 1, 2, 1, 3, 6]
def baseStart_1836068 : Nat := 118140960795 + 1836068 * 2 ^ 59
def prefixEnd_1836068 : Nat := 4983230072969 + 3 ^ 40 * 1836068 * 2
def baseEnd_1836068 : Nat := 104753933148825289911787

theorem tailTrace_1836068 : CollatzResearch.WordTrace tailWord_1836068 prefixEnd_1836068 104753933148825289911787 := by
  unfold tailWord_1836068
  simp only [CollatzResearch.WordTrace]
  refine ⟨33483450756123343147246429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44644601008164457529661905 33483450756123343147246429)
  ·
    refine ⟨12556294033546253680217411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33483450756123343147246429 12556294033546253680217411)
    ·
      refine ⟨18834441050319380520326117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12556294033546253680217411 18834441050319380520326117)
      ·
        refine ⟨3531457696934883847561147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18834441050319380520326117 3531457696934883847561147)
        ·
          refine ⟨5297186545402325771341721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531457696934883847561147 5297186545402325771341721)
          ·
            refine ⟨3972889909051744328506291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5297186545402325771341721 3972889909051744328506291)
            ·
              refine ⟨5959334863577616492759437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972889909051744328506291 5959334863577616492759437)
              ·
                refine ⟨2234750573841606184784789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5959334863577616492759437 2234750573841606184784789)
                ·
                  refine ⟨104753933148825289911787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2234750573841606184784789 104753933148825289911787)
                  ·
                    rfl

theorem cell23_1836068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_1836068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836068 prefixEnd_1836068 := by exact prefixLift 1836068
  have htrace : WordTrace (prefixWord ++ tailWord_1836068) baseStart_1836068 baseEnd_1836068 := by
    simpa [prefixWord, tailWord_1836068, baseEnd_1836068] using wordTrace_append hprefix tailTrace_1836068
  have hstable : (prefixWord ++ tailWord_1836068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836068).length < 2 ^ (prefixWord ++ tailWord_1836068).sum := by decide
  have hdescent : baseEnd_1836068 < baseStart_1836068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836081 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_1836081 : Nat := 118140960795 + 1836081 * 2 ^ 59
def prefixEnd_1836081 : Nat := 4983230072969 + 3 ^ 40 * 1836081 * 2
def baseEnd_1836081 : Nat := 314264024529312019447841

theorem tailTrace_1836081 : CollatzResearch.WordTrace tailWord_1836081 prefixEnd_1836081 314264024529312019447841 := by
  unfold tailWord_1836081
  simp only [CollatzResearch.WordTrace]
  refine ⟨66967375661199589514716097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44644917107466393009810731 66967375661199589514716097)
  ·
    refine ⟨50225531745899692136037073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66967375661199589514716097 50225531745899692136037073)
    ·
      refine ⟨37669148809424769102027805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50225531745899692136037073 37669148809424769102027805)
      ·
        refine ⟨14125930803534288413260427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37669148809424769102027805 14125930803534288413260427)
        ·
          refine ⟨21188896205301432619890641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14125930803534288413260427 21188896205301432619890641)
          ·
            refine ⟨15891672153976074464917981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21188896205301432619890641 15891672153976074464917981)
            ·
              refine ⟨5959377057741027924344243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15891672153976074464917981 5959377057741027924344243)
              ·
                refine ⟨8939065586611541886516365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5959377057741027924344243 8939065586611541886516365)
                ·
                  refine ⟨3352149594979328207443637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8939065586611541886516365 3352149594979328207443637)
                  ·
                    refine ⟨314264024529312019447841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3352149594979328207443637 314264024529312019447841)
                    ·
                      rfl

theorem cell23_1836081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_1836081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836081 prefixEnd_1836081 := by exact prefixLift 1836081
  have htrace : WordTrace (prefixWord ++ tailWord_1836081) baseStart_1836081 baseEnd_1836081 := by
    simpa [prefixWord, tailWord_1836081, baseEnd_1836081] using wordTrace_append hprefix tailTrace_1836081
  have hstable : (prefixWord ++ tailWord_1836081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836081).length < 2 ^ (prefixWord ++ tailWord_1836081).sum := by decide
  have hdescent : baseEnd_1836081 < baseStart_1836081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836095 : List Nat := [1, 1, 2, 2, 3, 1, 1, 7, 1, 1, 3]
def baseStart_1836095 : Nat := 118140960795 + 1836095 * 2 ^ 59
def prefixEnd_1836095 : Nat := 4983230072969 + 3 ^ 40 * 1836095 * 2
def baseEnd_1836095 : Nat := 942799262317099003568459

theorem tailTrace_1836095 : CollatzResearch.WordTrace tailWord_1836095 prefixEnd_1836095 942799262317099003568459 := by
  unfold tailWord_1836095
  simp only [CollatzResearch.WordTrace]
  refine ⟨66967886283148869905725739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44645257522099246603817159 66967886283148869905725739)
  ·
    refine ⟨100451829424723304858588609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66967886283148869905725739 100451829424723304858588609)
    ·
      refine ⟨75338872068542478643941457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100451829424723304858588609 75338872068542478643941457)
      ·
        refine ⟨56504154051406858982956093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75338872068542478643941457 56504154051406858982956093)
        ·
          refine ⟨21189057769277572118608535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56504154051406858982956093 21189057769277572118608535)
          ·
            refine ⟨31783586653916358177912803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21189057769277572118608535 31783586653916358177912803)
            ·
              refine ⟨47675379980874537266869205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31783586653916358177912803 47675379980874537266869205)
              ·
                refine ⟨1117391718301746967192247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47675379980874537266869205 1117391718301746967192247)
                ·
                  refine ⟨1676087577452620450788371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117391718301746967192247 1676087577452620450788371)
                  ·
                    refine ⟨2514131366178930676182557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676087577452620450788371 2514131366178930676182557)
                    ·
                      refine ⟨942799262317099003568459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2514131366178930676182557 942799262317099003568459)
                      ·
                        rfl

theorem cell23_1836095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 7, 1, 1, 3].length) (baseStart_1836095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836095 prefixEnd_1836095 := by exact prefixLift 1836095
  have htrace : WordTrace (prefixWord ++ tailWord_1836095) baseStart_1836095 baseEnd_1836095 := by
    simpa [prefixWord, tailWord_1836095, baseEnd_1836095] using wordTrace_append hprefix tailTrace_1836095
  have hstable : (prefixWord ++ tailWord_1836095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836095).length < 2 ^ (prefixWord ++ tailWord_1836095).sum := by decide
  have hdescent : baseEnd_1836095 < baseStart_1836095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836128 : List Nat := [2, 1, 1, 3, 2, 2, 1, 5, 2, 4]
def baseStart_1836128 : Nat := 118140960795 + 1836128 * 2 ^ 59
def prefixEnd_1836128 : Nat := 4983230072969 + 3 ^ 40 * 1836128 * 2
def baseEnd_1836128 : Nat := 314272069059565791485269

theorem tailTrace_1836128 : CollatzResearch.WordTrace tailWord_1836128 prefixEnd_1836128 314272069059565791485269 := by
  unfold tailWord_1836128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33484544946014658270838519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44646059928019544361118025 33484544946014658270838519)
  ·
    refine ⟨50226817419021987406257779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33484544946014658270838519 50226817419021987406257779)
    ·
      refine ⟨75340226128532981109386669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50226817419021987406257779 75340226128532981109386669)
      ·
        refine ⟨28252584798199867916020001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75340226128532981109386669 28252584798199867916020001)
        ·
          refine ⟨21189438598649900937015001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28252584798199867916020001 21189438598649900937015001)
          ·
            refine ⟨15892078948987425702761251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21189438598649900937015001 15892078948987425702761251)
            ·
              refine ⟨23838118423481138554141877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15892078948987425702761251 23838118423481138554141877)
              ·
                refine ⟨2234823602201356739450801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23838118423481138554141877 2234823602201356739450801)
                ·
                  refine ⟨1676117701651017554588101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2234823602201356739450801 1676117701651017554588101)
                  ·
                    refine ⟨314272069059565791485269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676117701651017554588101 314272069059565791485269)
                    ·
                      rfl

theorem cell23_1836128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 5, 2, 4].length) (baseStart_1836128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836128 prefixEnd_1836128 := by exact prefixLift 1836128
  have htrace : WordTrace (prefixWord ++ tailWord_1836128) baseStart_1836128 baseEnd_1836128 := by
    simpa [prefixWord, tailWord_1836128, baseEnd_1836128] using wordTrace_append hprefix tailTrace_1836128
  have hstable : (prefixWord ++ tailWord_1836128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836128).length < 2 ^ (prefixWord ++ tailWord_1836128).sum := by decide
  have hdescent : baseEnd_1836128 < baseStart_1836128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836135 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 5, 2, 2]
def baseStart_1836135 : Nat := 118140960795 + 1836135 * 2 ^ 59
def prefixEnd_1836135 : Nat := 4983230072969 + 3 ^ 40 * 1836135 * 2
def baseEnd_1836135 : Nat := 942819801543278847068275

theorem tailTrace_1836135 : CollatzResearch.WordTrace tailWord_1836135 prefixEnd_1836135 942819801543278847068275 := by
  unfold tailWord_1836135
  simp only [CollatzResearch.WordTrace]
  refine ⟨66969345203003956737181859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44646230135335971158121239 66969345203003956737181859)
  ·
    refine ⟨100454017804505935105772789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66969345203003956737181859 100454017804505935105772789)
    ·
      refine ⟨9417564169172431416166199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100454017804505935105772789 9417564169172431416166199)
      ·
        refine ⟨14126346253758647124249299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9417564169172431416166199 14126346253758647124249299)
        ·
          refine ⟨21189519380637970686373949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14126346253758647124249299 21189519380637970686373949)
          ·
            refine ⟨7946069767739239007390231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21189519380637970686373949 7946069767739239007390231)
            ·
              refine ⟨11919104651608858511085347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946069767739239007390231 11919104651608858511085347)
              ·
                refine ⟨17878656977413287766628021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11919104651608858511085347 17878656977413287766628021)
                ·
                  refine ⟨1676124091632495728121377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17878656977413287766628021 1676124091632495728121377)
                  ·
                    refine ⟨1257093068724371796091033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1676124091632495728121377 1257093068724371796091033)
                    ·
                      refine ⟨942819801543278847068275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257093068724371796091033 942819801543278847068275)
                      ·
                        rfl

theorem cell23_1836135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 2, 2].length) (baseStart_1836135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836135 prefixEnd_1836135 := by exact prefixLift 1836135
  have htrace : WordTrace (prefixWord ++ tailWord_1836135) baseStart_1836135 baseEnd_1836135 := by
    simpa [prefixWord, tailWord_1836135, baseEnd_1836135] using wordTrace_append hprefix tailTrace_1836135
  have hstable : (prefixWord ++ tailWord_1836135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836135).length < 2 ^ (prefixWord ++ tailWord_1836135).sum := by decide
  have hdescent : baseEnd_1836135 < baseStart_1836135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836149 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1836149 : Nat := 118140960795 + 1836149 * 2 ^ 59
def prefixEnd_1836149 : Nat := 4983230072969 + 3 ^ 40 * 1836149 * 2
def baseEnd_1836149 : Nat := 314275663424147264097737

theorem tailTrace_1836149 : CollatzResearch.WordTrace tailWord_1836149 prefixEnd_1836149 314275663424147264097737 := by
  unfold tailWord_1836149
  simp only [CollatzResearch.WordTrace]
  refine ⟨66969855824953237128191501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44646570549968824752127667 66969855824953237128191501)
  ·
    refine ⟨25113695934357463923071813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66969855824953237128191501 25113695934357463923071813)
    ·
      refine ⟨4708817987692024485575965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25113695934357463923071813 4708817987692024485575965)
      ·
        refine ⟨1765806745384509182090987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4708817987692024485575965 1765806745384509182090987)
        ·
          refine ⟨2648710118076763773136481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765806745384509182090987 2648710118076763773136481)
          ·
            refine ⟨1986532588557572829852361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648710118076763773136481 1986532588557572829852361)
            ·
              refine ⟨1489899441418179622389271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986532588557572829852361 1489899441418179622389271)
              ·
                refine ⟨2234849162127269433583907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489899441418179622389271 2234849162127269433583907)
                ·
                  refine ⟨3352273743190904150375861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2234849162127269433583907 3352273743190904150375861)
                  ·
                    refine ⟨314275663424147264097737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3352273743190904150375861 314275663424147264097737)
                    ·
                      rfl

theorem cell23_1836149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1836149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836149 prefixEnd_1836149 := by exact prefixLift 1836149
  have htrace : WordTrace (prefixWord ++ tailWord_1836149) baseStart_1836149 baseEnd_1836149 := by
    simpa [prefixWord, tailWord_1836149, baseEnd_1836149] using wordTrace_append hprefix tailTrace_1836149
  have hstable : (prefixWord ++ tailWord_1836149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836149).length < 2 ^ (prefixWord ++ tailWord_1836149).sum := by decide
  have hdescent : baseEnd_1836149 < baseStart_1836149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836152 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 1, 2, 2]
def baseStart_1836152 : Nat := 118140960795 + 1836152 * 2 ^ 59
def prefixEnd_1836152 : Nat := 4983230072969 + 3 ^ 40 * 1836152 * 2
def baseEnd_1836152 : Nat := 942828530714405280555697

theorem tailTrace_1836152 : CollatzResearch.WordTrace tailWord_1836152 prefixEnd_1836152 942828530714405280555697 := by
  unfold tailWord_1836152
  simp only [CollatzResearch.WordTrace]
  refine ⟨33484982621971184320275355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44646643495961579093700473 33484982621971184320275355)
  ·
    refine ⟨50227473932956776480413033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33484982621971184320275355 50227473932956776480413033)
    ·
      refine ⟨37670605449717582360309775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50227473932956776480413033 37670605449717582360309775)
      ·
        refine ⟨56505908174576373540464663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37670605449717582360309775 56505908174576373540464663)
        ·
          refine ⟨84758862261864560310696995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56505908174576373540464663 84758862261864560310696995)
          ·
            refine ⟨127138293392796840466045493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84758862261864560310696995 127138293392796840466045493)
            ·
              refine ⟨11919215005574703793691765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127138293392796840466045493 11919215005574703793691765)
              ·
                refine ⟨1117426406772628480658603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11919215005574703793691765 1117426406772628480658603)
                ·
                  refine ⟨1676139610158942720987905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117426406772628480658603 1676139610158942720987905)
                  ·
                    refine ⟨1257104707619207040740929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1676139610158942720987905 1257104707619207040740929)
                    ·
                      refine ⟨942828530714405280555697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257104707619207040740929 942828530714405280555697)
                      ·
                        rfl

theorem cell23_1836152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 2, 2].length) (baseStart_1836152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836152 prefixEnd_1836152 := by exact prefixLift 1836152
  have htrace : WordTrace (prefixWord ++ tailWord_1836152) baseStart_1836152 baseEnd_1836152 := by
    simpa [prefixWord, tailWord_1836152, baseEnd_1836152] using wordTrace_append hprefix tailTrace_1836152
  have hstable : (prefixWord ++ tailWord_1836152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836152).length < 2 ^ (prefixWord ++ tailWord_1836152).sum := by decide
  have hdescent : baseEnd_1836152 < baseStart_1836152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836202 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1836202 : Nat := 118140960795 + 1836202 * 2 ^ 59
def prefixEnd_1836202 : Nat := 4983230072969 + 3 ^ 40 * 1836202 * 2
def baseEnd_1836202 : Nat := 942854204747130084930467

theorem tailTrace_1836202 : CollatzResearch.WordTrace tailWord_1836202 prefixEnd_1836202 942854204747130084930467 := by
  unfold tailWord_1836202
  simp only [CollatzResearch.WordTrace]
  refine ⟨16742947223440306794967715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44647859262507484786580573 16742947223440306794967715)
  ·
    refine ⟨25114420835160460192451573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16742947223440306794967715 25114420835160460192451573)
    ·
      refine ⟨2354476953296293143042335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25114420835160460192451573 2354476953296293143042335)
      ·
        refine ⟨3531715429944439714563503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354476953296293143042335 3531715429944439714563503)
        ·
          refine ⟨5297573144916659571845255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531715429944439714563503 5297573144916659571845255)
          ·
            refine ⟨7946359717374989357767883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5297573144916659571845255 7946359717374989357767883)
            ·
              refine ⟨11919539576062484036651825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7946359717374989357767883 11919539576062484036651825)
              ·
                refine ⟨8939654682046863027488869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11919539576062484036651825 8939654682046863027488869)
                ·
                  refine ⟨1676185252883786817654163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8939654682046863027488869 1676185252883786817654163)
                  ·
                    refine ⟨2514277879325680226481245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676185252883786817654163 2514277879325680226481245)
                    ·
                      refine ⟨942854204747130084930467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2514277879325680226481245 942854204747130084930467)
                      ·
                        rfl

theorem cell23_1836202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1836202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836202 prefixEnd_1836202 := by exact prefixLift 1836202
  have htrace : WordTrace (prefixWord ++ tailWord_1836202) baseStart_1836202 baseEnd_1836202 := by
    simpa [prefixWord, tailWord_1836202, baseEnd_1836202] using wordTrace_append hprefix tailTrace_1836202
  have hstable : (prefixWord ++ tailWord_1836202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836202).length < 2 ^ (prefixWord ++ tailWord_1836202).sum := by decide
  have hdescent : baseEnd_1836202 < baseStart_1836202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836211 : List Nat := [1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5]
def baseStart_1836211 : Nat := 118140960795 + 1836211 * 2 ^ 59
def prefixEnd_1836211 : Nat := 4983230072969 + 3 ^ 40 * 1836211 * 2
def baseEnd_1836211 : Nat := 942858826073020549717925

theorem tailTrace_1836211 : CollatzResearch.WordTrace tailWord_1836211 prefixEnd_1836211 942858826073020549717925 := by
  unfold tailWord_1836211
  simp only [CollatzResearch.WordTrace]
  refine ⟨66972117150728621716948487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44648078100485747811298991 66972117150728621716948487)
  ·
    refine ⟨100458175726092932575422731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66972117150728621716948487 100458175726092932575422731)
    ·
      refine ⟨150687263589139398863134097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100458175726092932575422731 150687263589139398863134097)
      ·
        refine ⟨113015447691854549147350573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150687263589139398863134097 113015447691854549147350573)
        ·
          refine ⟨42380792884445455930256465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113015447691854549147350573 42380792884445455930256465)
          ·
            refine ⟨31785594663334091947692349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42380792884445455930256465 31785594663334091947692349)
            ·
              refine ⟨11919597998750284480384631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31785594663334091947692349 11919597998750284480384631)
              ·
                refine ⟨17879396998125426720576947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11919597998750284480384631 17879396998125426720576947)
                ·
                  refine ⟨26819095497188140080865421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17879396998125426720576947 26819095497188140080865421)
                  ·
                    refine ⟨10057160811445552530324533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26819095497188140080865421 10057160811445552530324533)
                    ·
                      refine ⟨942858826073020549717925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10057160811445552530324533 942858826073020549717925)
                      ·
                        rfl

theorem cell23_1836211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_1836211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836211 prefixEnd_1836211 := by exact prefixLift 1836211
  have htrace : WordTrace (prefixWord ++ tailWord_1836211) baseStart_1836211 baseEnd_1836211 := by
    simpa [prefixWord, tailWord_1836211, baseEnd_1836211] using wordTrace_append hprefix tailTrace_1836211
  have hstable : (prefixWord ++ tailWord_1836211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836211).length < 2 ^ (prefixWord ++ tailWord_1836211).sum := by decide
  have hdescent : baseEnd_1836211 < baseStart_1836211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836230 : List Nat := [6, 1, 2, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1836230 : Nat := 118140960795 + 1836230 * 2 ^ 59
def prefixEnd_1836230 : Nat := 4983230072969 + 3 ^ 40 * 1836230 * 2
def baseEnd_1836230 : Nat := 314289527401818658460113

theorem tailTrace_1836230 : CollatzResearch.WordTrace tailWord_1836230 prefixEnd_1836230 314289527401818658460113 := by
  unfold tailWord_1836230
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092900316801868373809067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44648540091773191974593429 2092900316801868373809067)
  ·
    refine ⟨3139350475202802560713601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2092900316801868373809067 3139350475202802560713601)
    ·
      refine ⟨2354512856402101920535201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3139350475202802560713601 2354512856402101920535201)
      ·
        refine ⟨1765884642301576440401401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2354512856402101920535201 1765884642301576440401401)
        ·
          refine ⟨1324413481726182330301051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1765884642301576440401401 1324413481726182330301051)
          ·
            refine ⟨1986620222589273495451577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324413481726182330301051 1986620222589273495451577)
            ·
              refine ⟨1489965166941955121588683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986620222589273495451577 1489965166941955121588683)
              ·
                refine ⟨2234947750412932682383025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489965166941955121588683 2234947750412932682383025)
                ·
                  refine ⟨1676210812809699511787269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2234947750412932682383025 1676210812809699511787269)
                  ·
                    refine ⟨314289527401818658460113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676210812809699511787269 314289527401818658460113)
                    ·
                      rfl

theorem cell23_1836230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1836230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836230 prefixEnd_1836230 := by exact prefixLift 1836230
  have htrace : WordTrace (prefixWord ++ tailWord_1836230) baseStart_1836230 baseEnd_1836230 := by
    simpa [prefixWord, tailWord_1836230, baseEnd_1836230] using wordTrace_append hprefix tailTrace_1836230
  have hstable : (prefixWord ++ tailWord_1836230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836230).length < 2 ^ (prefixWord ++ tailWord_1836230).sum := by decide
  have hdescent : baseEnd_1836230 < baseStart_1836230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836278 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1836278 : Nat := 118140960795 + 1836278 * 2 ^ 59
def prefixEnd_1836278 : Nat := 4983230072969 + 3 ^ 40 * 1836278 * 2
def baseEnd_1836278 : Nat := 314297743092290595860039

theorem tailTrace_1836278 : CollatzResearch.WordTrace tailWord_1836278 prefixEnd_1836278 314297743092290595860039 := by
  unfold tailWord_1836278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4185910052592868259977343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44649707227657261439758325 4185910052592868259977343)
  ·
    refine ⟨6278865078889302389966015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4185910052592868259977343 6278865078889302389966015)
    ·
      refine ⟨9418297618333953584949023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278865078889302389966015 9418297618333953584949023)
      ·
        refine ⟨14127446427500930377423535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9418297618333953584949023 14127446427500930377423535)
        ·
          refine ⟨21191169641251395566135303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127446427500930377423535 21191169641251395566135303)
          ·
            refine ⟨31786754461877093349202955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21191169641251395566135303 31786754461877093349202955)
            ·
              refine ⟨47680131692815640023804433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31786754461877093349202955 47680131692815640023804433)
              ·
                refine ⟨35760098769611730017853325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47680131692815640023804433 35760098769611730017853325)
                ·
                  refine ⟨13410037038604398756694997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35760098769611730017853325 13410037038604398756694997)
                  ·
                    refine ⟨314297743092290595860039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13410037038604398756694997 314297743092290595860039)
                    ·
                      rfl

theorem cell23_1836278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1836278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836278 prefixEnd_1836278 := by exact prefixLift 1836278
  have htrace : WordTrace (prefixWord ++ tailWord_1836278) baseStart_1836278 baseEnd_1836278 := by
    simpa [prefixWord, tailWord_1836278, baseEnd_1836278] using wordTrace_append hprefix tailTrace_1836278
  have hstable : (prefixWord ++ tailWord_1836278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836278).length < 2 ^ (prefixWord ++ tailWord_1836278).sum := by decide
  have hdescent : baseEnd_1836278 < baseStart_1836278 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836298 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1836298 : Nat := 118140960795 + 1836298 * 2 ^ 59
def prefixEnd_1836298 : Nat := 4983230072969 + 3 ^ 40 * 1836298 * 2
def baseEnd_1836298 : Nat := 942903498889961709330025

theorem tailTrace_1836298 : CollatzResearch.WordTrace tailWord_1836298 prefixEnd_1836298 942903498889961709330025 := by
  unfold tailWord_1836298
  simp only [CollatzResearch.WordTrace]
  refine ⟨16743822575353358893841387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44650193534275623716910365 16743822575353358893841387)
  ·
    refine ⟨25115733863030038340762081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16743822575353358893841387 25115733863030038340762081)
    ·
      refine ⟨18836800397272528755571561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25115733863030038340762081 18836800397272528755571561)
      ·
        refine ⟨14127600297954396566678671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18836800397272528755571561 14127600297954396566678671)
        ·
          refine ⟨21191400446931594850018007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14127600297954396566678671 21191400446931594850018007)
          ·
            refine ⟨31787100670397392275027011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21191400446931594850018007 31787100670397392275027011)
            ·
              refine ⟨47680651005596088412540517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31787100670397392275027011 47680651005596088412540517)
              ·
                refine ⟨8940122063549266577351347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47680651005596088412540517 8940122063549266577351347)
                ·
                  refine ⟨13410183095323899866027021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8940122063549266577351347 13410183095323899866027021)
                  ·
                    refine ⟨5028818660746462449760133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13410183095323899866027021 5028818660746462449760133)
                    ·
                      refine ⟨942903498889961709330025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5028818660746462449760133 942903498889961709330025)
                      ·
                        rfl

theorem cell23_1836298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1836298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836298 prefixEnd_1836298 := by exact prefixLift 1836298
  have htrace : WordTrace (prefixWord ++ tailWord_1836298) baseStart_1836298 baseEnd_1836298 := by
    simpa [prefixWord, tailWord_1836298, baseEnd_1836298] using wordTrace_append hprefix tailTrace_1836298
  have hstable : (prefixWord ++ tailWord_1836298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836298).length < 2 ^ (prefixWord ++ tailWord_1836298).sum := by decide
  have hdescent : baseEnd_1836298 < baseStart_1836298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836428 : List Nat := [2, 2, 1, 2, 1, 3, 1, 11]
def baseStart_1836428 : Nat := 118140960795 + 1836428 * 2 ^ 59
def prefixEnd_1836428 : Nat := 4983230072969 + 3 ^ 40 * 1836428 * 2
def baseEnd_1836428 : Nat := 34924824125001711137201

theorem tailTrace_1836428 : CollatzResearch.WordTrace tailWord_1836428 prefixEnd_1836428 34924824125001711137201 := by
  unfold tailWord_1836428
  simp only [CollatzResearch.WordTrace]
  refine ⟨33490015895471233888798969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44653354527294978518398625 33490015895471233888798969)
  ·
    refine ⟨25117511921603425416599227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33490015895471233888798969 25117511921603425416599227)
    ·
      refine ⟨37676267882405138124898841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25117511921603425416599227 37676267882405138124898841)
      ·
        refine ⟨28257200911803853593674131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37676267882405138124898841 28257200911803853593674131)
        ·
          refine ⟨42385801367705780390511197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28257200911803853593674131 42385801367705780390511197)
          ·
            refine ⟨15894675512889667646441699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42385801367705780390511197 15894675512889667646441699)
            ·
              refine ⟨23842013269334501469662549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15894675512889667646441699 23842013269334501469662549)
              ·
                refine ⟨34924824125001711137201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 23842013269334501469662549 34924824125001711137201)
                ·
                  rfl

theorem cell23_1836428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 11].length) (baseStart_1836428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836428 prefixEnd_1836428 := by exact prefixLift 1836428
  have htrace : WordTrace (prefixWord ++ tailWord_1836428) baseStart_1836428 baseEnd_1836428 := by
    simpa [prefixWord, tailWord_1836428, baseEnd_1836428] using wordTrace_append hprefix tailTrace_1836428
  have hstable : (prefixWord ++ tailWord_1836428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836428).length < 2 ^ (prefixWord ++ tailWord_1836428).sum := by decide
  have hdescent : baseEnd_1836428 < baseStart_1836428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836505 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_1836505 : Nat := 118140960795 + 1836505 * 2 ^ 59
def prefixEnd_1836505 : Nat := 4983230072969 + 3 ^ 40 * 1836505 * 2
def baseEnd_1836505 : Nat := 314336596461814133147191

theorem tailTrace_1836505 : CollatzResearch.WordTrace tailWord_1836505 prefixEnd_1836505 314336596461814133147191 := by
  unfold tailWord_1836505
  simp only [CollatzResearch.WordTrace]
  refine ⟨66982840211663509928150969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44655226807775673285433979 66982840211663509928150969)
  ·
    refine ⟨50237130158747632446113227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66982840211663509928150969 50237130158747632446113227)
    ·
      refine ⟨75355695238121448669169841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50237130158747632446113227 75355695238121448669169841)
      ·
        refine ⟨56516771428591086501877381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75355695238121448669169841 56516771428591086501877381)
        ·
          refine ⟨10596894642860828719102009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56516771428591086501877381 10596894642860828719102009)
          ·
            refine ⟨7947670982145621539326507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10596894642860828719102009 7947670982145621539326507)
            ·
              refine ⟨11921506473218432308989761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7947670982145621539326507 11921506473218432308989761)
              ·
                refine ⟨8941129854913824231742321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11921506473218432308989761 8941129854913824231742321)
                ·
                  refine ⟨6705847391185368173806741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8941129854913824231742321 6705847391185368173806741)
                  ·
                    refine ⟨314336596461814133147191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6705847391185368173806741 314336596461814133147191)
                    ·
                      rfl

theorem cell23_1836505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_1836505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836505 prefixEnd_1836505 := by exact prefixLift 1836505
  have htrace : WordTrace (prefixWord ++ tailWord_1836505) baseStart_1836505 baseEnd_1836505 := by
    simpa [prefixWord, tailWord_1836505, baseEnd_1836505] using wordTrace_append hprefix tailTrace_1836505
  have hstable : (prefixWord ++ tailWord_1836505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836505).length < 2 ^ (prefixWord ++ tailWord_1836505).sum := by decide
  have hdescent : baseEnd_1836505 < baseStart_1836505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836506 : List Nat := [3, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3]
def baseStart_1836506 : Nat := 118140960795 + 1836506 * 2 ^ 59
def prefixEnd_1836506 : Nat := 4983230072969 + 3 ^ 40 * 1836506 * 2
def baseEnd_1836506 : Nat := 943010302866096895529069

theorem tailTrace_1836506 : CollatzResearch.WordTrace tailWord_1836506 prefixEnd_1836506 943010302866096895529069 := by
  unfold tailWord_1836506
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745719171164971774734343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44655251123106591399291581 16745719171164971774734343)
  ·
    refine ⟨25118578756747457662101515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16745719171164971774734343 25118578756747457662101515)
    ·
      refine ⟨37677868135121186493152273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25118578756747457662101515 37677868135121186493152273)
      ·
        refine ⟨28258401101340889869864205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37677868135121186493152273 28258401101340889869864205)
        ·
          refine ⟨10596900413002833701199077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28258401101340889869864205 10596900413002833701199077)
          ·
            refine ⟨1986918827438031318974827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10596900413002833701199077 1986918827438031318974827)
            ·
              refine ⟨2980378241157046978462241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1986918827438031318974827 2980378241157046978462241)
              ·
                refine ⟨2235283680867785233846681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980378241157046978462241 2235283680867785233846681)
                ·
                  refine ⟨1676462760650838925385011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235283680867785233846681 1676462760650838925385011)
                  ·
                    refine ⟨2514694140976258388077517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676462760650838925385011 2514694140976258388077517)
                    ·
                      refine ⟨943010302866096895529069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2514694140976258388077517 943010302866096895529069)
                      ·
                        rfl

theorem cell23_1836506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 2, 2, 1, 3].length) (baseStart_1836506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836506 prefixEnd_1836506 := by exact prefixLift 1836506
  have htrace : WordTrace (prefixWord ++ tailWord_1836506) baseStart_1836506 baseEnd_1836506 := by
    simpa [prefixWord, tailWord_1836506, baseEnd_1836506] using wordTrace_append hprefix tailTrace_1836506
  have hstable : (prefixWord ++ tailWord_1836506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836506).length < 2 ^ (prefixWord ++ tailWord_1836506).sum := by decide
  have hdescent : baseEnd_1836506 < baseStart_1836506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836529 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 1, 4, 2]
def baseStart_1836529 : Nat := 118140960795 + 1836529 * 2 ^ 59
def prefixEnd_1836529 : Nat := 4983230072969 + 3 ^ 40 * 1836529 * 2
def baseEnd_1836529 : Nat := 943022112921150305541463

theorem tailTrace_1836529 : CollatzResearch.WordTrace tailWord_1836529 prefixEnd_1836529 943022112921150305541463 := by
  unfold tailWord_1836529
  simp only [CollatzResearch.WordTrace]
  refine ⟨66983715563576562027024641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44655810375717708018016427 66983715563576562027024641)
  ·
    refine ⟨50237786672682421520268481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66983715563576562027024641 50237786672682421520268481)
    ·
      refine ⟨37678340004511816140201361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50237786672682421520268481 37678340004511816140201361)
      ·
        refine ⟨28258755003383862105151021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37678340004511816140201361 28258755003383862105151021)
        ·
          refine ⟨10597033126268948289431633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28258755003383862105151021 10597033126268948289431633)
          ·
            refine ⟨7947774844701711217073725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10597033126268948289431633 7947774844701711217073725)
            ·
              refine ⟨2980415566763141706402647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7947774844701711217073725 2980415566763141706402647)
              ·
                refine ⟨4470623350144712559603971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980415566763141706402647 4470623350144712559603971)
                ·
                  refine ⟨6705935025217068839405957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4470623350144712559603971 6705935025217068839405957)
                  ·
                    refine ⟨1257362817228200407388617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6705935025217068839405957 1257362817228200407388617)
                    ·
                      refine ⟨943022112921150305541463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257362817228200407388617 943022112921150305541463)
                      ·
                        rfl

theorem cell23_1836529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_1836529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836529 prefixEnd_1836529 := by exact prefixLift 1836529
  have htrace : WordTrace (prefixWord ++ tailWord_1836529) baseStart_1836529 baseEnd_1836529 := by
    simpa [prefixWord, tailWord_1836529, baseEnd_1836529] using wordTrace_append hprefix tailTrace_1836529
  have hstable : (prefixWord ++ tailWord_1836529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836529).length < 2 ^ (prefixWord ++ tailWord_1836529).sum := by decide
  have hdescent : baseEnd_1836529 < baseStart_1836529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836533 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1836533 : Nat := 118140960795 + 1836533 * 2 ^ 59
def prefixEnd_1836533 : Nat := 4983230072969 + 3 ^ 40 * 1836533 * 2
def baseEnd_1836533 : Nat := 943024166843768289891445

theorem tailTrace_1836533 : CollatzResearch.WordTrace tailWord_1836533 prefixEnd_1836533 943024166843768289891445 := by
  unfold tailWord_1836533
  simp only [CollatzResearch.WordTrace]
  refine ⟨66983861455562070710170253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44655907637041380473446835 66983861455562070710170253)
  ·
    refine ⟨25118948045835776516313845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66983861455562070710170253 25118948045835776516313845)
    ·
      refine ⟨2354901379297104048404423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25118948045835776516313845 2354901379297104048404423)
      ·
        refine ⟨3532352068945656072606635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354901379297104048404423 3532352068945656072606635)
        ·
          refine ⟨5298528103418484108909953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532352068945656072606635 5298528103418484108909953)
          ·
            refine ⟨3973896077563863081682465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298528103418484108909953 3973896077563863081682465)
            ·
              refine ⟨2980422058172897311261849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3973896077563863081682465 2980422058172897311261849)
              ·
                refine ⟨2235316543629672983446387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980422058172897311261849 2235316543629672983446387)
                ·
                  refine ⟨3352974815444509475169581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235316543629672983446387 3352974815444509475169581)
                  ·
                    refine ⟨1257365555791691053188593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3352974815444509475169581 1257365555791691053188593)
                    ·
                      refine ⟨943024166843768289891445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257365555791691053188593 943024166843768289891445)
                      ·
                        rfl

theorem cell23_1836533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1836533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836533 prefixEnd_1836533 := by exact prefixLift 1836533
  have htrace : WordTrace (prefixWord ++ tailWord_1836533) baseStart_1836533 baseEnd_1836533 := by
    simpa [prefixWord, tailWord_1836533, baseEnd_1836533] using wordTrace_append hprefix tailTrace_1836533
  have hstable : (prefixWord ++ tailWord_1836533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836533).length < 2 ^ (prefixWord ++ tailWord_1836533).sum := by decide
  have hdescent : baseEnd_1836533 < baseStart_1836533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836574 : List Nat := [4, 3, 3, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_1836574 : Nat := 118140960795 + 1836574 * 2 ^ 59
def prefixEnd_1836574 : Nat := 4983230072969 + 3 ^ 40 * 1836574 * 2
def baseEnd_1836574 : Nat := 943045219550602629478757

theorem tailTrace_1836574 : CollatzResearch.WordTrace tailWord_1836574 prefixEnd_1836574 943045219550602629478757 := by
  unfold tailWord_1836574
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373169606051691839051597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44656904565609023141608517 8373169606051691839051597)
  ·
    refine ⟨3139938602269384439644349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8373169606051691839051597 3139938602269384439644349)
    ·
      refine ⟨1177476975851019164866631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3139938602269384439644349 1177476975851019164866631)
      ·
        refine ⟨1766215463776528747299947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177476975851019164866631 1766215463776528747299947)
        ·
          refine ⟨2649323195664793120949921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766215463776528747299947 2649323195664793120949921)
          ·
            refine ⟨1986992396748594840712441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649323195664793120949921 1986992396748594840712441)
            ·
              refine ⟨1490244297561446130534331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1986992396748594840712441 1490244297561446130534331)
              ·
                refine ⟨2235366446342169195801497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490244297561446130534331 2235366446342169195801497)
                ·
                  refine ⟨1676524834756626896851123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235366446342169195801497 1676524834756626896851123)
                  ·
                    refine ⟨2514787252134940345276685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676524834756626896851123 2514787252134940345276685)
                    ·
                      refine ⟨943045219550602629478757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2514787252134940345276685 943045219550602629478757)
                      ·
                        rfl

theorem cell23_1836574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_1836574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836574 prefixEnd_1836574 := by exact prefixLift 1836574
  have htrace : WordTrace (prefixWord ++ tailWord_1836574) baseStart_1836574 baseEnd_1836574 := by
    simpa [prefixWord, tailWord_1836574, baseEnd_1836574] using wordTrace_append hprefix tailTrace_1836574
  have hstable : (prefixWord ++ tailWord_1836574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836574).length < 2 ^ (prefixWord ++ tailWord_1836574).sum := by decide
  have hdescent : baseEnd_1836574 < baseStart_1836574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836575 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7]
def baseStart_1836575 : Nat := 118140960795 + 1836575 * 2 ^ 59
def prefixEnd_1836575 : Nat := 4983230072969 + 3 ^ 40 * 1836575 * 2
def baseEnd_1836575 : Nat := 943045733031257125566251

theorem tailTrace_1836575 : CollatzResearch.WordTrace tailWord_1836575 prefixEnd_1836575 943045733031257125566251 := by
  unfold tailWord_1836575
  simp only [CollatzResearch.WordTrace]
  refine ⟨66985393321409911883199179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44656928880939941255466119 66985393321409911883199179)
  ·
    refine ⟨100478089982114867824798769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66985393321409911883199179 100478089982114867824798769)
    ·
      refine ⟨75358567486586150868599077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100478089982114867824798769 75358567486586150868599077)
      ·
        refine ⟨14129731403734903287862327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75358567486586150868599077 14129731403734903287862327)
        ·
          refine ⟨21194597105602354931793491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14129731403734903287862327 21194597105602354931793491)
          ·
            refine ⟨31791895658403532397690237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21194597105602354931793491 31791895658403532397690237)
            ·
              refine ⟨11921960871901324649133839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31791895658403532397690237 11921960871901324649133839)
              ·
                refine ⟨17882941307851986973700759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11921960871901324649133839 17882941307851986973700759)
                ·
                  refine ⟨26824411961777980460551139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17882941307851986973700759 26824411961777980460551139)
                  ·
                    refine ⟨40236617942666970690826709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26824411961777980460551139 40236617942666970690826709)
                    ·
                      refine ⟨943045733031257125566251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40236617942666970690826709 943045733031257125566251)
                      ·
                        rfl

theorem cell23_1836575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_1836575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836575 prefixEnd_1836575 := by exact prefixLift 1836575
  have htrace : WordTrace (prefixWord ++ tailWord_1836575) baseStart_1836575 baseEnd_1836575 := by
    simpa [prefixWord, tailWord_1836575, baseEnd_1836575] using wordTrace_append hprefix tailTrace_1836575
  have hstable : (prefixWord ++ tailWord_1836575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836575).length < 2 ^ (prefixWord ++ tailWord_1836575).sum := by decide
  have hdescent : baseEnd_1836575 < baseStart_1836575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836622 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1836622 : Nat := 118140960795 + 1836622 * 2 ^ 59
def prefixEnd_1836622 : Nat := 4983230072969 + 3 ^ 40 * 1836622 * 2
def baseEnd_1836622 : Nat := 943069866622018441678535

theorem tailTrace_1836622 : CollatzResearch.WordTrace tailWord_1836622 prefixEnd_1836622 943069866622018441678535 := by
  unfold tailWord_1836622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373388444029954863770015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44658071701493092606773413 8373388444029954863770015)
  ·
    refine ⟨12560082666044932295655023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8373388444029954863770015 12560082666044932295655023)
    ·
      refine ⟨18840123999067398443482535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560082666044932295655023 18840123999067398443482535)
      ·
        refine ⟨28260185998601097665223803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18840123999067398443482535 28260185998601097665223803)
        ·
          refine ⟨42390278997901646497835705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28260185998601097665223803 42390278997901646497835705)
          ·
            refine ⟨31792709248426234873376779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42390278997901646497835705 31792709248426234873376779)
            ·
              refine ⟨47689063872639352310065169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31792709248426234873376779 47689063872639352310065169)
              ·
                refine ⟨35766797904479514232548877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47689063872639352310065169 35766797904479514232548877)
                ·
                  refine ⟨13412549214179817837205829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35766797904479514232548877 13412549214179817837205829)
                  ·
                    refine ⟨2514852977658715844476093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13412549214179817837205829 2514852977658715844476093)
                    ·
                      refine ⟨943069866622018441678535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2514852977658715844476093 943069866622018441678535)
                      ·
                        rfl

theorem cell23_1836622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1836622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836622 prefixEnd_1836622 := by exact prefixLift 1836622
  have htrace : WordTrace (prefixWord ++ tailWord_1836622) baseStart_1836622 baseEnd_1836622 := by
    simpa [prefixWord, tailWord_1836622, baseEnd_1836622] using wordTrace_append hprefix tailTrace_1836622
  have hstable : (prefixWord ++ tailWord_1836622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836622).length < 2 ^ (prefixWord ++ tailWord_1836622).sum := by decide
  have hdescent : baseEnd_1836622 < baseStart_1836622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836636 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_1836636 : Nat := 118140960795 + 1836636 * 2 ^ 59
def prefixEnd_1836636 : Nat := 4983230072969 + 3 ^ 40 * 1836636 * 2
def baseEnd_1836636 : Nat := 943077055351181386903471

theorem tailTrace_1836636 : CollatzResearch.WordTrace tailWord_1836636 prefixEnd_1836636 943077055351181386903471 := by
  unfold tailWord_1836636
  simp only [CollatzResearch.WordTrace]
  refine ⟨33493809087094459650584881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44658412116125946200779841 33493809087094459650584881)
  ·
    refine ⟨25120356815320844737938661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33493809087094459650584881 25120356815320844737938661)
    ·
      refine ⟨4710066902872658388363499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25120356815320844737938661 4710066902872658388363499)
      ·
        refine ⟨7065100354308987582545249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710066902872658388363499 7065100354308987582545249)
        ·
          refine ⟨5298825265731740686908937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7065100354308987582545249 5298825265731740686908937)
          ·
            refine ⟨3974118949298805515181703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298825265731740686908937 3974118949298805515181703)
            ·
              refine ⟨5961178423948208272772555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974118949298805515181703 5961178423948208272772555)
              ·
                refine ⟨8941767635922312409158833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5961178423948208272772555 8941767635922312409158833)
                ·
                  refine ⟨6706325726941734306869125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8941767635922312409158833 6706325726941734306869125)
                  ·
                    refine ⟨1257436073801575182537961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6706325726941734306869125 1257436073801575182537961)
                    ·
                      refine ⟨943077055351181386903471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257436073801575182537961 943077055351181386903471)
                      ·
                        rfl

theorem cell23_1836636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_1836636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836636 prefixEnd_1836636 := by exact prefixLift 1836636
  have htrace : WordTrace (prefixWord ++ tailWord_1836636) baseStart_1836636 baseEnd_1836636 := by
    simpa [prefixWord, tailWord_1836636, baseEnd_1836636] using wordTrace_append hprefix tailTrace_1836636
  have hstable : (prefixWord ++ tailWord_1836636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836636).length < 2 ^ (prefixWord ++ tailWord_1836636).sum := by decide
  have hdescent : baseEnd_1836636 < baseStart_1836636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836653 : List Nat := [1, 5, 1, 1, 5, 1, 1, 1, 2, 1, 4]
def baseStart_1836653 : Nat := 118140960795 + 1836653 * 2 ^ 59
def prefixEnd_1836653 : Nat := 4983230072969 + 3 ^ 40 * 1836653 * 2
def baseEnd_1836653 : Nat := 943085784522307820390893

theorem tailTrace_1836653 : CollatzResearch.WordTrace tailWord_1836653 prefixEnd_1836653 943085784522307820390893 := by
  unfold tailWord_1836653
  simp only [CollatzResearch.WordTrace]
  refine ⟨66988238215127331204538613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44658825476751554136359075 66988238215127331204538613)
  ·
    refine ⟨6280147332668187300425495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66988238215127331204538613 6280147332668187300425495)
    ·
      refine ⟨9420220999002280950638243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6280147332668187300425495 9420220999002280950638243)
      ·
        refine ⟨14130331498503421425957365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420220999002280950638243 14130331498503421425957365)
        ·
          refine ⟨1324718577984695758683503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14130331498503421425957365 1324718577984695758683503)
          ·
            refine ⟨1987077866977043638025255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324718577984695758683503 1987077866977043638025255)
            ·
              refine ⟨2980616800465565457037883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987077866977043638025255 2980616800465565457037883)
              ·
                refine ⟨4470925200698348185556825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980616800465565457037883 4470925200698348185556825)
                ·
                  refine ⟨3353193900523761139167619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470925200698348185556825 3353193900523761139167619)
                  ·
                    refine ⟨5029790850785641708751429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353193900523761139167619 5029790850785641708751429)
                    ·
                      refine ⟨943085784522307820390893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5029790850785641708751429 943085784522307820390893)
                      ·
                        rfl

theorem cell23_1836653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 1, 2, 1, 4].length) (baseStart_1836653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836653 prefixEnd_1836653 := by exact prefixLift 1836653
  have htrace : WordTrace (prefixWord ++ tailWord_1836653) baseStart_1836653 baseEnd_1836653 := by
    simpa [prefixWord, tailWord_1836653, baseEnd_1836653] using wordTrace_append hprefix tailTrace_1836653
  have hstable : (prefixWord ++ tailWord_1836653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836653).length < 2 ^ (prefixWord ++ tailWord_1836653).sum := by decide
  have hdescent : baseEnd_1836653 < baseStart_1836653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836656 : List Nat := [2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3]
def baseStart_1836656 : Nat := 118140960795 + 1836656 * 2 ^ 59
def prefixEnd_1836656 : Nat := 4983230072969 + 3 ^ 40 * 1836656 * 2
def baseEnd_1836656 : Nat := 943087324964271308653379

theorem tailTrace_1836656 : CollatzResearch.WordTrace tailWord_1836656 prefixEnd_1836656 943087324964271308653379 := by
  unfold tailWord_1836656
  simp only [CollatzResearch.WordTrace]
  refine ⟨33494173817058231358448911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44658898422744308477931881 33494173817058231358448911)
  ·
    refine ⟨50241260725587347037673367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33494173817058231358448911 50241260725587347037673367)
    ·
      refine ⟨75361891088381020556510051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50241260725587347037673367 75361891088381020556510051)
      ·
        refine ⟨113042836632571530834765077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75361891088381020556510051 113042836632571530834765077)
        ·
          refine ⟨5298882967151790507879613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113042836632571530834765077 5298882967151790507879613)
          ·
            refine ⟨1987081112681921440454855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5298882967151790507879613 1987081112681921440454855)
            ·
              refine ⟨2980621669022882160682283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987081112681921440454855 2980621669022882160682283)
              ·
                refine ⟨4470932503534323241023425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2980621669022882160682283 4470932503534323241023425)
                ·
                  refine ⟨3353199377650742430767569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4470932503534323241023425 3353199377650742430767569)
                  ·
                    refine ⟨2514899533238056823075677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3353199377650742430767569 2514899533238056823075677)
                    ·
                      refine ⟨943087324964271308653379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2514899533238056823075677 943087324964271308653379)
                      ·
                        rfl

theorem cell23_1836656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 1, 2, 2, 3].length) (baseStart_1836656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836656 prefixEnd_1836656 := by exact prefixLift 1836656
  have htrace : WordTrace (prefixWord ++ tailWord_1836656) baseStart_1836656 baseEnd_1836656 := by
    simpa [prefixWord, tailWord_1836656, baseEnd_1836656] using wordTrace_append hprefix tailTrace_1836656
  have hstable : (prefixWord ++ tailWord_1836656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836656).length < 2 ^ (prefixWord ++ tailWord_1836656).sum := by decide
  have hdescent : baseEnd_1836656 < baseStart_1836656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836676 : List Nat := [2, 3, 2, 1, 4, 2, 1, 2, 6]
def baseStart_1836676 : Nat := 118140960795 + 1836676 * 2 ^ 59
def prefixEnd_1836676 : Nat := 4983230072969 + 3 ^ 40 * 1836676 * 2
def baseEnd_1836676 : Nat := 104788621619706803378143

theorem tailTrace_1836676 : CollatzResearch.WordTrace tailWord_1836676 prefixEnd_1836676 104788621619706803378143 := by
  unfold tailWord_1836676
  simp only [CollatzResearch.WordTrace]
  refine ⟨33494538547022003066312941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44659384729362670755083921 33494538547022003066312941)
  ·
    refine ⟨12560451955133251149867353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33494538547022003066312941 12560451955133251149867353)
    ·
      refine ⟨9420338966349938362400515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12560451955133251149867353 9420338966349938362400515)
      ·
        refine ⟨14130508449524907543600773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420338966349938362400515 14130508449524907543600773)
        ·
          refine ⟨2649470334285920164425145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14130508449524907543600773 2649470334285920164425145)
          ·
            refine ⟨1987102750714440123318859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2649470334285920164425145 1987102750714440123318859)
            ·
              refine ⟨2980654126071660184978289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987102750714440123318859 2980654126071660184978289)
              ·
                refine ⟨2235490594553745138733717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980654126071660184978289 2235490594553745138733717)
                ·
                  refine ⟨104788621619706803378143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2235490594553745138733717 104788621619706803378143)
                  ·
                    rfl

theorem cell23_1836676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_1836676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836676 prefixEnd_1836676 := by exact prefixLift 1836676
  have htrace : WordTrace (prefixWord ++ tailWord_1836676) baseStart_1836676 baseEnd_1836676 := by
    simpa [prefixWord, tailWord_1836676, baseEnd_1836676] using wordTrace_append hprefix tailTrace_1836676
  have hstable : (prefixWord ++ tailWord_1836676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836676).length < 2 ^ (prefixWord ++ tailWord_1836676).sum := by decide
  have hdescent : baseEnd_1836676 < baseStart_1836676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836686 : List Nat := [4, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1836686 : Nat := 118140960795 + 1836686 * 2 ^ 59
def prefixEnd_1836686 : Nat := 4983230072969 + 3 ^ 40 * 1836686 * 2
def baseEnd_1836686 : Nat := 943102729383906191278241

theorem tailTrace_1836686 : CollatzResearch.WordTrace tailWord_1836686 prefixEnd_1836686 943102729383906191278241 := by
  unfold tailWord_1836686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373680228000972230061239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44659627882671851893659941 8373680228000972230061239)
  ·
    refine ⟨12560520342001458345091859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8373680228000972230061239 12560520342001458345091859)
    ·
      refine ⟨18840780513002187517637789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12560520342001458345091859 18840780513002187517637789)
      ·
        refine ⟨7065292692375820319114171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18840780513002187517637789 7065292692375820319114171)
        ·
          refine ⟨10597939038563730478671257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065292692375820319114171 10597939038563730478671257)
          ·
            refine ⟨7948454278922797859003443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10597939038563730478671257 7948454278922797859003443)
            ·
              refine ⟨11922681418384196788505165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7948454278922797859003443 11922681418384196788505165)
              ·
                refine ⟨4471005531894073795689437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11922681418384196788505165 4471005531894073795689437)
                ·
                  refine ⟨1676627074460277673383539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4471005531894073795689437 1676627074460277673383539)
                  ·
                    refine ⟨2514940611690416510075309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676627074460277673383539 2514940611690416510075309)
                    ·
                      refine ⟨943102729383906191278241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2514940611690416510075309 943102729383906191278241)
                      ·
                        rfl

theorem cell23_1836686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1836686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836686 prefixEnd_1836686 := by exact prefixLift 1836686
  have htrace : WordTrace (prefixWord ++ tailWord_1836686) baseStart_1836686 baseEnd_1836686 := by
    simpa [prefixWord, tailWord_1836686, baseEnd_1836686] using wordTrace_append hprefix tailTrace_1836686
  have hstable : (prefixWord ++ tailWord_1836686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836686).length < 2 ^ (prefixWord ++ tailWord_1836686).sum := by decide
  have hdescent : baseEnd_1836686 < baseStart_1836686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836709 : List Nat := [1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 4]
def baseStart_1836709 : Nat := 118140960795 + 1836709 * 2 ^ 59
def prefixEnd_1836709 : Nat := 4983230072969 + 3 ^ 40 * 1836709 * 2
def baseEnd_1836709 : Nat := 943114539438959601290635

theorem tailTrace_1836709 : CollatzResearch.WordTrace tailWord_1836709 prefixEnd_1836709 943114539438959601290635 := by
  unfold tailWord_1836709
  simp only [CollatzResearch.WordTrace]
  refine ⟨66990280702924452768577181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44660187135282968512384787 66990280702924452768577181)
  ·
    refine ⟨25121355263596669788216443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66990280702924452768577181 25121355263596669788216443)
    ·
      refine ⟨37682032895395004682324665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25121355263596669788216443 37682032895395004682324665)
      ·
        refine ⟨28261524671546253511743499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37682032895395004682324665 28261524671546253511743499)
        ·
          refine ⟨42392287007319380267615249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28261524671546253511743499 42392287007319380267615249)
          ·
            refine ⟨31794215255489535200711437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42392287007319380267615249 31794215255489535200711437)
            ·
              refine ⟨11922830720808575700266789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31794215255489535200711437 11922830720808575700266789)
              ·
                refine ⟨2235530760151607943800023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11922830720808575700266789 2235530760151607943800023)
                ·
                  refine ⟨3353296140227411915700035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235530760151607943800023 3353296140227411915700035)
                  ·
                    refine ⟨5029944210341117873550053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3353296140227411915700035 5029944210341117873550053)
                    ·
                      refine ⟨943114539438959601290635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5029944210341117873550053 943114539438959601290635)
                      ·
                        rfl

theorem cell23_1836709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_1836709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836709 prefixEnd_1836709 := by exact prefixLift 1836709
  have htrace : WordTrace (prefixWord ++ tailWord_1836709) baseStart_1836709 baseEnd_1836709 := by
    simpa [prefixWord, tailWord_1836709, baseEnd_1836709] using wordTrace_append hprefix tailTrace_1836709
  have hstable : (prefixWord ++ tailWord_1836709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836709).length < 2 ^ (prefixWord ++ tailWord_1836709).sum := by decide
  have hdescent : baseEnd_1836709 < baseStart_1836709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836732 : List Nat := [2, 2, 2, 3, 1, 2, 11]
def baseStart_1836732 : Nat := 118140960795 + 1836732 * 2 ^ 59
def prefixEnd_1836732 : Nat := 4983230072969 + 3 ^ 40 * 1836732 * 2
def baseEnd_1836732 : Nat := 11643535178938432238309

theorem tailTrace_1836732 : CollatzResearch.WordTrace tailWord_1836732 prefixEnd_1836732 11643535178938432238309 := by
  unfold tailWord_1836732
  simp only [CollatzResearch.WordTrace]
  refine ⟨33495559790920563848332225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44660746387894085131109633 33495559790920563848332225)
  ·
    refine ⟨25121669843190422886249169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33495559790920563848332225 25121669843190422886249169)
    ·
      refine ⟨18841252382392817164686877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25121669843190422886249169 18841252382392817164686877)
      ·
        refine ⟨7065469643397306436757579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18841252382392817164686877 7065469643397306436757579)
        ·
          refine ⟨10598204465095959655136369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7065469643397306436757579 10598204465095959655136369)
          ·
            refine ⟨7948653348821969741352277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10598204465095959655136369 7948653348821969741352277)
            ·
              refine ⟨11643535178938432238309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7948653348821969741352277 11643535178938432238309)
              ·
                rfl

theorem cell23_1836732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 11].length) (baseStart_1836732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836732 prefixEnd_1836732 := by exact prefixLift 1836732
  have htrace : WordTrace (prefixWord ++ tailWord_1836732) baseStart_1836732 baseEnd_1836732 := by
    simpa [prefixWord, tailWord_1836732, baseEnd_1836732] using wordTrace_append hprefix tailTrace_1836732
  have hstable : (prefixWord ++ tailWord_1836732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836732).length < 2 ^ (prefixWord ++ tailWord_1836732).sum := by decide
  have hdescent : baseEnd_1836732 < baseStart_1836732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836753 : List Nat := [1, 2, 2, 1, 2, 6, 2, 1, 2, 4]
def baseStart_1836753 : Nat := 118140960795 + 1836753 * 2 ^ 59
def prefixEnd_1836753 : Nat := 4983230072969 + 3 ^ 40 * 1836753 * 2
def baseEnd_1836753 : Nat := 314379044195919143046811

theorem tailTrace_1836753 : CollatzResearch.WordTrace tailWord_1836753 prefixEnd_1836753 314379044195919143046811 := by
  unfold tailWord_1836753
  simp only [CollatzResearch.WordTrace]
  refine ⟨66991885514765048283178913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44661257009843365522119275 66991885514765048283178913)
  ·
    refine ⟨50243914136073786212384185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66991885514765048283178913 50243914136073786212384185)
    ·
      refine ⟨37682935602055339659288139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50243914136073786212384185 37682935602055339659288139)
      ·
        refine ⟨56524403403083009488932209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37682935602055339659288139 56524403403083009488932209)
        ·
          refine ⟨42393302552312257116699157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56524403403083009488932209 42393302552312257116699157)
          ·
            refine ⟨1987186057139637052345273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42393302552312257116699157 1987186057139637052345273)
            ·
              refine ⟨1490389542854727789258955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987186057139637052345273 1490389542854727789258955)
              ·
                refine ⟨2235584314282091683888433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1490389542854727789258955 2235584314282091683888433)
                ·
                  refine ⟨1676688235711568762916325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235584314282091683888433 1676688235711568762916325)
                  ·
                    refine ⟨314379044195919143046811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676688235711568762916325 314379044195919143046811)
                    ·
                      rfl

theorem cell23_1836753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_1836753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836753 prefixEnd_1836753 := by exact prefixLift 1836753
  have htrace : WordTrace (prefixWord ++ tailWord_1836753) baseStart_1836753 baseEnd_1836753 := by
    simpa [prefixWord, tailWord_1836753, baseEnd_1836753] using wordTrace_append hprefix tailTrace_1836753
  have hstable : (prefixWord ++ tailWord_1836753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836753).length < 2 ^ (prefixWord ++ tailWord_1836753).sum := by decide
  have hdescent : baseEnd_1836753 < baseStart_1836753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836759 : List Nat := [1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 3]
def baseStart_1836759 : Nat := 118140960795 + 1836759 * 2 ^ 59
def prefixEnd_1836759 : Nat := 4983230072969 + 3 ^ 40 * 1836759 * 2
def baseEnd_1836759 : Nat := 943140213471684405665405

theorem tailTrace_1836759 : CollatzResearch.WordTrace tailWord_1836759 prefixEnd_1836759 943140213471684405665405 := by
  unfold tailWord_1836759
  simp only [CollatzResearch.WordTrace]
  refine ⟨66992104352743311307897331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44661402901828874205264887 66992104352743311307897331)
  ·
    refine ⟨100488156529114966961845997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66992104352743311307897331 100488156529114966961845997)
    ·
      refine ⟨37683058698418112610692249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100488156529114966961845997 37683058698418112610692249)
      ·
        refine ⟨28262294023813584458019187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37683058698418112610692249 28262294023813584458019187)
        ·
          refine ⟨42393441035720376687028781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28262294023813584458019187 42393441035720376687028781)
          ·
            refine ⟨15897540388395141257635793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42393441035720376687028781 15897540388395141257635793)
            ·
              refine ⟨11923155291296355943226845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15897540388395141257635793 11923155291296355943226845)
              ·
                refine ⟨4471183234236133478710067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11923155291296355943226845 4471183234236133478710067)
                ·
                  refine ⟨6706774851354200218065101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471183234236133478710067 6706774851354200218065101)
                  ·
                    refine ⟨2515040569257825081774413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6706774851354200218065101 2515040569257825081774413)
                    ·
                      refine ⟨943140213471684405665405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2515040569257825081774413 943140213471684405665405)
                      ·
                        rfl

theorem cell23_1836759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 3].length) (baseStart_1836759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836759 prefixEnd_1836759 := by exact prefixLift 1836759
  have htrace : WordTrace (prefixWord ++ tailWord_1836759) baseStart_1836759 baseEnd_1836759 := by
    simpa [prefixWord, tailWord_1836759, baseEnd_1836759] using wordTrace_append hprefix tailTrace_1836759
  have hstable : (prefixWord ++ tailWord_1836759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836759).length < 2 ^ (prefixWord ++ tailWord_1836759).sum := by decide
  have hdescent : baseEnd_1836759 < baseStart_1836759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836776 : List Nat := [2, 1, 4, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1836776 : Nat := 118140960795 + 1836776 * 2 ^ 59
def prefixEnd_1836776 : Nat := 4983230072969 + 3 ^ 40 * 1836776 * 2
def baseEnd_1836776 : Nat := 943148942642810839152827

theorem tailTrace_1836776 : CollatzResearch.WordTrace tailWord_1836776 prefixEnd_1836776 943148942642810839152827 := by
  unfold tailWord_1836776
  simp only [CollatzResearch.WordTrace]
  refine ⟨33496362196840861605633091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44661816262454482140844121 33496362196840861605633091)
  ·
    refine ⟨50244543295261292408449637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33496362196840861605633091 50244543295261292408449637)
    ·
      refine ⟨9420851867861492326584307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50244543295261292408449637 9420851867861492326584307)
      ·
        refine ⟨14131277801792238489876461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9420851867861492326584307 14131277801792238489876461)
        ·
          refine ⟨5299229175672089433703673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14131277801792238489876461 5299229175672089433703673)
          ·
            refine ⟨3974421881754067075277755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5299229175672089433703673 3974421881754067075277755)
            ·
              refine ⟨5961632822631100612916633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974421881754067075277755 5961632822631100612916633)
              ·
                refine ⟨4471224616973325459687475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5961632822631100612916633 4471224616973325459687475)
                ·
                  refine ⟨6706836925459988189531213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471224616973325459687475 6706836925459988189531213)
                  ·
                    refine ⟨2515063847047495571074205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6706836925459988189531213 2515063847047495571074205)
                    ·
                      refine ⟨943148942642810839152827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2515063847047495571074205 943148942642810839152827)
                      ·
                        rfl

theorem cell23_1836776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1836776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836776 prefixEnd_1836776 := by exact prefixLift 1836776
  have htrace : WordTrace (prefixWord ++ tailWord_1836776) baseStart_1836776 baseEnd_1836776 := by
    simpa [prefixWord, tailWord_1836776, baseEnd_1836776] using wordTrace_append hprefix tailTrace_1836776
  have hstable : (prefixWord ++ tailWord_1836776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836776).length < 2 ^ (prefixWord ++ tailWord_1836776).sum := by decide
  have hdescent : baseEnd_1836776 < baseStart_1836776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836850 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2]
def baseStart_1836850 : Nat := 118140960795 + 1836850 * 2 ^ 59
def prefixEnd_1836850 : Nat := 4983230072969 + 3 ^ 40 * 1836850 * 2
def baseEnd_1836850 : Nat := 943186940211243549627487

theorem tailTrace_1836850 : CollatzResearch.WordTrace tailWord_1836850 prefixEnd_1836850 943186940211243549627487 := by
  unfold tailWord_1836850
  simp only [CollatzResearch.WordTrace]
  refine ⟨16748855848853408462365001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44663615596942422566306669 16748855848853408462365001)
  ·
    refine ⟨12561641886640056346773751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16748855848853408462365001 12561641886640056346773751)
    ·
      refine ⟨18842462829960084520160627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12561641886640056346773751 18842462829960084520160627)
      ·
        refine ⟨28263694244940126780240941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18842462829960084520160627 28263694244940126780240941)
        ·
          refine ⟨10598885341852547542590353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28263694244940126780240941 10598885341852547542590353)
          ·
            refine ⟨7949164006389410656942765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10598885341852547542590353 7949164006389410656942765)
            ·
              refine ⟨2980936502396028996353537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7949164006389410656942765 2980936502396028996353537)
              ·
                refine ⟨2235702376797021747265153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980936502396028996353537 2235702376797021747265153)
                ·
                  refine ⟨1676776782597766310448865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235702376797021747265153 1676776782597766310448865)
                  ·
                    refine ⟨1257582586948324732836649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1676776782597766310448865 1257582586948324732836649)
                    ·
                      refine ⟨943186940211243549627487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257582586948324732836649 943186940211243549627487)
                      ·
                        rfl

theorem cell23_1836850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2].length) (baseStart_1836850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836850 prefixEnd_1836850 := by exact prefixLift 1836850
  have htrace : WordTrace (prefixWord ++ tailWord_1836850) baseStart_1836850 baseEnd_1836850 := by
    simpa [prefixWord, tailWord_1836850, baseEnd_1836850] using wordTrace_append hprefix tailTrace_1836850
  have hstable : (prefixWord ++ tailWord_1836850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836850).length < 2 ^ (prefixWord ++ tailWord_1836850).sum := by decide
  have hdescent : baseEnd_1836850 < baseStart_1836850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836856 : List Nat := [2, 1, 2, 1, 3, 3, 2, 4, 5]
def baseStart_1836856 : Nat := 118140960795 + 1836856 * 2 ^ 59
def prefixEnd_1836856 : Nat := 4983230072969 + 3 ^ 40 * 1836856 * 2
def baseEnd_1836856 : Nat := 104798891232796725128051

theorem tailTrace_1836856 : CollatzResearch.WordTrace tailWord_1836856 prefixEnd_1836856 104798891232796725128051 := by
  unfold tailWord_1836856
  simp only [CollatzResearch.WordTrace]
  refine ⟨33497821116695948437089211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44663761488927931249452281 33497821116695948437089211)
  ·
    refine ⟨50246731675043922655633817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33497821116695948437089211 50246731675043922655633817)
    ·
      refine ⟨37685048756282941991725363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50246731675043922655633817 37685048756282941991725363)
      ·
        refine ⟨56527573134424412987588045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37685048756282941991725363 56527573134424412987588045)
        ·
          refine ⟨21197839925409154870345517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56527573134424412987588045 21197839925409154870345517)
          ·
            refine ⟨7949189972028433076379569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21197839925409154870345517 7949189972028433076379569)
            ·
              refine ⟨5961892479021324807284677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7949189972028433076379569 5961892479021324807284677)
              ·
                refine ⟨1117854839816498401365877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5961892479021324807284677 1117854839816498401365877)
                ·
                  refine ⟨104798891232796725128051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1117854839816498401365877 104798891232796725128051)
                  ·
                    rfl

theorem cell23_1836856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 5].length) (baseStart_1836856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836856 prefixEnd_1836856 := by exact prefixLift 1836856
  have htrace : WordTrace (prefixWord ++ tailWord_1836856) baseStart_1836856 baseEnd_1836856 := by
    simpa [prefixWord, tailWord_1836856, baseEnd_1836856] using wordTrace_append hprefix tailTrace_1836856
  have hstable : (prefixWord ++ tailWord_1836856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836856).length < 2 ^ (prefixWord ++ tailWord_1836856).sum := by decide
  have hdescent : baseEnd_1836856 < baseStart_1836856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836889 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 4]
def baseStart_1836889 : Nat := 118140960795 + 1836889 * 2 ^ 59
def prefixEnd_1836889 : Nat := 4983230072969 + 3 ^ 40 * 1836889 * 2
def baseEnd_1836889 : Nat := 943206965956768897039807

theorem tailTrace_1836889 : CollatzResearch.WordTrace tailWord_1836889 prefixEnd_1836889 943206965956768897039807 := by
  unfold tailWord_1836889
  simp only [CollatzResearch.WordTrace]
  refine ⟨66996845842272343510129721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44664563894848229006753147 66996845842272343510129721)
  ·
    refine ⟨50247634381704257632597291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66996845842272343510129721 50247634381704257632597291)
    ·
      refine ⟨75371451572556386448895937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50247634381704257632597291 75371451572556386448895937)
      ·
        refine ⟨56528588679417289836671953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75371451572556386448895937 56528588679417289836671953)
        ·
          refine ⟨42396441509562967377503965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56528588679417289836671953 42396441509562967377503965)
          ·
            refine ⟨15898665566086112766563987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42396441509562967377503965 15898665566086112766563987)
            ·
              refine ⟨23847998349129169149845981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15898665566086112766563987 23847998349129169149845981)
              ·
                refine ⟨8942999380923438431192243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23847998349129169149845981 8942999380923438431192243)
                ·
                  refine ⟨13414499071385157646788365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8942999380923438431192243 13414499071385157646788365)
                  ·
                    refine ⟨5030437151769434117545637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13414499071385157646788365 5030437151769434117545637)
                    ·
                      refine ⟨943206965956768897039807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5030437151769434117545637 943206965956768897039807)
                      ·
                        rfl

theorem cell23_1836889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 1, 3, 4].length) (baseStart_1836889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836889 prefixEnd_1836889 := by exact prefixLift 1836889
  have htrace : WordTrace (prefixWord ++ tailWord_1836889) baseStart_1836889 baseEnd_1836889 := by
    simpa [prefixWord, tailWord_1836889, baseEnd_1836889] using wordTrace_append hprefix tailTrace_1836889
  have hstable : (prefixWord ++ tailWord_1836889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836889).length < 2 ^ (prefixWord ++ tailWord_1836889).sum := by decide
  have hdescent : baseEnd_1836889 < baseStart_1836889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836967 : List Nat := [1, 1, 6, 1, 2, 1, 4, 2, 1, 4]
def baseStart_1836967 : Nat := 118140960795 + 1836967 * 2 ^ 59
def prefixEnd_1836967 : Nat := 4983230072969 + 3 ^ 40 * 1836967 * 2
def baseEnd_1836967 : Nat := 314415672482606530621483

theorem tailTrace_1836967 : CollatzResearch.WordTrace tailWord_1836967 prefixEnd_1836967 314415672482606530621483 := by
  unfold tailWord_1836967
  simp only [CollatzResearch.WordTrace]
  refine ⟨66999690735989762831469155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44666460490659841887646103 66999690735989762831469155)
  ·
    refine ⟨100499536103984644247203733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66999690735989762831469155 100499536103984644247203733)
    ·
      refine ⟨4710915754874280199087675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100499536103984644247203733 4710915754874280199087675)
      ·
        refine ⟨7066373632311420298631513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4710915754874280199087675 7066373632311420298631513)
        ·
          refine ⟨5299780224233565223973635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7066373632311420298631513 5299780224233565223973635)
          ·
            refine ⟨7949670336350347835960453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299780224233565223973635 7949670336350347835960453)
            ·
              refine ⟨1490563188065690219242585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7949670336350347835960453 1490563188065690219242585)
              ·
                refine ⟨1117922391049267664431939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490563188065690219242585 1117922391049267664431939)
                ·
                  refine ⟨1676883586573901496647909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1117922391049267664431939 1676883586573901496647909)
                  ·
                    refine ⟨314415672482606530621483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676883586573901496647909 314415672482606530621483)
                    ·
                      rfl

theorem cell23_1836967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_1836967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836967 prefixEnd_1836967 := by exact prefixLift 1836967
  have htrace : WordTrace (prefixWord ++ tailWord_1836967) baseStart_1836967 baseEnd_1836967 := by
    simpa [prefixWord, tailWord_1836967, baseEnd_1836967] using wordTrace_append hprefix tailTrace_1836967
  have hstable : (prefixWord ++ tailWord_1836967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836967).length < 2 ^ (prefixWord ++ tailWord_1836967).sum := by decide
  have hdescent : baseEnd_1836967 < baseStart_1836967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836974 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2]
def baseStart_1836974 : Nat := 118140960795 + 1836974 * 2 ^ 59
def prefixEnd_1836974 : Nat := 4983230072969 + 3 ^ 40 * 1836974 * 2
def baseEnd_1836974 : Nat := 943250611812401064476917

theorem tailTrace_1836974 : CollatzResearch.WordTrace tailWord_1836974 prefixEnd_1836974 943250611812401064476917 := by
  unfold tailWord_1836974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374993255870550378371747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44666630697976268684649317 8374993255870550378371747)
  ·
    refine ⟨12562489883805825567557621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374993255870550378371747 12562489883805825567557621)
    ·
      refine ⟨1177733426606796146958527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12562489883805825567557621 1177733426606796146958527)
      ·
        refine ⟨1766600139910194220437791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177733426606796146958527 1766600139910194220437791)
        ·
          refine ⟨2649900209865291330656687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766600139910194220437791 2649900209865291330656687)
          ·
            refine ⟨3974850314797936995985031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649900209865291330656687 3974850314797936995985031)
            ·
              refine ⟨5962275472196905493977547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974850314797936995985031 5962275472196905493977547)
              ·
                refine ⟨8943413208295358240966321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962275472196905493977547 8943413208295358240966321)
                ·
                  refine ⟨6707559906221518680724741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8943413208295358240966321 6707559906221518680724741)
                  ·
                    refine ⟨1257667482416534752635889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6707559906221518680724741 1257667482416534752635889)
                    ·
                      refine ⟨943250611812401064476917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257667482416534752635889 943250611812401064476917)
                      ·
                        rfl

theorem cell23_1836974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_1836974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836974 prefixEnd_1836974 := by exact prefixLift 1836974
  have htrace : WordTrace (prefixWord ++ tailWord_1836974) baseStart_1836974 baseEnd_1836974 := by
    simpa [prefixWord, tailWord_1836974, baseEnd_1836974] using wordTrace_append hprefix tailTrace_1836974
  have hstable : (prefixWord ++ tailWord_1836974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836974).length < 2 ^ (prefixWord ++ tailWord_1836974).sum := by decide
  have hdescent : baseEnd_1836974 < baseStart_1836974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1836990 : List Nat := [4, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1836990 : Nat := 118140960795 + 1836990 * 2 ^ 59
def prefixEnd_1836990 : Nat := 4983230072969 + 3 ^ 40 * 1836990 * 2
def baseEnd_1836990 : Nat := 943258827502873001876843

theorem tailTrace_1836990 : CollatzResearch.WordTrace tailWord_1836990 prefixEnd_1836990 943258827502873001876843 := by
  unfold tailWord_1836990
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375066201863304719944553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44667019743270958506370949 8375066201863304719944553)
  ·
    refine ⟨6281299651397478539958415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8375066201863304719944553 6281299651397478539958415)
    ·
      refine ⟨9421949477096217809937623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6281299651397478539958415 9421949477096217809937623)
      ·
        refine ⟨14132924215644326714906435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9421949477096217809937623 14132924215644326714906435)
        ·
          refine ⟨21199386323466490072359653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14132924215644326714906435 21199386323466490072359653)
          ·
            refine ⟨3974884935649966888567435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21199386323466490072359653 3974884935649966888567435)
            ·
              refine ⟨5962327403474950332851153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974884935649966888567435 5962327403474950332851153)
              ·
                refine ⟨4471745552606212749638365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962327403474950332851153 4471745552606212749638365)
                ·
                  refine ⟨1676904582227329781114387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4471745552606212749638365 1676904582227329781114387)
                  ·
                    refine ⟨2515356873340994671671581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676904582227329781114387 2515356873340994671671581)
                    ·
                      refine ⟨943258827502873001876843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2515356873340994671671581 943258827502873001876843)
                      ·
                        rfl

theorem cell23_1836990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1836990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1836990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1836990 prefixEnd_1836990 := by exact prefixLift 1836990
  have htrace : WordTrace (prefixWord ++ tailWord_1836990) baseStart_1836990 baseEnd_1836990 := by
    simpa [prefixWord, tailWord_1836990, baseEnd_1836990] using wordTrace_append hprefix tailTrace_1836990
  have hstable : (prefixWord ++ tailWord_1836990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1836990).length < 2 ^ (prefixWord ++ tailWord_1836990).sum := by decide
  have hdescent : baseEnd_1836990 < baseStart_1836990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1836990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837000 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 2, 3, 2]
def baseStart_1837000 : Nat := 118140960795 + 1837000 * 2 ^ 59
def prefixEnd_1837000 : Nat := 4983230072969 + 3 ^ 40 * 1837000 * 2
def baseEnd_1837000 : Nat := 943263962309417962751797

theorem tailTrace_1837000 : CollatzResearch.WordTrace tailWord_1837000 prefixEnd_1837000 943263962309417962751797 := by
  unfold tailWord_1837000
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500447172435104733710227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44667262896580139644946969 33500447172435104733710227)
  ·
    refine ⟨50250670758652657100565341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33500447172435104733710227 50250670758652657100565341)
    ·
      refine ⟨18844001534494746412712003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50250670758652657100565341 18844001534494746412712003)
      ·
        refine ⟨28266002301742119619068005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18844001534494746412712003 28266002301742119619068005)
        ·
          refine ⟨5299875431576647428575251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28266002301742119619068005 5299875431576647428575251)
          ·
            refine ⟨7949813147364971142862877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5299875431576647428575251 7949813147364971142862877)
            ·
              refine ⟨2981179930261864178573579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7949813147364971142862877 2981179930261864178573579)
              ·
                refine ⟨4471769895392796267860369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981179930261864178573579 4471769895392796267860369)
                ·
                  refine ⟨3353827421544597200895277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4471769895392796267860369 3353827421544597200895277)
                  ·
                    refine ⟨1257685283079223950335729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353827421544597200895277 1257685283079223950335729)
                    ·
                      refine ⟨943263962309417962751797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257685283079223950335729 943263962309417962751797)
                      ·
                        rfl

theorem cell23_1837000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_1837000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837000 prefixEnd_1837000 := by exact prefixLift 1837000
  have htrace : WordTrace (prefixWord ++ tailWord_1837000) baseStart_1837000 baseEnd_1837000 := by
    simpa [prefixWord, tailWord_1837000, baseEnd_1837000] using wordTrace_append hprefix tailTrace_1837000
  have hstable : (prefixWord ++ tailWord_1837000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837000).length < 2 ^ (prefixWord ++ tailWord_1837000).sum := by decide
  have hdescent : baseEnd_1837000 < baseStart_1837000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837006 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_1837006 : Nat := 118140960795 + 1837006 * 2 ^ 59
def prefixEnd_1837006 : Nat := 4983230072969 + 3 ^ 40 * 1837006 * 2
def baseEnd_1837006 : Nat := 314422347731114979758923

theorem tailTrace_1837006 : CollatzResearch.WordTrace tailWord_1837006 prefixEnd_1837006 314422347731114979758923 := by
  unfold tailWord_1837006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8375139147856059061517359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44667408788565648328092581 8375139147856059061517359)
  ·
    refine ⟨12562708721784088592276039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8375139147856059061517359 12562708721784088592276039)
    ·
      refine ⟨18844063082676132888414059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12562708721784088592276039 18844063082676132888414059)
      ·
        refine ⟨28266094624014199332621089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18844063082676132888414059 28266094624014199332621089)
        ·
          refine ⟨21199570968010649499465817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28266094624014199332621089 21199570968010649499465817)
          ·
            refine ⟨15899678226007987124599363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21199570968010649499465817 15899678226007987124599363)
            ·
              refine ⟨23849517339011980686899045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15899678226007987124599363 23849517339011980686899045)
              ·
                refine ⟨4471784501064746378793571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23849517339011980686899045 4471784501064746378793571)
                ·
                  refine ⟨6707676751597119568190357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471784501064746378793571 6707676751597119568190357)
                  ·
                    refine ⟨314422347731114979758923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6707676751597119568190357 314422347731114979758923)
                    ·
                      rfl

theorem cell23_1837006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_1837006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837006 prefixEnd_1837006 := by exact prefixLift 1837006
  have htrace : WordTrace (prefixWord ++ tailWord_1837006) baseStart_1837006 baseEnd_1837006 := by
    simpa [prefixWord, tailWord_1837006, baseEnd_1837006] using wordTrace_append hprefix tailTrace_1837006
  have hstable : (prefixWord ++ tailWord_1837006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837006).length < 2 ^ (prefixWord ++ tailWord_1837006).sum := by decide
  have hdescent : baseEnd_1837006 < baseStart_1837006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837010 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1837010 : Nat := 118140960795 + 1837010 * 2 ^ 59
def prefixEnd_1837010 : Nat := 4983230072969 + 3 ^ 40 * 1837010 * 2
def baseEnd_1837010 : Nat := 314423032371987641208917

theorem tailTrace_1837010 : CollatzResearch.WordTrace tailWord_1837010 prefixEnd_1837010 314423032371987641208917 := by
  unfold tailWord_1837010
  simp only [CollatzResearch.WordTrace]
  refine ⟨16750314768708495293821121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44667506049889320783522989 16750314768708495293821121)
  ·
    refine ⟨12562736076531371470365841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16750314768708495293821121 12562736076531371470365841)
    ·
      refine ⟨9422052057398528602774381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12562736076531371470365841 9422052057398528602774381)
      ·
        refine ⟨3533269521524448226040393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9422052057398528602774381 3533269521524448226040393)
        ·
          refine ⟨2649952141143336169530295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533269521524448226040393 2649952141143336169530295)
          ·
            refine ⟨3974928211715004254295443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649952141143336169530295 3974928211715004254295443)
            ·
              refine ⟨5962392317572506381443165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974928211715004254295443 5962392317572506381443165)
              ·
                refine ⟨2235897119089689893041187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5962392317572506381443165 2235897119089689893041187)
                ·
                  refine ⟨3353845678634534839561781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2235897119089689893041187 3353845678634534839561781)
                  ·
                    refine ⟨314423032371987641208917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3353845678634534839561781 314423032371987641208917)
                    ·
                      rfl

theorem cell23_1837010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1837010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837010 prefixEnd_1837010 := by exact prefixLift 1837010
  have htrace : WordTrace (prefixWord ++ tailWord_1837010) baseStart_1837010 baseEnd_1837010 := by
    simpa [prefixWord, tailWord_1837010, baseEnd_1837010] using wordTrace_append hprefix tailTrace_1837010
  have hstable : (prefixWord ++ tailWord_1837010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837010).length < 2 ^ (prefixWord ++ tailWord_1837010).sum := by decide
  have hdescent : baseEnd_1837010 < baseStart_1837010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837016 : List Nat := [2, 1, 2, 2, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1837016 : Nat := 118140960795 + 1837016 * 2 ^ 59
def prefixEnd_1837016 : Nat := 4983230072969 + 3 ^ 40 * 1837016 * 2
def baseEnd_1837016 : Nat := 943272177999889900151723

theorem tailTrace_1837016 : CollatzResearch.WordTrace tailWord_1837016 prefixEnd_1837016 943272177999889900151723 := by
  unfold tailWord_1837016
  simp only [CollatzResearch.WordTrace]
  refine ⟨33500738956406122100001451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44667651941874829466668601 33500738956406122100001451)
  ·
    refine ⟨50251108434609183150002177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33500738956406122100001451 50251108434609183150002177)
    ·
      refine ⟨37688331325956887362501633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50251108434609183150002177 37688331325956887362501633)
      ·
        refine ⟨28266248494467665521876225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37688331325956887362501633 28266248494467665521876225)
        ·
          refine ⟨21199686370850749141407169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28266248494467665521876225 21199686370850749141407169)
          ·
            refine ⟨15899764778138061856055377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21199686370850749141407169 15899764778138061856055377)
            ·
              refine ⟨11924823583603546392041533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15899764778138061856055377 11924823583603546392041533)
              ·
                refine ⟨4471808843851329897015575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11924823583603546392041533 4471808843851329897015575)
                ·
                  refine ⟨6707713265776994845523363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4471808843851329897015575 6707713265776994845523363)
                  ·
                    refine ⟨10061569898665492268285045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6707713265776994845523363 10061569898665492268285045)
                    ·
                      refine ⟨943272177999889900151723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10061569898665492268285045 943272177999889900151723)
                      ·
                        rfl

theorem cell23_1837016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1837016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837016 prefixEnd_1837016 := by exact prefixLift 1837016
  have htrace : WordTrace (prefixWord ++ tailWord_1837016) baseStart_1837016 baseEnd_1837016 := by
    simpa [prefixWord, tailWord_1837016, baseEnd_1837016] using wordTrace_append hprefix tailTrace_1837016
  have hstable : (prefixWord ++ tailWord_1837016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837016).length < 2 ^ (prefixWord ++ tailWord_1837016).sum := by decide
  have hdescent : baseEnd_1837016 < baseStart_1837016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837023 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 4, 4]
def baseStart_1837023 : Nat := 118140960795 + 1837023 * 2 ^ 59
def prefixEnd_1837023 : Nat := 4983230072969 + 3 ^ 40 * 1837023 * 2
def baseEnd_1837023 : Nat := 314425257454823790921397

theorem tailTrace_1837023 : CollatzResearch.WordTrace tailWord_1837023 prefixEnd_1837023 314425257454823790921397 := by
  unfold tailWord_1837023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67001733223786884395507723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44667822149191256263671815 67001733223786884395507723)
  ·
    refine ⟨100502599835680326593261585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67001733223786884395507723 100502599835680326593261585)
    ·
      refine ⟨75376949876760244944946189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100502599835680326593261585 75376949876760244944946189)
      ·
        refine ⟨28266356203785091854354821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75376949876760244944946189 28266356203785091854354821)
        ·
          refine ⟨5299941788209704722691529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28266356203785091854354821 5299941788209704722691529)
          ·
            refine ⟨3974956341157278542018647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5299941788209704722691529 3974956341157278542018647)
            ·
              refine ⟨5962434511735917813027971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974956341157278542018647 5962434511735917813027971)
              ·
                refine ⟨8943651767603876719541957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5962434511735917813027971 8943651767603876719541957)
                ·
                  refine ⟨1676934706425726884914117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8943651767603876719541957 1676934706425726884914117)
                  ·
                    refine ⟨314425257454823790921397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676934706425726884914117 314425257454823790921397)
                    ·
                      rfl

theorem cell23_1837023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_1837023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837023 prefixEnd_1837023 := by exact prefixLift 1837023
  have htrace : WordTrace (prefixWord ++ tailWord_1837023) baseStart_1837023 baseEnd_1837023 := by
    simpa [prefixWord, tailWord_1837023, baseEnd_1837023] using wordTrace_append hprefix tailTrace_1837023
  have hstable : (prefixWord ++ tailWord_1837023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837023).length < 2 ^ (prefixWord ++ tailWord_1837023).sum := by decide
  have hdescent : baseEnd_1837023 < baseStart_1837023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837073 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 7, 3, 2]
def baseStart_1837073 : Nat := 118140960795 + 1837073 * 2 ^ 59
def prefixEnd_1837073 : Nat := 4983230072969 + 3 ^ 40 * 1837073 * 2
def baseEnd_1837073 : Nat := 943301446397196177138961

theorem tailTrace_1837073 : CollatzResearch.WordTrace tailWord_1837073 prefixEnd_1837073 943301446397196177138961 := by
  unfold tailWord_1837073
  simp only [CollatzResearch.WordTrace]
  refine ⟨67003556873605742934827873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44669037915737161956551915 67003556873605742934827873)
  ·
    refine ⟨50252667655204307201120905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67003556873605742934827873 50252667655204307201120905)
    ·
      refine ⟨37689500741403230400840679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50252667655204307201120905 37689500741403230400840679)
      ·
        refine ⟨56534251112104845601261019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37689500741403230400840679 56534251112104845601261019)
        ·
          refine ⟨84801376668157268401891529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56534251112104845601261019 84801376668157268401891529)
          ·
            refine ⟨63601032501117951301418647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84801376668157268401891529 63601032501117951301418647)
            ·
              refine ⟨95401548751676926952127971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63601032501117951301418647 95401548751676926952127971)
              ·
                refine ⟨143102323127515390428191957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95401548751676926952127971 143102323127515390428191957)
                ·
                  refine ⟨3353960698301141963160749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 143102323127515390428191957 3353960698301141963160749)
                  ·
                    refine ⟨1257735261862928236185281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353960698301141963160749 1257735261862928236185281)
                    ·
                      refine ⟨943301446397196177138961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257735261862928236185281 943301446397196177138961)
                      ·
                        rfl

theorem cell23_1837073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 3, 2].length) (baseStart_1837073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837073 prefixEnd_1837073 := by exact prefixLift 1837073
  have htrace : WordTrace (prefixWord ++ tailWord_1837073) baseStart_1837073 baseEnd_1837073 := by
    simpa [prefixWord, tailWord_1837073, baseEnd_1837073] using wordTrace_append hprefix tailTrace_1837073
  have hstable : (prefixWord ++ tailWord_1837073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837073).length < 2 ^ (prefixWord ++ tailWord_1837073).sum := by decide
  have hdescent : baseEnd_1837073 < baseStart_1837073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837080 : List Nat := [2, 1, 2, 3, 2, 1, 2, 4, 2, 1, 3]
def baseStart_1837080 : Nat := 118140960795 + 1837080 * 2 ^ 59
def prefixEnd_1837080 : Nat := 4983230072969 + 3 ^ 40 * 1837080 * 2
def baseEnd_1837080 : Nat := 943305040761777649751429

theorem tailTrace_1837080 : CollatzResearch.WordTrace tailWord_1837080 prefixEnd_1837080 943305040761777649751429 := by
  unfold tailWord_1837080
  simp only [CollatzResearch.WordTrace]
  refine ⟨33501906092290191565166347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44669208123053588753555129 33501906092290191565166347)
  ·
    refine ⟨50252859138435287347749521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33501906092290191565166347 50252859138435287347749521)
    ·
      refine ⟨37689644353826465510812141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50252859138435287347749521 37689644353826465510812141)
      ·
        refine ⟨14133616632684924566554553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37689644353826465510812141 14133616632684924566554553)
        ·
          refine ⟨10600212474513693424915915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14133616632684924566554553 10600212474513693424915915)
          ·
            refine ⟨15900318711770540137373873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600212474513693424915915 15900318711770540137373873)
            ·
              refine ⟨11925239033827905103030405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15900318711770540137373873 11925239033827905103030405)
              ·
                refine ⟨2235982318842732206818201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11925239033827905103030405 2235982318842732206818201)
                ·
                  refine ⟨1676986739132049155113651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235982318842732206818201 1676986739132049155113651)
                  ·
                    refine ⟨2515480108698073732670477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1676986739132049155113651 2515480108698073732670477)
                    ·
                      refine ⟨943305040761777649751429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2515480108698073732670477 943305040761777649751429)
                      ·
                        rfl

theorem cell23_1837080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_1837080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837080 prefixEnd_1837080 := by exact prefixLift 1837080
  have htrace : WordTrace (prefixWord ++ tailWord_1837080) baseStart_1837080 baseEnd_1837080 := by
    simpa [prefixWord, tailWord_1837080, baseEnd_1837080] using wordTrace_append hprefix tailTrace_1837080
  have hstable : (prefixWord ++ tailWord_1837080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837080).length < 2 ^ (prefixWord ++ tailWord_1837080).sum := by decide
  have hdescent : baseEnd_1837080 < baseStart_1837080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837090 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 3, 3, 2]
def baseStart_1837090 : Nat := 118140960795 + 1837090 * 2 ^ 59
def prefixEnd_1837090 : Nat := 4983230072969 + 3 ^ 40 * 1837090 * 2
def baseEnd_1837090 : Nat := 943310175568322610626383

theorem tailTrace_1837090 : CollatzResearch.WordTrace tailWord_1837090 prefixEnd_1837090 943310175568322610626383 := by
  unfold tailWord_1837090
  simp only [CollatzResearch.WordTrace]
  refine ⟨16751044228636038709549181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44669451276362769892131149 16751044228636038709549181)
  ·
    refine ⟨6281641585738514516080943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16751044228636038709549181 6281641585738514516080943)
    ·
      refine ⟨9422462378607771774121415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6281641585738514516080943 9422462378607771774121415)
      ·
        refine ⟨14133693567911657661182123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9422462378607771774121415 14133693567911657661182123)
        ·
          refine ⟨21200540351867486491773185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14133693567911657661182123 21200540351867486491773185)
          ·
            refine ⟨15900405263900614868829889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21200540351867486491773185 15900405263900614868829889)
            ·
              refine ⟨11925303947925461151622417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15900405263900614868829889 11925303947925461151622417)
              ·
                refine ⟨8943977960944095863716813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11925303947925461151622417 8943977960944095863716813)
                ·
                  refine ⟨3353991735354035948893805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8943977960944095863716813 3353991735354035948893805)
                  ·
                    refine ⟨1257746900757763480835177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3353991735354035948893805 1257746900757763480835177)
                    ·
                      refine ⟨943310175568322610626383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257746900757763480835177 943310175568322610626383)
                      ·
                        rfl

theorem cell23_1837090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 3, 2].length) (baseStart_1837090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837090 prefixEnd_1837090 := by exact prefixLift 1837090
  have htrace : WordTrace (prefixWord ++ tailWord_1837090) baseStart_1837090 baseEnd_1837090 := by
    simpa [prefixWord, tailWord_1837090, baseEnd_1837090] using wordTrace_append hprefix tailTrace_1837090
  have hstable : (prefixWord ++ tailWord_1837090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837090).length < 2 ^ (prefixWord ++ tailWord_1837090).sum := by decide
  have hdescent : baseEnd_1837090 < baseStart_1837090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837120 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 1, 4, 2]
def baseStart_1837120 : Nat := 118140960795 + 1837120 * 2 ^ 59
def prefixEnd_1837120 : Nat := 4983230072969 + 3 ^ 40 * 1837120 * 2
def baseEnd_1837120 : Nat := 943325579987957493251245

theorem tailTrace_1837120 : CollatzResearch.WordTrace tailWord_1837120 prefixEnd_1837120 943325579987957493251245 := by
  unfold tailWord_1837120
  simp only [CollatzResearch.WordTrace]
  refine ⟨33502635552217734980894407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44670180736290313307859209 33502635552217734980894407)
  ·
    refine ⟨50253953328326602471341611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33502635552217734980894407 50253953328326602471341611)
    ·
      refine ⟨75380929992489903707012417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50253953328326602471341611 75380929992489903707012417)
      ·
        refine ⟨56535697494367427780259313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75380929992489903707012417 56535697494367427780259313)
        ·
          refine ⟨42401773120775570835194485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56535697494367427780259313 42401773120775570835194485)
          ·
            refine ⟨3975166230072709765799483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42401773120775570835194485 3975166230072709765799483)
            ·
              refine ⟨5962749345109064648699225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975166230072709765799483 5962749345109064648699225)
              ·
                refine ⟨4472062008831798486524419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5962749345109064648699225 4472062008831798486524419)
                ·
                  refine ⟨6708093013247697729786629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472062008831798486524419 6708093013247697729786629)
                  ·
                    refine ⟨1257767439983943324334993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6708093013247697729786629 1257767439983943324334993)
                    ·
                      refine ⟨943325579987957493251245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257767439983943324334993 943325579987957493251245)
                      ·
                        rfl

theorem cell23_1837120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_1837120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837120 prefixEnd_1837120 := by exact prefixLift 1837120
  have htrace : WordTrace (prefixWord ++ tailWord_1837120) baseStart_1837120 baseEnd_1837120 := by
    simpa [prefixWord, tailWord_1837120, baseEnd_1837120] using wordTrace_append hprefix tailTrace_1837120
  have hstable : (prefixWord ++ tailWord_1837120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837120).length < 2 ^ (prefixWord ++ tailWord_1837120).sum := by decide
  have hdescent : baseEnd_1837120 < baseStart_1837120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837154 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 1, 4, 2]
def baseStart_1837154 : Nat := 118140960795 + 1837154 * 2 ^ 59
def prefixEnd_1837154 : Nat := 4983230072969 + 3 ^ 40 * 1837154 * 2
def baseEnd_1837154 : Nat := 943343038330210360226089

theorem tailTrace_1837154 : CollatzResearch.WordTrace tailWord_1837154 prefixEnd_1837154 943343038330210360226089 := by
  unfold tailWord_1837154
  simp only [CollatzResearch.WordTrace]
  refine ⟨16751627796578073442131629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44671007457541529179017677 16751627796578073442131629)
  ·
    refine ⟨6281860423716777540799361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16751627796578073442131629 6281860423716777540799361)
    ·
      refine ⟨4711395317787583155599521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6281860423716777540799361 4711395317787583155599521)
      ·
        refine ⟨3533546488340687366699641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4711395317787583155599521 3533546488340687366699641)
        ·
          refine ⟨2650159866255515525024731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533546488340687366699641 2650159866255515525024731)
          ·
            refine ⟨3975239799383273287537097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650159866255515525024731 3975239799383273287537097)
            ·
              refine ⟨2981429849537454965652823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975239799383273287537097 2981429849537454965652823)
              ·
                refine ⟨4472144774306182448479235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2981429849537454965652823 4472144774306182448479235)
                ·
                  refine ⟨6708217161459273672718853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472144774306182448479235 6708217161459273672718853)
                  ·
                    refine ⟨1257790717773613813634785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6708217161459273672718853 1257790717773613813634785)
                    ·
                      refine ⟨943343038330210360226089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257790717773613813634785 943343038330210360226089)
                      ·
                        rfl

theorem cell23_1837154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_1837154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837154 prefixEnd_1837154 := by exact prefixLift 1837154
  have htrace : WordTrace (prefixWord ++ tailWord_1837154) baseStart_1837154 baseEnd_1837154 := by
    simpa [prefixWord, tailWord_1837154, baseEnd_1837154] using wordTrace_append hprefix tailTrace_1837154
  have hstable : (prefixWord ++ tailWord_1837154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837154).length < 2 ^ (prefixWord ++ tailWord_1837154).sum := by decide
  have hdescent : baseEnd_1837154 < baseStart_1837154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837193 : List Nat := [1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 4]
def baseStart_1837193 : Nat := 118140960795 + 1837193 * 2 ^ 59
def prefixEnd_1837193 : Nat := 4983230072969 + 3 ^ 40 * 1837193 * 2
def baseEnd_1837193 : Nat := 943363064075735707638409

theorem tailTrace_1837193 : CollatzResearch.WordTrace tailWord_1837193 prefixEnd_1837193 943363064075735707638409 := by
  unfold tailWord_1837193
  simp only [CollatzResearch.WordTrace]
  refine ⟨67007933633171003429196233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44671955755447335619464155 67007933633171003429196233)
  ·
    refine ⟨50255950224878252571897175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67007933633171003429196233 50255950224878252571897175)
    ·
      refine ⟨75383925337317378857845763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50255950224878252571897175 75383925337317378857845763)
      ·
        refine ⟨113075888005976068286768645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75383925337317378857845763 113075888005976068286768645)
        ·
          refine ⟨21201729001120512803769121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113075888005976068286768645 21201729001120512803769121)
          ·
            refine ⟨15901296750840384602826841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21201729001120512803769121 15901296750840384602826841)
            ·
              refine ⟨11925972563130288452120131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15901296750840384602826841 11925972563130288452120131)
              ·
                refine ⟨17888958844695432678180197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11925972563130288452120131 17888958844695432678180197)
                ·
                  refine ⟨3354179783380393627158787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17888958844695432678180197 3354179783380393627158787)
                  ·
                    refine ⟨5031269675070590440738181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3354179783380393627158787 5031269675070590440738181)
                    ·
                      refine ⟨943363064075735707638409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5031269675070590440738181 943363064075735707638409)
                      ·
                        rfl

theorem cell23_1837193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 4].length) (baseStart_1837193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837193 prefixEnd_1837193 := by exact prefixLift 1837193
  have htrace : WordTrace (prefixWord ++ tailWord_1837193) baseStart_1837193 baseEnd_1837193 := by
    simpa [prefixWord, tailWord_1837193, baseEnd_1837193] using wordTrace_append hprefix tailTrace_1837193
  have hstable : (prefixWord ++ tailWord_1837193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837193).length < 2 ^ (prefixWord ++ tailWord_1837193).sum := by decide
  have hdescent : baseEnd_1837193 < baseStart_1837193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837263 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 3, 5]
def baseStart_1837263 : Nat := 118140960795 + 1837263 * 2 ^ 59
def prefixEnd_1837263 : Nat := 4983230072969 + 3 ^ 40 * 1837263 * 2
def baseEnd_1837263 : Nat := 314466335907183477921029

theorem tailTrace_1837263 : CollatzResearch.WordTrace tailWord_1837263 prefixEnd_1837263 314466335907183477921029 := by
  unfold tailWord_1837263
  simp only [CollatzResearch.WordTrace]
  refine ⟨67010486742917405384244443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44673657828611603589496295 67010486742917405384244443)
  ·
    refine ⟨100515730114376108076366665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67010486742917405384244443 100515730114376108076366665)
    ·
      refine ⟨75386797585782081057274999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100515730114376108076366665 75386797585782081057274999)
      ·
        refine ⟨113080196378673121585912499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75386797585782081057274999 113080196378673121585912499)
        ·
          refine ⟨169620294568009682378868749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113080196378673121585912499 169620294568009682378868749)
          ·
            refine ⟨63607610463003630892075781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169620294568009682378868749 63607610463003630892075781)
            ·
              refine ⟨11926426961813180792264209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63607610463003630892075781 11926426961813180792264209)
              ·
                refine ⟨8944820221359885594198157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11926426961813180792264209 8944820221359885594198157)
                ·
                  refine ⟨3354307583009957097824309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8944820221359885594198157 3354307583009957097824309)
                  ·
                    refine ⟨314466335907183477921029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3354307583009957097824309 314466335907183477921029)
                    ·
                      rfl

theorem cell23_1837263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_1837263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837263 prefixEnd_1837263 := by exact prefixLift 1837263
  have htrace : WordTrace (prefixWord ++ tailWord_1837263) baseStart_1837263 baseEnd_1837263 := by
    simpa [prefixWord, tailWord_1837263, baseEnd_1837263] using wordTrace_append hprefix tailTrace_1837263
  have hstable : (prefixWord ++ tailWord_1837263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837263).length < 2 ^ (prefixWord ++ tailWord_1837263).sum := by decide
  have hdescent : baseEnd_1837263 < baseStart_1837263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837294 : List Nat := [4, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3]
def baseStart_1837294 : Nat := 118140960795 + 1837294 * 2 ^ 59
def prefixEnd_1837294 : Nat := 4983230072969 + 3 ^ 40 * 1837294 * 2
def baseEnd_1837294 : Nat := 943414925621839812475445

theorem tailTrace_1837294 : CollatzResearch.WordTrace tailWord_1837294 prefixEnd_1837294 943414925621839812475445 := by
  unfold tailWord_1837294
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376452175725637209827867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44674411603870065119081957 8376452175725637209827867)
  ·
    refine ⟨12564678263588455814741801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8376452175725637209827867 12564678263588455814741801)
    ·
      refine ⟨9423508697691341861056351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12564678263588455814741801 9423508697691341861056351)
      ·
        refine ⟨14135263046537012791584527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9423508697691341861056351 14135263046537012791584527)
        ·
          refine ⟨21202894569805519187376791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14135263046537012791584527 21202894569805519187376791)
          ·
            refine ⟨31804341854708278781065187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21202894569805519187376791 31804341854708278781065187)
            ·
              refine ⟨47706512782062418171597781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31804341854708278781065187 47706512782062418171597781)
              ·
                refine ⟨1118121393329587925896823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 47706512782062418171597781 1118121393329587925896823)
                ·
                  refine ⟨1677182089994381888845235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118121393329587925896823 1677182089994381888845235)
                  ·
                    refine ⟨2515773134991572833267853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1677182089994381888845235 2515773134991572833267853)
                    ·
                      refine ⟨943414925621839812475445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2515773134991572833267853 943414925621839812475445)
                      ·
                        rfl

theorem cell23_1837294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_1837294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837294 prefixEnd_1837294 := by exact prefixLift 1837294
  have htrace : WordTrace (prefixWord ++ tailWord_1837294) baseStart_1837294 baseEnd_1837294 := by
    simpa [prefixWord, tailWord_1837294, baseEnd_1837294] using wordTrace_append hprefix tailTrace_1837294
  have hstable : (prefixWord ++ tailWord_1837294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837294).length < 2 ^ (prefixWord ++ tailWord_1837294).sum := by decide
  have hdescent : baseEnd_1837294 < baseStart_1837294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837310 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1837310 : Nat := 118140960795 + 1837310 * 2 ^ 59
def prefixEnd_1837310 : Nat := 4983230072969 + 3 ^ 40 * 1837310 * 2
def baseEnd_1837310 : Nat := 314474380437437249958457

theorem tailTrace_1837310 : CollatzResearch.WordTrace tailWord_1837310 prefixEnd_1837310 314474380437437249958457 := by
  unfold tailWord_1837310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8376525121718391551400673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44674800649164754940803589 8376525121718391551400673)
  ·
    refine ⟨6282393841288793663550505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8376525121718391551400673 6282393841288793663550505)
    ·
      refine ⟨4711795380966595247662879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6282393841288793663550505 4711795380966595247662879)
      ·
        refine ⟨7067693071449892871494319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4711795380966595247662879 7067693071449892871494319)
        ·
          refine ⟨10601539607174839307241479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7067693071449892871494319 10601539607174839307241479)
          ·
            refine ⟨15902309410762258960862219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10601539607174839307241479 15902309410762258960862219)
            ·
              refine ⟨23853464116143388441293329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15902309410762258960862219 23853464116143388441293329)
              ·
                refine ⟨17890098087107541330969997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23853464116143388441293329 17890098087107541330969997)
                ·
                  refine ⟨6708786782665327999113749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17890098087107541330969997 6708786782665327999113749)
                  ·
                    refine ⟨314474380437437249958457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6708786782665327999113749 314474380437437249958457)
                    ·
                      rfl

theorem cell23_1837310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1837310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837310 prefixEnd_1837310 := by exact prefixLift 1837310
  have htrace : WordTrace (prefixWord ++ tailWord_1837310) baseStart_1837310 baseEnd_1837310 := by
    simpa [prefixWord, tailWord_1837310, baseEnd_1837310] using wordTrace_append hprefix tailTrace_1837310
  have hstable : (prefixWord ++ tailWord_1837310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837310).length < 2 ^ (prefixWord ++ tailWord_1837310).sum := by decide
  have hdescent : baseEnd_1837310 < baseStart_1837310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837357 : List Nat := [1, 5, 3, 1, 2, 1, 10]
def baseStart_1837357 : Nat := 118140960795 + 1837357 * 2 ^ 59
def prefixEnd_1837357 : Nat := 4983230072969 + 3 ^ 40 * 1837357 * 2
def baseEnd_1837357 : Nat := 11647497221025593407255

theorem tailTrace_1837357 : CollatzResearch.WordTrace tailWord_1837357 prefixEnd_1837357 11647497221025593407255 := by
  unfold tailWord_1837357
  simp only [CollatzResearch.WordTrace]
  refine ⟨67013915204576859438166325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44675943469717906292110883 67013915204576859438166325)
  ·
    refine ⟨6282554550429080572328093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67013915204576859438166325 6282554550429080572328093)
    ·
      refine ⟨2355957956410905214623035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6282554550429080572328093 2355957956410905214623035)
      ·
        refine ⟨3533936934616357821934553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355957956410905214623035 3533936934616357821934553)
        ·
          refine ⟨2650452700962268366450915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3533936934616357821934553 2650452700962268366450915)
          ·
            refine ⟨3975679051443402549676373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650452700962268366450915 3975679051443402549676373)
            ·
              refine ⟨11647497221025593407255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3975679051443402549676373 11647497221025593407255)
              ·
                rfl

theorem cell23_1837357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 10].length) (baseStart_1837357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837357 prefixEnd_1837357 := by exact prefixLift 1837357
  have htrace : WordTrace (prefixWord ++ tailWord_1837357) baseStart_1837357 baseEnd_1837357 := by
    simpa [prefixWord, tailWord_1837357, baseEnd_1837357] using wordTrace_append hprefix tailTrace_1837357
  have hstable : (prefixWord ++ tailWord_1837357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837357).length < 2 ^ (prefixWord ++ tailWord_1837357).sum := by decide
  have hdescent : baseEnd_1837357 < baseStart_1837357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837361 : List Nat := [1, 2, 2, 3, 5, 1, 1, 2, 2, 4]
def baseStart_1837361 : Nat := 118140960795 + 1837361 * 2 ^ 59
def prefixEnd_1837361 : Nat := 4983230072969 + 3 ^ 40 * 1837361 * 2
def baseEnd_1837361 : Nat := 314483109608563683445879

theorem tailTrace_1837361 : CollatzResearch.WordTrace tailWord_1837361 prefixEnd_1837361 314483109608563683445879 := by
  unfold tailWord_1837361
  simp only [CollatzResearch.WordTrace]
  refine ⟨67014061096562368121311937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44676040731041578747541291 67014061096562368121311937)
  ·
    refine ⟨50260545822421776090983953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67014061096562368121311937 50260545822421776090983953)
    ·
      refine ⟨37695409366816332068237965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50260545822421776090983953 37695409366816332068237965)
      ·
        refine ⟨14135778512556124525589237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37695409366816332068237965 14135778512556124525589237)
        ·
          refine ⟨1325229235552136674273991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14135778512556124525589237 1325229235552136674273991)
          ·
            refine ⟨1987843853328205011410987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325229235552136674273991 1987843853328205011410987)
            ·
              refine ⟨2981765779992307517116481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987843853328205011410987 2981765779992307517116481)
              ·
                refine ⟨2236324334994230637837361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981765779992307517116481 2236324334994230637837361)
                ·
                  refine ⟨1677243251245672978378021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2236324334994230637837361 1677243251245672978378021)
                  ·
                    refine ⟨314483109608563683445879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1677243251245672978378021 314483109608563683445879)
                    ·
                      rfl

theorem cell23_1837361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_1837361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837361 prefixEnd_1837361 := by exact prefixLift 1837361
  have htrace : WordTrace (prefixWord ++ tailWord_1837361) baseStart_1837361 baseEnd_1837361 := by
    simpa [prefixWord, tailWord_1837361, baseEnd_1837361] using wordTrace_append hprefix tailTrace_1837361
  have hstable : (prefixWord ++ tailWord_1837361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837361).length < 2 ^ (prefixWord ++ tailWord_1837361).sum := by decide
  have hdescent : baseEnd_1837361 < baseStart_1837361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837394 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_1837394 : Nat := 118140960795 + 1837394 * 2 ^ 59
def prefixEnd_1837394 : Nat := 4983230072969 + 3 ^ 40 * 1837394 * 2
def baseEnd_1837394 : Nat := 943466273687289421224985

theorem tailTrace_1837394 : CollatzResearch.WordTrace tailWord_1837394 prefixEnd_1837394 943466273687289421224985 := by
  unfold tailWord_1837394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16753816176360703689315809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44676843136961876504842157 16753816176360703689315809)
  ·
    refine ⟨12565362132270527766986857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16753816176360703689315809 12565362132270527766986857)
    ·
      refine ⟨9424021599202895825240143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12565362132270527766986857 9424021599202895825240143)
      ·
        refine ⟨14136032398804343737860215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424021599202895825240143 14136032398804343737860215)
        ·
          refine ⟨21204048598206515606790323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14136032398804343737860215 21204048598206515606790323)
          ·
            refine ⟨31806072897309773410185485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21204048598206515606790323 31806072897309773410185485)
            ·
              refine ⟨11927277336491165028819557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31806072897309773410185485 11927277336491165028819557)
              ·
                refine ⟨2236364500592093442903667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11927277336491165028819557 2236364500592093442903667)
                ·
                  refine ⟨3354546750888140164355501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236364500592093442903667 3354546750888140164355501)
                  ·
                    refine ⟨1257955031583052561633313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3354546750888140164355501 1257955031583052561633313)
                    ·
                      refine ⟨943466273687289421224985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257955031583052561633313 943466273687289421224985)
                      ·
                        rfl

theorem cell23_1837394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_1837394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837394 prefixEnd_1837394 := by exact prefixLift 1837394
  have htrace : WordTrace (prefixWord ++ tailWord_1837394) baseStart_1837394 baseEnd_1837394 := by
    simpa [prefixWord, tailWord_1837394, baseEnd_1837394] using wordTrace_append hprefix tailTrace_1837394
  have hstable : (prefixWord ++ tailWord_1837394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837394).length < 2 ^ (prefixWord ++ tailWord_1837394).sum := by decide
  have hdescent : baseEnd_1837394 < baseStart_1837394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837407 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 1, 4, 2]
def baseStart_1837407 : Nat := 118140960795 + 1837407 * 2 ^ 59
def prefixEnd_1837407 : Nat := 4983230072969 + 3 ^ 40 * 1837407 * 2
def baseEnd_1837407 : Nat := 943472948935797870362425

theorem tailTrace_1837407 : CollatzResearch.WordTrace tailWord_1837407 prefixEnd_1837407 943472948935797870362425 := by
  unfold tailWord_1837407
  simp only [CollatzResearch.WordTrace]
  refine ⟨67015738854395717977486475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44677159236263811984990983 67015738854395717977486475)
  ·
    refine ⟨100523608281593576966229713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67015738854395717977486475 100523608281593576966229713)
    ·
      refine ⟨75392706211195182724672285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100523608281593576966229713 75392706211195182724672285)
      ·
        refine ⟨28272264829198193521752107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75392706211195182724672285 28272264829198193521752107)
        ·
          refine ⟨42408397243797290282628161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28272264829198193521752107 42408397243797290282628161)
          ·
            refine ⟨31806297932847967711971121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42408397243797290282628161 31806297932847967711971121)
            ·
              refine ⟨23854723449635975783978341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31806297932847967711971121 23854723449635975783978341)
              ·
                refine ⟨4472760646806745459495939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23854723449635975783978341 4472760646806745459495939)
                ·
                  refine ⟨6709140970210118189243909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4472760646806745459495939 6709140970210118189243909)
                  ·
                    refine ⟨1257963931914397160483233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6709140970210118189243909 1257963931914397160483233)
                    ·
                      refine ⟨943472948935797870362425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257963931914397160483233 943472948935797870362425)
                      ·
                        rfl

theorem cell23_1837407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_1837407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837407 prefixEnd_1837407 := by exact prefixLift 1837407
  have htrace : WordTrace (prefixWord ++ tailWord_1837407) baseStart_1837407 baseEnd_1837407 := by
    simpa [prefixWord, tailWord_1837407, baseEnd_1837407] using wordTrace_append hprefix tailTrace_1837407
  have hstable : (prefixWord ++ tailWord_1837407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837407).length < 2 ^ (prefixWord ++ tailWord_1837407).sum := by decide
  have hdescent : baseEnd_1837407 < baseStart_1837407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837424 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 4, 2, 2]
def baseStart_1837424 : Nat := 118140960795 + 1837424 * 2 ^ 59
def prefixEnd_1837424 : Nat := 4983230072969 + 3 ^ 40 * 1837424 * 2
def baseEnd_1837424 : Nat := 943481678106924303849847

theorem tailTrace_1837424 : CollatzResearch.WordTrace tailWord_1837424 prefixEnd_1837424 943481678106924303849847 := by
  unfold tailWord_1837424
  simp only [CollatzResearch.WordTrace]
  refine ⟨33508179447667064940427663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44677572596889419920570217 33508179447667064940427663)
  ·
    refine ⟨50262269171500597410641495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33508179447667064940427663 50262269171500597410641495)
    ·
      refine ⟨75393403757250896115962243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50262269171500597410641495 75393403757250896115962243)
      ·
        refine ⟨113090105635876344173943365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75393403757250896115962243 113090105635876344173943365)
        ·
          refine ⟨21204394806726814532614381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113090105635876344173943365 21204394806726814532614381)
          ·
            refine ⟨7951648052522555449730393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21204394806726814532614381 7951648052522555449730393)
            ·
              refine ⟨5963736039391916587297795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7951648052522555449730393 5963736039391916587297795)
              ·
                refine ⟨8945604059087874880946693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5963736039391916587297795 8945604059087874880946693)
                ·
                  refine ⟨1677300761078976540177505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8945604059087874880946693 1677300761078976540177505)
                  ·
                    refine ⟨1257975570809232405133129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1677300761078976540177505 1257975570809232405133129)
                    ·
                      refine ⟨943481678106924303849847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1257975570809232405133129 943481678106924303849847)
                      ·
                        rfl

theorem cell23_1837424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 2, 2].length) (baseStart_1837424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837424 prefixEnd_1837424 := by exact prefixLift 1837424
  have htrace : WordTrace (prefixWord ++ tailWord_1837424) baseStart_1837424 baseEnd_1837424 := by
    simpa [prefixWord, tailWord_1837424, baseEnd_1837424] using wordTrace_append hprefix tailTrace_1837424
  have hstable : (prefixWord ++ tailWord_1837424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837424).length < 2 ^ (prefixWord ++ tailWord_1837424).sum := by decide
  have hdescent : baseEnd_1837424 < baseStart_1837424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837541 : List Nat := [1, 3, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_1837541 : Nat := 118140960795 + 1837541 * 2 ^ 59
def prefixEnd_1837541 : Nat := 4983230072969 + 3 ^ 40 * 1837541 * 2
def baseEnd_1837541 : Nat := 314513918447833448695603

theorem tailTrace_1837541 : CollatzResearch.WordTrace tailWord_1837541 prefixEnd_1837541 314513918447833448695603 := by
  unfold tailWord_1837541
  simp only [CollatzResearch.WordTrace]
  refine ⟨67020626235910258862864477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44680417490606839241909651 67020626235910258862864477)
  ·
    refine ⟨25132734838466347073574179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67020626235910258862864477 25132734838466347073574179)
    ·
      refine ⟨37699102257699520610361269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25132734838466347073574179 37699102257699520610361269)
      ·
        refine ⟨3534290836659330057221369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37699102257699520610361269 3534290836659330057221369)
        ·
          refine ⟨2650718127494497542916027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3534290836659330057221369 2650718127494497542916027)
          ·
            refine ⟨3976077191241746314374041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650718127494497542916027 3976077191241746314374041)
            ·
              refine ⟨2982057893431309735780531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3976077191241746314374041 2982057893431309735780531)
              ·
                refine ⟨4473086840146964603670797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982057893431309735780531 4473086840146964603670797)
                ·
                  refine ⟨1677407565055111726376549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4473086840146964603670797 1677407565055111726376549)
                  ·
                    refine ⟨314513918447833448695603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1677407565055111726376549 314513918447833448695603)
                    ·
                      rfl

theorem cell23_1837541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_1837541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837541 prefixEnd_1837541 := by exact prefixLift 1837541
  have htrace : WordTrace (prefixWord ++ tailWord_1837541) baseStart_1837541 baseEnd_1837541 := by
    simpa [prefixWord, tailWord_1837541, baseEnd_1837541] using wordTrace_append hprefix tailTrace_1837541
  have hstable : (prefixWord ++ tailWord_1837541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837541).length < 2 ^ (prefixWord ++ tailWord_1837541).sum := by decide
  have hdescent : baseEnd_1837541 < baseStart_1837541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837575 : List Nat := [1, 1, 4, 3, 4, 1, 1, 3, 1, 4]
def baseStart_1837575 : Nat := 118140960795 + 1837575 * 2 ^ 59
def prefixEnd_1837575 : Nat := 4983230072969 + 3 ^ 40 * 1837575 * 2
def baseEnd_1837575 : Nat := 314519737895251071020551

theorem tailTrace_1837575 : CollatzResearch.WordTrace tailWord_1837575 prefixEnd_1837575 314519737895251071020551 := by
  unfold tailWord_1837575
  simp only [CollatzResearch.WordTrace]
  refine ⟨67021866317787082669602179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44681244211858055113068119 67021866317787082669602179)
  ·
    refine ⟨100532799476680624004403269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67021866317787082669602179 100532799476680624004403269)
    ·
      refine ⟨18849899901877617000825613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100532799476680624004403269 18849899901877617000825613)
      ·
        refine ⟨7068712463204106375309605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18849899901877617000825613 7068712463204106375309605)
        ·
          refine ⟨1325383586850769945370551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7068712463204106375309605 1325383586850769945370551)
          ·
            refine ⟨1988075380276154918055827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325383586850769945370551 1988075380276154918055827)
            ·
              refine ⟨2982113070414232377083741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988075380276154918055827 2982113070414232377083741)
              ·
                refine ⟨1118292401405337141406403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2982113070414232377083741 1118292401405337141406403)
                ·
                  refine ⟨1677438602108005712109605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118292401405337141406403 1677438602108005712109605)
                  ·
                    refine ⟨314519737895251071020551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1677438602108005712109605 314519737895251071020551)
                    ·
                      rfl

theorem cell23_1837575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_1837575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837575 prefixEnd_1837575 := by exact prefixLift 1837575
  have htrace : WordTrace (prefixWord ++ tailWord_1837575) baseStart_1837575 baseEnd_1837575 := by
    simpa [prefixWord, tailWord_1837575, baseEnd_1837575] using wordTrace_append hprefix tailTrace_1837575
  have hstable : (prefixWord ++ tailWord_1837575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837575).length < 2 ^ (prefixWord ++ tailWord_1837575).sum := by decide
  have hdescent : baseEnd_1837575 < baseStart_1837575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837617 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1837617 : Nat := 118140960795 + 1837617 * 2 ^ 59
def prefixEnd_1837617 : Nat := 4983230072969 + 3 ^ 40 * 1837617 * 2
def baseEnd_1837617 : Nat := 943580779873242048736459

theorem tailTrace_1837617 : CollatzResearch.WordTrace tailWord_1837617 prefixEnd_1837617 943580779873242048736459 := by
  unfold tailWord_1837617
  simp only [CollatzResearch.WordTrace]
  refine ⟨67023398183634923842631105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44682265455756615895087403 67023398183634923842631105)
  ·
    refine ⟨50267548637726192881973329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67023398183634923842631105 50267548637726192881973329)
    ·
      refine ⟨37700661478294644661479997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50267548637726192881973329 37700661478294644661479997)
      ·
        refine ⟨14137748054360491748054999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37700661478294644661479997 14137748054360491748054999)
        ·
          refine ⟨21206622081540737622082499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137748054360491748054999 21206622081540737622082499)
          ·
            refine ⟨31809933122311106433123749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21206622081540737622082499 31809933122311106433123749)
            ·
              refine ⟨5964362460433332456210703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31809933122311106433123749 5964362460433332456210703)
              ·
                refine ⟨8946543690649998684316055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964362460433332456210703 8946543690649998684316055)
                ·
                  refine ⟨13419815535974998026474083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946543690649998684316055 13419815535974998026474083)
                  ·
                    refine ⟨20129723303962497039711125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13419815535974998026474083 20129723303962497039711125)
                    ·
                      refine ⟨943580779873242048736459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20129723303962497039711125 943580779873242048736459)
                      ·
                        rfl

theorem cell23_1837617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1837617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837617 prefixEnd_1837617 := by exact prefixLift 1837617
  have htrace : WordTrace (prefixWord ++ tailWord_1837617) baseStart_1837617 baseEnd_1837617 := by
    simpa [prefixWord, tailWord_1837617, baseEnd_1837617] using wordTrace_append hprefix tailTrace_1837617
  have hstable : (prefixWord ++ tailWord_1837617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837617).length < 2 ^ (prefixWord ++ tailWord_1837617).sum := by decide
  have hdescent : baseEnd_1837617 < baseStart_1837617 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837621 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_1837621 : Nat := 118140960795 + 1837621 * 2 ^ 59
def prefixEnd_1837621 : Nat := 4983230072969 + 3 ^ 40 * 1837621 * 2
def baseEnd_1837621 : Nat := 943582833795860033086441

theorem tailTrace_1837621 : CollatzResearch.WordTrace tailWord_1837621 prefixEnd_1837621 943582833795860033086441 := by
  unfold tailWord_1837621
  simp only [CollatzResearch.WordTrace]
  refine ⟨67023544075620432525776717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44682362717080288350517811 67023544075620432525776717)
  ·
    refine ⟨25133829028357662197166269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67023544075620432525776717 25133829028357662197166269)
    ·
      refine ⟨9425185885634123323937351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25133829028357662197166269 9425185885634123323937351)
      ·
        refine ⟨14137778828451184985906027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425185885634123323937351 14137778828451184985906027)
        ·
          refine ⟨21206668242676777478859041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14137778828451184985906027 21206668242676777478859041)
          ·
            refine ⟨15905001182007583109144281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21206668242676777478859041 15905001182007583109144281)
            ·
              refine ⟨11928750886505687331858211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15905001182007583109144281 11928750886505687331858211)
              ·
                refine ⟨17893126329758530997787317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11928750886505687331858211 17893126329758530997787317)
                ·
                  refine ⟨1677480593414862281042561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17893126329758530997787317 1677480593414862281042561)
                  ·
                    refine ⟨1258110445061146710781921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1677480593414862281042561 1258110445061146710781921)
                    ·
                      refine ⟨943582833795860033086441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1258110445061146710781921 943582833795860033086441)
                      ·
                        rfl

theorem cell23_1837621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_1837621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837621 prefixEnd_1837621 := by exact prefixLift 1837621
  have htrace : WordTrace (prefixWord ++ tailWord_1837621) baseStart_1837621 baseEnd_1837621 := by
    simpa [prefixWord, tailWord_1837621, baseEnd_1837621] using wordTrace_append hprefix tailTrace_1837621
  have hstable : (prefixWord ++ tailWord_1837621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837621).length < 2 ^ (prefixWord ++ tailWord_1837621).sum := by decide
  have hdescent : baseEnd_1837621 < baseStart_1837621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837624 : List Nat := [2, 1, 2, 1, 4, 1, 3, 1, 3, 2, 3]
def baseStart_1837624 : Nat := 118140960795 + 1837624 * 2 ^ 59
def prefixEnd_1837624 : Nat := 4983230072969 + 3 ^ 40 * 1837624 * 2
def baseEnd_1837624 : Nat := 943584374237823521348927

theorem tailTrace_1837624 : CollatzResearch.WordTrace tailWord_1837624 prefixEnd_1837624 943584374237823521348927 := by
  unfold tailWord_1837624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33511826747304782019067963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44682435663073042692090617 33511826747304782019067963)
  ·
    refine ⟨50267740120957173028601945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33511826747304782019067963 50267740120957173028601945)
    ·
      refine ⟨37700805090717879771451459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50267740120957173028601945 37700805090717879771451459)
      ·
        refine ⟨56551207636076819657177189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37700805090717879771451459 56551207636076819657177189)
        ·
          refine ⟨10603351431764403685720723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56551207636076819657177189 10603351431764403685720723)
          ·
            refine ⟨15905027147646605528581085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603351431764403685720723 15905027147646605528581085)
            ·
              refine ⟨5964385180367477073217907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15905027147646605528581085 5964385180367477073217907)
              ·
                refine ⟨8946577770551215609826861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964385180367477073217907 8946577770551215609826861)
                ·
                  refine ⟨3354966663956705853685073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8946577770551215609826861 3354966663956705853685073)
                  ·
                    refine ⟨2516224997967529390263805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3354966663956705853685073 2516224997967529390263805)
                    ·
                      refine ⟨943584374237823521348927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2516224997967529390263805 943584374237823521348927)
                      ·
                        rfl

theorem cell23_1837624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 3, 2, 3].length) (baseStart_1837624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837624 prefixEnd_1837624 := by exact prefixLift 1837624
  have htrace : WordTrace (prefixWord ++ tailWord_1837624) baseStart_1837624 baseEnd_1837624 := by
    simpa [prefixWord, tailWord_1837624, baseEnd_1837624] using wordTrace_append hprefix tailTrace_1837624
  have hstable : (prefixWord ++ tailWord_1837624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837624).length < 2 ^ (prefixWord ++ tailWord_1837624).sum := by decide
  have hdescent : baseEnd_1837624 < baseStart_1837624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 4, 2, 2]
def baseStart_1837711 : Nat := 118140960795 + 1837711 * 2 ^ 59
def prefixEnd_1837711 : Nat := 4983230072969 + 3 ^ 40 * 1837711 * 2
def baseEnd_1837711 : Nat := 943629047054764680961027

theorem tailTrace_1837711 : CollatzResearch.WordTrace tailWord_1837711 prefixEnd_1837711 943629047054764680961027 := by
  unfold tailWord_1837711
  simp only [CollatzResearch.WordTrace]
  refine ⟨67026826645294377896552987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44684551096862918597701991 67026826645294377896552987)
  ·
    refine ⟨100540239967941566844829481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67026826645294377896552987 100540239967941566844829481)
    ·
      refine ⟨75405179975956175133622111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100540239967941566844829481 75405179975956175133622111)
      ·
        refine ⟨113107769963934262700433167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75405179975956175133622111 113107769963934262700433167)
        ·
          refine ⟨169661654945901394050649751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113107769963934262700433167 169661654945901394050649751)
          ·
            refine ⟨254492482418852091075974627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169661654945901394050649751 254492482418852091075974627)
            ·
              refine ⟨381738723628278136613961941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254492482418852091075974627 381738723628278136613961941)
              ·
                refine ⟨8947001335037768826889733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 381738723628278136613961941 8947001335037768826889733)
                ·
                  refine ⟨1677562750319581655041825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8947001335037768826889733 1677562750319581655041825)
                  ·
                    refine ⟨1258172062739686241281369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1677562750319581655041825 1258172062739686241281369)
                    ·
                      refine ⟨943629047054764680961027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1258172062739686241281369 943629047054764680961027)
                      ·
                        rfl

theorem cell23_1837711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 2, 2].length) (baseStart_1837711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837711 prefixEnd_1837711 := by exact prefixLift 1837711
  have htrace : WordTrace (prefixWord ++ tailWord_1837711) baseStart_1837711 baseEnd_1837711 := by
    simpa [prefixWord, tailWord_1837711, baseEnd_1837711] using wordTrace_append hprefix tailTrace_1837711
  have hstable : (prefixWord ++ tailWord_1837711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837711).length < 2 ^ (prefixWord ++ tailWord_1837711).sum := by decide
  have hdescent : baseEnd_1837711 < baseStart_1837711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837722 : List Nat := [3, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1837722 : Nat := 118140960795 + 1837722 * 2 ^ 59
def prefixEnd_1837722 : Nat := 4983230072969 + 3 ^ 40 * 1837722 * 2
def baseEnd_1837722 : Nat := 943634695341964137923477

theorem tailTrace_1837722 : CollatzResearch.WordTrace tailWord_1837722 prefixEnd_1837722 943634695341964137923477 := by
  unfold tailWord_1837722
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756806962063631693800855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44684818565503017850135613 16756806962063631693800855)
  ·
    refine ⟨25135210443095447540701283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16756806962063631693800855 25135210443095447540701283)
    ·
      refine ⟨37702815664643171311051925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25135210443095447540701283 37702815664643171311051925)
      ·
        refine ⟨1767319484280148655205559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37702815664643171311051925 1767319484280148655205559)
        ·
          refine ⟨2650979226420222982808339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767319484280148655205559 2650979226420222982808339)
          ·
            refine ⟨3976468839630334474212509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650979226420222982808339 3976468839630334474212509)
            ·
              refine ⟨1491175814861375427829691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3976468839630334474212509 1491175814861375427829691)
              ·
                refine ⟨2236763722292063141744537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491175814861375427829691 2236763722292063141744537)
                ·
                  refine ⟨1677572791719047356308403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2236763722292063141744537 1677572791719047356308403)
                  ·
                    refine ⟨2516359187578571034462605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1677572791719047356308403 2516359187578571034462605)
                    ·
                      refine ⟨943634695341964137923477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2516359187578571034462605 943634695341964137923477)
                      ·
                        rfl

theorem cell23_1837722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1837722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837722 prefixEnd_1837722 := by exact prefixLift 1837722
  have htrace : WordTrace (prefixWord ++ tailWord_1837722) baseStart_1837722 baseEnd_1837722 := by
    simpa [prefixWord, tailWord_1837722, baseEnd_1837722] using wordTrace_append hprefix tailTrace_1837722
  have hstable : (prefixWord ++ tailWord_1837722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837722).length < 2 ^ (prefixWord ++ tailWord_1837722).sum := by decide
  have hdescent : baseEnd_1837722 < baseStart_1837722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837768 : List Nat := [2, 1, 3, 1, 2, 4, 3, 2, 5]
def baseStart_1837768 : Nat := 118140960795 + 1837768 * 2 ^ 59
def prefixEnd_1837768 : Nat := 4983230072969 + 3 ^ 40 * 1837768 * 2
def baseEnd_1837768 : Nat := 104850923939118995327585

theorem tailTrace_1837768 : CollatzResearch.WordTrace tailWord_1837768 prefixEnd_1837768 104850923939118995327585 := by
  unfold tailWord_1837768
  simp only [CollatzResearch.WordTrace]
  refine ⟨33514452803043938315688979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44685937070725251087585305 33514452803043938315688979)
  ·
    refine ⟨50271679204565907473533469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33514452803043938315688979 50271679204565907473533469)
    ·
      refine ⟨18851879701712215302575051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50271679204565907473533469 18851879701712215302575051)
      ·
        refine ⟨28277819552568322953862577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851879701712215302575051 28277819552568322953862577)
        ·
          refine ⟨21208364664426242215396933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28277819552568322953862577 21208364664426242215396933)
          ·
            refine ⟨3976568374579920415386925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21208364664426242215396933 3976568374579920415386925)
            ·
              refine ⟨1491213140467470155770097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3976568374579920415386925 1491213140467470155770097)
              ·
                refine ⟨1118409855350602616827573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491213140467470155770097 1118409855350602616827573)
                ·
                  refine ⟨104850923939118995327585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1118409855350602616827573 104850923939118995327585)
                  ·
                    rfl

theorem cell23_1837768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 5].length) (baseStart_1837768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837768 prefixEnd_1837768 := by exact prefixLift 1837768
  have htrace : WordTrace (prefixWord ++ tailWord_1837768) baseStart_1837768 baseEnd_1837768 := by
    simpa [prefixWord, tailWord_1837768, baseEnd_1837768] using wordTrace_append hprefix tailTrace_1837768
  have hstable : (prefixWord ++ tailWord_1837768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837768).length < 2 ^ (prefixWord ++ tailWord_1837768).sum := by decide
  have hdescent : baseEnd_1837768 < baseStart_1837768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837774 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1837774 : Nat := 118140960795 + 1837774 * 2 ^ 59
def prefixEnd_1837774 : Nat := 4983230072969 + 3 ^ 40 * 1837774 * 2
def baseEnd_1837774 : Nat := 943661396335997934473237

theorem tailTrace_1837774 : CollatzResearch.WordTrace tailWord_1837774 prefixEnd_1837774 943661396335997934473237 := by
  unfold tailWord_1837774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8378640555508267457012047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44686082962710759770730917 8378640555508267457012047)
  ·
    refine ⟨12567960833262401185518071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8378640555508267457012047 12567960833262401185518071)
    ·
      refine ⟨18851941249893601778277107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12567960833262401185518071 18851941249893601778277107)
      ·
        refine ⟨28277911874840402667415661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851941249893601778277107 28277911874840402667415661)
        ·
          refine ⟨10604216953065151000280873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28277911874840402667415661 10604216953065151000280873)
          ·
            refine ⟨7953162714798863250210655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10604216953065151000280873 7953162714798863250210655)
            ·
              refine ⟨11929744072198294875315983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7953162714798863250210655 11929744072198294875315983)
              ·
                refine ⟨17894616108297442312973975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11929744072198294875315983 17894616108297442312973975)
                ·
                  refine ⟨26841924162446163469460963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17894616108297442312973975 26841924162446163469460963)
                  ·
                    refine ⟨40262886243669245204191445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26841924162446163469460963 40262886243669245204191445)
                    ·
                      refine ⟨943661396335997934473237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40262886243669245204191445 943661396335997934473237)
                      ·
                        rfl

theorem cell23_1837774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1837774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837774 prefixEnd_1837774 := by exact prefixLift 1837774
  have htrace : WordTrace (prefixWord ++ tailWord_1837774) baseStart_1837774 baseEnd_1837774 := by
    simpa [prefixWord, tailWord_1837774, baseEnd_1837774] using wordTrace_append hprefix tailTrace_1837774
  have hstable : (prefixWord ++ tailWord_1837774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837774).length < 2 ^ (prefixWord ++ tailWord_1837774).sum := by decide
  have hdescent : baseEnd_1837774 < baseStart_1837774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837821 : List Nat := [1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_1837821 : Nat := 118140960795 + 1837821 * 2 ^ 59
def prefixEnd_1837821 : Nat := 4983230072969 + 3 ^ 40 * 1837821 * 2
def baseEnd_1837821 : Nat := 943685529926759250585521

theorem tailTrace_1837821 : CollatzResearch.WordTrace tailWord_1837821 prefixEnd_1837821 943685529926759250585521 := by
  unfold tailWord_1837821
  simp only [CollatzResearch.WordTrace]
  refine ⟨67030838674895866683057317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44687225783263911122038211 67030838674895866683057317)
  ·
    refine ⟨12568282251542975003073247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67030838674895866683057317 12568282251542975003073247)
    ·
      refine ⟨18852423377314462504609871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12568282251542975003073247 18852423377314462504609871)
      ·
        refine ⟨28278635065971693756914807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18852423377314462504609871 28278635065971693756914807)
        ·
          refine ⟨42417952598957540635372211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28278635065971693756914807 42417952598957540635372211)
          ·
            refine ⟨63626928898436310953058317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42417952598957540635372211 63626928898436310953058317)
            ·
              refine ⟨23860098336913616607396869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63626928898436310953058317 23860098336913616607396869)
              ·
                refine ⟨4473768438171303113886913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23860098336913616607396869 4473768438171303113886913)
                ·
                  refine ⟨3355326328628477335415185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4473768438171303113886913 3355326328628477335415185)
                  ·
                    refine ⟨2516494746471358001561389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355326328628477335415185 2516494746471358001561389)
                    ·
                      refine ⟨943685529926759250585521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2516494746471358001561389 943685529926759250585521)
                      ·
                        rfl

theorem cell23_1837821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_1837821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837821 prefixEnd_1837821 := by exact prefixLift 1837821
  have htrace : WordTrace (prefixWord ++ tailWord_1837821) baseStart_1837821 baseEnd_1837821 := by
    simpa [prefixWord, tailWord_1837821, baseEnd_1837821] using wordTrace_append hprefix tailTrace_1837821
  have hstable : (prefixWord ++ tailWord_1837821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837821).length < 2 ^ (prefixWord ++ tailWord_1837821).sum := by decide
  have hdescent : baseEnd_1837821 < baseStart_1837821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837892 : List Nat := [2, 3, 4, 2, 1, 1, 3, 1, 6]
def baseStart_1837892 : Nat := 118140960795 + 1837892 * 2 ^ 59
def prefixEnd_1837892 : Nat := 4983230072969 + 3 ^ 40 * 1837892 * 2
def baseEnd_1837892 : Nat := 104857998561469830310855

theorem tailTrace_1837892 : CollatzResearch.WordTrace tailWord_1837892 prefixEnd_1837892 104857998561469830310855 := by
  unfold tailWord_1837892
  simp only [CollatzResearch.WordTrace]
  refine ⟨33516714128819322904445965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44688952171759097205927953 33516714128819322904445965)
  ·
    refine ⟨12568767798307246089167237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33516714128819322904445965 12568767798307246089167237)
    ·
      refine ⟨2356643962182608641718857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12568767798307246089167237 2356643962182608641718857)
      ·
        refine ⟨1767482971636956481289143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2356643962182608641718857 1767482971636956481289143)
        ·
          refine ⟨2651224457455434721933715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1767482971636956481289143 2651224457455434721933715)
          ·
            refine ⟨3976836686183152082900573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651224457455434721933715 3976836686183152082900573)
            ·
              refine ⟨1491313757318682031087715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3976836686183152082900573 1491313757318682031087715)
              ·
                refine ⟨2236970635978023046631573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491313757318682031087715 2236970635978023046631573)
                ·
                  refine ⟨104857998561469830310855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2236970635978023046631573 104857998561469830310855)
                  ·
                    rfl

theorem cell23_1837892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_1837892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837892 prefixEnd_1837892 := by exact prefixLift 1837892
  have htrace : WordTrace (prefixWord ++ tailWord_1837892) baseStart_1837892 baseEnd_1837892 := by
    simpa [prefixWord, tailWord_1837892, baseEnd_1837892] using wordTrace_append hprefix tailTrace_1837892
  have hstable : (prefixWord ++ tailWord_1837892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837892).length < 2 ^ (prefixWord ++ tailWord_1837892).sum := by decide
  have hdescent : baseEnd_1837892 < baseStart_1837892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837928 : List Nat := [2, 1, 4, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1837928 : Nat := 118140960795 + 1837928 * 2 ^ 59
def prefixEnd_1837928 : Nat := 4983230072969 + 3 ^ 40 * 1837928 * 2
def baseEnd_1837928 : Nat := 943740472356790331947529

theorem tailTrace_1837928 : CollatzResearch.WordTrace tailWord_1837928 prefixEnd_1837928 943740472356790331947529 := by
  unfold tailWord_1837928
  simp only [CollatzResearch.WordTrace]
  refine ⟨33517370642754111978601219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44689827523672149304801625 33517370642754111978601219)
  ·
    refine ⟨50276055964131167967901829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33517370642754111978601219 50276055964131167967901829)
    ·
      refine ⟨9426760493274593993981593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50276055964131167967901829 9426760493274593993981593)
      ·
        refine ⟨7070070369955945495486195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9426760493274593993981593 7070070369955945495486195)
        ·
          refine ⟨10605105554933918243229293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7070070369955945495486195 10605105554933918243229293)
          ·
            refine ⟨3976914583100219341210985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10605105554933918243229293 3976914583100219341210985)
            ·
              refine ⟨2982685937325164505908239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3976914583100219341210985 2982685937325164505908239)
              ·
                refine ⟨4474028905987746758862359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982685937325164505908239 4474028905987746758862359)
                ·
                  refine ⟨6711043358981620138293539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474028905987746758862359 6711043358981620138293539)
                  ·
                    refine ⟨10066565038472430207440309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6711043358981620138293539 10066565038472430207440309)
                    ·
                      refine ⟨943740472356790331947529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10066565038472430207440309 943740472356790331947529)
                      ·
                        rfl

theorem cell23_1837928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1837928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837928 prefixEnd_1837928 := by exact prefixLift 1837928
  have htrace : WordTrace (prefixWord ++ tailWord_1837928) baseStart_1837928 baseEnd_1837928 := by
    simpa [prefixWord, tailWord_1837928, baseEnd_1837928] using wordTrace_append hprefix tailTrace_1837928
  have hstable : (prefixWord ++ tailWord_1837928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837928).length < 2 ^ (prefixWord ++ tailWord_1837928).sum := by decide
  have hdescent : baseEnd_1837928 < baseStart_1837928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1837962 : List Nat := [3, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_1837962 : Nat := 118140960795 + 1837962 * 2 ^ 59
def prefixEnd_1837962 : Nat := 4983230072969 + 3 ^ 40 * 1837962 * 2
def baseEnd_1837962 : Nat := 943757930699043198922373

theorem tailTrace_1837962 : CollatzResearch.WordTrace tailWord_1837962 prefixEnd_1837962 943757930699043198922373 := by
  unfold tailWord_1837962
  simp only [CollatzResearch.WordTrace]
  refine ⟨16758995341846261940985035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44690654244923365175960093 16758995341846261940985035)
  ·
    refine ⟨25138493012769392911477553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16758995341846261940985035 25138493012769392911477553)
    ·
      refine ⟨18853869759577044683608165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25138493012769392911477553 18853869759577044683608165)
      ·
        refine ⟨3535100579920695878176531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18853869759577044683608165 3535100579920695878176531)
        ·
          refine ⟨5302650869881043817264797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535100579920695878176531 5302650869881043817264797)
          ·
            refine ⟨1988494076205391431474299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5302650869881043817264797 1988494076205391431474299)
            ·
              refine ⟨2982741114308087147211449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988494076205391431474299 2982741114308087147211449)
              ·
                refine ⟨2237055835731065360408587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982741114308087147211449 2237055835731065360408587)
                ·
                  refine ⟨3355583753596598040612881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237055835731065360408587 3355583753596598040612881)
                  ·
                    refine ⟨2516687815197448530459661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355583753596598040612881 2516687815197448530459661)
                    ·
                      refine ⟨943757930699043198922373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2516687815197448530459661 943757930699043198922373)
                      ·
                        rfl

theorem cell23_1837962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_1837962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1837962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1837962 prefixEnd_1837962 := by exact prefixLift 1837962
  have htrace : WordTrace (prefixWord ++ tailWord_1837962) baseStart_1837962 baseEnd_1837962 := by
    simpa [prefixWord, tailWord_1837962, baseEnd_1837962] using wordTrace_append hprefix tailTrace_1837962
  have hstable : (prefixWord ++ tailWord_1837962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1837962).length < 2 ^ (prefixWord ++ tailWord_1837962).sum := by decide
  have hdescent : baseEnd_1837962 < baseStart_1837962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1837962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838055 : List Nat := [1, 1, 5, 2, 2, 1, 2, 4, 5]
def baseStart_1838055 : Nat := 118140960795 + 1838055 * 2 ^ 59
def prefixEnd_1838055 : Nat := 4983230072969 + 3 ^ 40 * 1838055 * 2
def baseEnd_1838055 : Nat := 104867298266656815006605

theorem tailTrace_1838055 : CollatzResearch.WordTrace tailWord_1838055 prefixEnd_1838055 104867298266656815006605 := by
  unfold tailWord_1838055
  simp only [CollatzResearch.WordTrace]
  refine ⟨67039373356048124647075619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44692915570698749764717079 67039373356048124647075619)
  ·
    refine ⟨100559060034072186970613429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67039373356048124647075619 100559060034072186970613429)
    ·
      refine ⟨9427411878194267528495009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100559060034072186970613429 9427411878194267528495009)
      ·
        refine ⟨7070558908645700646371257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9427411878194267528495009 7070558908645700646371257)
        ·
          refine ⟨5302919181484275484778443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7070558908645700646371257 5302919181484275484778443)
          ·
            refine ⟨7954378772226413227167665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5302919181484275484778443 7954378772226413227167665)
            ·
              refine ⟨5965784079169809920375749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7954378772226413227167665 5965784079169809920375749)
              ·
                refine ⟨1118584514844339360070453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5965784079169809920375749 1118584514844339360070453)
                ·
                  refine ⟨104867298266656815006605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1118584514844339360070453 104867298266656815006605)
                  ·
                    rfl

theorem cell23_1838055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 4, 5].length) (baseStart_1838055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838055 prefixEnd_1838055 := by exact prefixLift 1838055
  have htrace : WordTrace (prefixWord ++ tailWord_1838055) baseStart_1838055 baseEnd_1838055 := by
    simpa [prefixWord, tailWord_1838055, baseEnd_1838055] using wordTrace_append hprefix tailTrace_1838055
  have hstable : (prefixWord ++ tailWord_1838055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838055).length < 2 ^ (prefixWord ++ tailWord_1838055).sum := by decide
  have hdescent : baseEnd_1838055 < baseStart_1838055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838066 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 1, 4, 2]
def baseStart_1838066 : Nat := 118140960795 + 1838066 * 2 ^ 59
def prefixEnd_1838066 : Nat := 4983230072969 + 3 ^ 40 * 1838066 * 2
def baseEnd_1838066 : Nat := 943811332687110792021895

theorem tailTrace_1838066 : CollatzResearch.WordTrace tailWord_1838066 prefixEnd_1838066 943811332687110792021895 := by
  unfold tailWord_1838066
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759943639752068381431513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44693183039338849017150701 16759943639752068381431513)
  ·
    refine ⟨12569957729814051286073635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16759943639752068381431513 12569957729814051286073635)
    ·
      refine ⟨18854936594721076929110453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12569957729814051286073635 18854936594721076929110453)
      ·
        refine ⟨1767650305755100962104105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18854936594721076929110453 1767650305755100962104105)
        ·
          refine ⟨1325737729316325721578079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767650305755100962104105 1325737729316325721578079)
          ·
            refine ⟨1988606593974488582367119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325737729316325721578079 1988606593974488582367119)
            ·
              refine ⟨2982909890961732873550679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988606593974488582367119 2982909890961732873550679)
              ·
                refine ⟨4474364836442599310326019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982909890961732873550679 4474364836442599310326019)
                ·
                  refine ⟨6711547254663898965489029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474364836442599310326019 6711547254663898965489029)
                  ·
                    refine ⟨1258415110249481056029193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6711547254663898965489029 1258415110249481056029193)
                    ·
                      refine ⟨943811332687110792021895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1258415110249481056029193 943811332687110792021895)
                      ·
                        rfl

theorem cell23_1838066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_1838066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838066 prefixEnd_1838066 := by exact prefixLift 1838066
  have htrace : WordTrace (prefixWord ++ tailWord_1838066) baseStart_1838066 baseEnd_1838066 := by
    simpa [prefixWord, tailWord_1838066, baseEnd_1838066] using wordTrace_append hprefix tailTrace_1838066
  have hstable : (prefixWord ++ tailWord_1838066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838066).length < 2 ^ (prefixWord ++ tailWord_1838066).sum := by decide
  have hdescent : baseEnd_1838066 < baseStart_1838066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838088 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 1, 3, 4]
def baseStart_1838088 : Nat := 118140960795 + 1838088 * 2 ^ 59
def prefixEnd_1838088 : Nat := 4983230072969 + 3 ^ 40 * 1838088 * 2
def baseEnd_1838088 : Nat := 943822629261509705946793

theorem tailTrace_1838088 : CollatzResearch.WordTrace tailWord_1838088 prefixEnd_1838088 943822629261509705946793 := by
  unfold tailWord_1838088
  simp only [CollatzResearch.WordTrace]
  refine ⟨33520288482464285641513459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44693717976619047522017945 33520288482464285641513459)
  ·
    refine ⟨50280432723696428462270189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33520288482464285641513459 50280432723696428462270189)
    ·
      refine ⟨18855162271386160673351321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50280432723696428462270189 18855162271386160673351321)
      ·
        refine ⟨14141371703539620505013491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18855162271386160673351321 14141371703539620505013491)
        ·
          refine ⟨21212057555309430757520237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14141371703539620505013491 21212057555309430757520237)
          ·
            refine ⟨7954521583241036534070089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21212057555309430757520237 7954521583241036534070089)
            ·
              refine ⟨5965891187430777400552567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7954521583241036534070089 5965891187430777400552567)
              ·
                refine ⟨8948836781146166100828851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5965891187430777400552567 8948836781146166100828851)
                ·
                  refine ⟨13423255171719249151243277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8948836781146166100828851 13423255171719249151243277)
                  ·
                    refine ⟨5033720689394718431716229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13423255171719249151243277 5033720689394718431716229)
                    ·
                      refine ⟨943822629261509705946793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5033720689394718431716229 943822629261509705946793)
                      ·
                        rfl

theorem cell23_1838088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_1838088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838088 prefixEnd_1838088 := by exact prefixLift 1838088
  have htrace : WordTrace (prefixWord ++ tailWord_1838088) baseStart_1838088 baseEnd_1838088 := by
    simpa [prefixWord, tailWord_1838088, baseEnd_1838088] using wordTrace_append hprefix tailTrace_1838088
  have hstable : (prefixWord ++ tailWord_1838088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838088).length < 2 ^ (prefixWord ++ tailWord_1838088).sum := by decide
  have hdescent : baseEnd_1838088 < baseStart_1838088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838115 : List Nat := [1, 1, 1, 4, 3, 2, 3, 1, 3, 4]
def baseStart_1838115 : Nat := 118140960795 + 1838115 * 2 ^ 59
def prefixEnd_1838115 : Nat := 4983230072969 + 3 ^ 40 * 1838115 * 2
def baseEnd_1838115 : Nat := 314612164413060366769723

theorem tailTrace_1838115 : CollatzResearch.WordTrace tailWord_1838115 prefixEnd_1838115 314612164413060366769723 := by
  unfold tailWord_1838115
  simp only [CollatzResearch.WordTrace]
  refine ⟨67041561735830754894259799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44694374490553836596173199 67041561735830754894259799)
  ·
    refine ⟨100562342603746132341389699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67041561735830754894259799 100562342603746132341389699)
    ·
      refine ⟨150843513905619198512084549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100562342603746132341389699 150843513905619198512084549)
      ·
        refine ⟨28283158857303599721015853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150843513905619198512084549 28283158857303599721015853)
        ·
          refine ⟨10606184571488849895380945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28283158857303599721015853 10606184571488849895380945)
          ·
            refine ⟨7954638428616637421535709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10606184571488849895380945 7954638428616637421535709)
            ·
              refine ⟨2982989410731239033075891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7954638428616637421535709 2982989410731239033075891)
              ·
                refine ⟨4474484116096858549613837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2982989410731239033075891 4474484116096858549613837)
                ·
                  refine ⟨1677931543536321956105189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4474484116096858549613837 1677931543536321956105189)
                  ·
                    refine ⟨314612164413060366769723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1677931543536321956105189 314612164413060366769723)
                    ·
                      rfl

theorem cell23_1838115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 1, 3, 4].length) (baseStart_1838115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838115 prefixEnd_1838115 := by exact prefixLift 1838115
  have htrace : WordTrace (prefixWord ++ tailWord_1838115) baseStart_1838115 baseEnd_1838115 := by
    simpa [prefixWord, tailWord_1838115, baseEnd_1838115] using wordTrace_append hprefix tailTrace_1838115
  have hstable : (prefixWord ++ tailWord_1838115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838115).length < 2 ^ (prefixWord ++ tailWord_1838115).sum := by decide
  have hdescent : baseEnd_1838115 < baseStart_1838115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838128 : List Nat := [2, 1, 1, 1, 2, 4, 3, 3, 6]
def baseStart_1838128 : Nat := 118140960795 + 1838128 * 2 ^ 59
def prefixEnd_1838128 : Nat := 4983230072969 + 3 ^ 40 * 1838128 * 2
def baseEnd_1838128 : Nat := 104871463165298838827401

theorem tailTrace_1838128 : CollatzResearch.WordTrace tailWord_1838128 prefixEnd_1838128 104871463165298838827401 := by
  unfold tailWord_1838128
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521017942391829057241519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44694690589855772076322025 33521017942391829057241519)
  ·
    refine ⟨50281526913587743585862279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33521017942391829057241519 50281526913587743585862279)
    ·
      refine ⟨75422290370381615378793419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50281526913587743585862279 75422290370381615378793419)
      ·
        refine ⟨113133435555572423068190129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75422290370381615378793419 113133435555572423068190129)
        ·
          refine ⟨84850076666679317301142597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113133435555572423068190129 84850076666679317301142597)
          ·
            refine ⟨15909389375002371993964237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84850076666679317301142597 15909389375002371993964237)
            ·
              refine ⟨5966021015625889497736589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15909389375002371993964237 5966021015625889497736589)
              ·
                refine ⟨2237257880859708561651221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5966021015625889497736589 2237257880859708561651221)
                ·
                  refine ⟨104871463165298838827401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2237257880859708561651221 104871463165298838827401)
                  ·
                    rfl

theorem cell23_1838128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 6].length) (baseStart_1838128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838128 prefixEnd_1838128 := by exact prefixLift 1838128
  have htrace : WordTrace (prefixWord ++ tailWord_1838128) baseStart_1838128 baseEnd_1838128 := by
    simpa [prefixWord, tailWord_1838128, baseEnd_1838128] using wordTrace_append hprefix tailTrace_1838128
  have hstable : (prefixWord ++ tailWord_1838128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838128).length < 2 ^ (prefixWord ++ tailWord_1838128).sum := by decide
  have hdescent : baseEnd_1838128 < baseStart_1838128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838138 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3]
def baseStart_1838138 : Nat := 118140960795 + 1838138 * 2 ^ 59
def prefixEnd_1838138 : Nat := 4983230072969 + 3 ^ 40 * 1838138 * 2
def baseEnd_1838138 : Nat := 943848303294234510321563

theorem tailTrace_1838138 : CollatzResearch.WordTrace tailWord_1838138 prefixEnd_1838138 943848303294234510321563 := by
  unfold tailWord_1838138
  simp only [CollatzResearch.WordTrace]
  refine ⟨16760600153686857455586767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44694933743164953214898045 16760600153686857455586767)
  ·
    refine ⟨25140900230530286183380151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16760600153686857455586767 25140900230530286183380151)
    ·
      refine ⟨37711350345795429275070227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25140900230530286183380151 37711350345795429275070227)
      ·
        refine ⟨56567025518693143912605341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37711350345795429275070227 56567025518693143912605341)
        ·
          refine ⟨21212634569509928967227003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56567025518693143912605341 21212634569509928967227003)
          ·
            refine ⟨31818951854264893450840505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21212634569509928967227003 31818951854264893450840505)
            ·
              refine ⟨23864213890698670088130379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31818951854264893450840505 23864213890698670088130379)
              ·
                refine ⟨35796320836048005132195569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23864213890698670088130379 35796320836048005132195569)
                ·
                  refine ⟨26847240627036003849146677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35796320836048005132195569 26847240627036003849146677)
                  ·
                    refine ⟨2516928808784625360857501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26847240627036003849146677 2516928808784625360857501)
                    ·
                      refine ⟨943848303294234510321563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2516928808784625360857501 943848303294234510321563)
                      ·
                        rfl

theorem cell23_1838138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3].length) (baseStart_1838138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838138 prefixEnd_1838138 := by exact prefixLift 1838138
  have htrace : WordTrace (prefixWord ++ tailWord_1838138) baseStart_1838138 baseEnd_1838138 := by
    simpa [prefixWord, tailWord_1838138, baseEnd_1838138] using wordTrace_append hprefix tailTrace_1838138
  have hstable : (prefixWord ++ tailWord_1838138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838138).length < 2 ^ (prefixWord ++ tailWord_1838138).sum := by decide
  have hdescent : baseEnd_1838138 < baseStart_1838138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838142 : List Nat := [4, 2, 1, 3, 1, 1, 1, 3, 2, 2, 3]
def baseStart_1838142 : Nat := 118140960795 + 1838142 * 2 ^ 59
def prefixEnd_1838142 : Nat := 4983230072969 + 3 ^ 40 * 1838142 * 2
def baseEnd_1838142 : Nat := 943850357216852494671545

theorem tailTrace_1838142 : CollatzResearch.WordTrace tailWord_1838142 prefixEnd_1838142 943850357216852494671545 := by
  unfold tailWord_1838142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380318313341617313186585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44695031004488625670328453 8380318313341617313186585)
  ·
    refine ⟨6285238735006212984889939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8380318313341617313186585 6285238735006212984889939)
    ·
      refine ⟨9427858102509319477334909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285238735006212984889939 9427858102509319477334909)
      ·
        refine ⟨3535446788440994804000591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9427858102509319477334909 3535446788440994804000591)
        ·
          refine ⟨5303170182661492206000887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3535446788440994804000591 5303170182661492206000887)
          ·
            refine ⟨7954755273992238309001331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5303170182661492206000887 7954755273992238309001331)
            ·
              refine ⟨11932132910988357463501997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7954755273992238309001331 11932132910988357463501997)
              ·
                refine ⟨4474549841620634048813249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932132910988357463501997 4474549841620634048813249)
                ·
                  refine ⟨3355912381215475536609937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4474549841620634048813249 3355912381215475536609937)
                  ·
                    refine ⟨2516934285911606652457453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3355912381215475536609937 2516934285911606652457453)
                    ·
                      refine ⟨943850357216852494671545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2516934285911606652457453 943850357216852494671545)
                      ·
                        rfl

theorem cell23_1838142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_1838142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838142 prefixEnd_1838142 := by exact prefixLift 1838142
  have htrace : WordTrace (prefixWord ++ tailWord_1838142) baseStart_1838142 baseEnd_1838142 := by
    simpa [prefixWord, tailWord_1838142, baseEnd_1838142] using wordTrace_append hprefix tailTrace_1838142
  have hstable : (prefixWord ++ tailWord_1838142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838142).length < 2 ^ (prefixWord ++ tailWord_1838142).sum := by decide
  have hdescent : baseEnd_1838142 < baseStart_1838142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838172 : List Nat := [2, 2, 4, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_1838172 : Nat := 118140960795 + 1838172 * 2 ^ 59
def prefixEnd_1838172 : Nat := 4983230072969 + 3 ^ 40 * 1838172 * 2
def baseEnd_1838172 : Nat := 943865761636487377296407

theorem tailTrace_1838172 : CollatzResearch.WordTrace tailWord_1838172 prefixEnd_1838172 943865761636487377296407 := by
  unfold tailWord_1838172
  simp only [CollatzResearch.WordTrace]
  refine ⟨33521820348312126814542385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44695760464416169086056513 33521820348312126814542385)
  ·
    refine ⟨25141365261234095110906789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33521820348312126814542385 25141365261234095110906789)
    ·
      refine ⟨4714005986481392833295023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25141365261234095110906789 4714005986481392833295023)
      ·
        refine ⟨7071008979722089249942535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714005986481392833295023 7071008979722089249942535)
        ·
          refine ⟨10606513469583133874913803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071008979722089249942535 10606513469583133874913803)
          ·
            refine ⟨15909770204374700812370705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606513469583133874913803 15909770204374700812370705)
            ·
              refine ⟨11932327653281025609278029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15909770204374700812370705 11932327653281025609278029)
              ·
                refine ⟨4474622869980384603479261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11932327653281025609278029 4474622869980384603479261)
                ·
                  refine ⟨1677983576242644226304723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4474622869980384603479261 1677983576242644226304723)
                  ·
                    refine ⟨2516975364363966339457085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1677983576242644226304723 2516975364363966339457085)
                    ·
                      refine ⟨943865761636487377296407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2516975364363966339457085 943865761636487377296407)
                      ·
                        rfl

theorem cell23_1838172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_1838172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838172 prefixEnd_1838172 := by exact prefixLift 1838172
  have htrace : WordTrace (prefixWord ++ tailWord_1838172) baseStart_1838172 baseEnd_1838172 := by
    simpa [prefixWord, tailWord_1838172, baseEnd_1838172] using wordTrace_append hprefix tailTrace_1838172
  have hstable : (prefixWord ++ tailWord_1838172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838172).length < 2 ^ (prefixWord ++ tailWord_1838172).sum := by decide
  have hdescent : baseEnd_1838172 < baseStart_1838172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838205 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1838205 : Nat := 118140960795 + 1838205 * 2 ^ 59
def prefixEnd_1838205 : Nat := 4983230072969 + 3 ^ 40 * 1838205 * 2
def baseEnd_1838205 : Nat := 314627568832695249394585

theorem tailTrace_1838205 : CollatzResearch.WordTrace tailWord_1838205 prefixEnd_1838205 314627568832695249394585 := by
  unfold tailWord_1838205
  simp only [CollatzResearch.WordTrace]
  refine ⟨67044844305504700265036069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44696562870336466843357379 67044844305504700265036069)
  ·
    refine ⟨12570908307282131299694263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67044844305504700265036069 12570908307282131299694263)
    ·
      refine ⟨18856362460923196949541395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12570908307282131299694263 18856362460923196949541395)
      ·
        refine ⟨28284543691384795424312093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18856362460923196949541395 28284543691384795424312093)
        ·
          refine ⟨10606703884269298284117035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28284543691384795424312093 10606703884269298284117035)
          ·
            refine ⟨15910055826403947426175553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606703884269298284117035 15910055826403947426175553)
            ·
              refine ⟨11932541869802960569631665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15910055826403947426175553 11932541869802960569631665)
              ·
                refine ⟨8949406402352220427223749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11932541869802960569631665 8949406402352220427223749)
                ·
                  refine ⟨1678013700441041330104453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8949406402352220427223749 1678013700441041330104453)
                  ·
                    refine ⟨314627568832695249394585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678013700441041330104453 314627568832695249394585)
                    ·
                      rfl

theorem cell23_1838205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1838205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838205 prefixEnd_1838205 := by exact prefixLift 1838205
  have htrace : WordTrace (prefixWord ++ tailWord_1838205) baseStart_1838205 baseEnd_1838205 := by
    simpa [prefixWord, tailWord_1838205, baseEnd_1838205] using wordTrace_append hprefix tailTrace_1838205
  have hstable : (prefixWord ++ tailWord_1838205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838205).length < 2 ^ (prefixWord ++ tailWord_1838205).sum := by decide
  have hdescent : baseEnd_1838205 < baseStart_1838205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838209 : List Nat := [1, 2, 4, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1838209 : Nat := 118140960795 + 1838209 * 2 ^ 59
def prefixEnd_1838209 : Nat := 4983230072969 + 3 ^ 40 * 1838209 * 2
def baseEnd_1838209 : Nat := 314628253473567910844579

theorem tailTrace_1838209 : CollatzResearch.WordTrace tailWord_1838209 prefixEnd_1838209 314628253473567910844579 := by
  unfold tailWord_1838209
  simp only [CollatzResearch.WordTrace]
  refine ⟨67044990197490208948181681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44696660131660139298787787 67044990197490208948181681)
  ·
    refine ⟨50283742648117656711136261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67044990197490208948181681 50283742648117656711136261)
    ·
      refine ⟨9428201746522060633338049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50283742648117656711136261 9428201746522060633338049)
      ·
        refine ⟨7071151309891545475003537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9428201746522060633338049 7071151309891545475003537)
        ·
          refine ⟨5303363482418659106252653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7071151309891545475003537 5303363482418659106252653)
          ·
            refine ⟨1988761305906997164844745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5303363482418659106252653 1988761305906997164844745)
            ·
              refine ⟨1491570979430247873633559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988761305906997164844745 1491570979430247873633559)
              ·
                refine ⟨2237356469145371810450339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491570979430247873633559 2237356469145371810450339)
                ·
                  refine ⟨3356034703718057715675509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237356469145371810450339 3356034703718057715675509)
                  ·
                    refine ⟨314628253473567910844579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3356034703718057715675509 314628253473567910844579)
                    ·
                      rfl

theorem cell23_1838209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1838209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838209 prefixEnd_1838209 := by exact prefixLift 1838209
  have htrace : WordTrace (prefixWord ++ tailWord_1838209) baseStart_1838209 baseEnd_1838209 := by
    simpa [prefixWord, tailWord_1838209, baseEnd_1838209] using wordTrace_append hprefix tailTrace_1838209
  have hstable : (prefixWord ++ tailWord_1838209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838209).length < 2 ^ (prefixWord ++ tailWord_1838209).sum := by decide
  have hdescent : baseEnd_1838209 < baseStart_1838209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838212 : List Nat := [2, 3, 2, 1, 2, 3, 1, 3, 1, 1, 4]
def baseStart_1838212 : Nat := 118140960795 + 1838212 * 2 ^ 59
def prefixEnd_1838212 : Nat := 4983230072969 + 3 ^ 40 * 1838212 * 2
def baseEnd_1838212 : Nat := 943886300862667220796223

theorem tailTrace_1838212 : CollatzResearch.WordTrace tailWord_1838212 prefixEnd_1838212 943886300862667220796223 := by
  unfold tailWord_1838212
  simp only [CollatzResearch.WordTrace]
  refine ⟨33522549808239670230270445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44696733077652893640360593 33522549808239670230270445)
  ·
    refine ⟨12570956178089876336351417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33522549808239670230270445 12570956178089876336351417)
    ·
      refine ⟨9428217133567407252263563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12570956178089876336351417 9428217133567407252263563)
      ·
        refine ⟨14142325700351110878395345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9428217133567407252263563 14142325700351110878395345)
        ·
          refine ⟨10606744275263333158796509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14142325700351110878395345 10606744275263333158796509)
          ·
            refine ⟨3977529103223749934548691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10606744275263333158796509 3977529103223749934548691)
            ·
              refine ⟨5966293654835624901823037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977529103223749934548691 5966293654835624901823037)
              ·
                refine ⟨2237360120563359338183639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5966293654835624901823037 2237360120563359338183639)
                ·
                  refine ⟨3356040180845039007275459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237360120563359338183639 3356040180845039007275459)
                  ·
                    refine ⟨5034060271267558510913189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356040180845039007275459 5034060271267558510913189)
                    ·
                      refine ⟨943886300862667220796223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5034060271267558510913189 943886300862667220796223)
                      ·
                        rfl

theorem cell23_1838212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 1, 1, 4].length) (baseStart_1838212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838212 prefixEnd_1838212 := by exact prefixLift 1838212
  have htrace : WordTrace (prefixWord ++ tailWord_1838212) baseStart_1838212 baseEnd_1838212 := by
    simpa [prefixWord, tailWord_1838212, baseEnd_1838212] using wordTrace_append hprefix tailTrace_1838212
  have hstable : (prefixWord ++ tailWord_1838212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838212).length < 2 ^ (prefixWord ++ tailWord_1838212).sum := by decide
  have hdescent : baseEnd_1838212 < baseStart_1838212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838218 : List Nat := [3, 1, 2, 3, 1, 1, 12]
def baseStart_1838218 : Nat := 118140960795 + 1838218 * 2 ^ 59
def prefixEnd_1838218 : Nat := 4983230072969 + 3 ^ 40 * 1838218 * 2
def baseEnd_1838218 : Nat := 11652955330204866633595

theorem tailTrace_1838218 : CollatzResearch.WordTrace tailWord_1838218 prefixEnd_1838218 11652955330204866633595 := by
  unfold tailWord_1838218
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761329613614400871314827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44696878969638402323506205 16761329613614400871314827)
  ·
    refine ⟨25141994420421601306972241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16761329613614400871314827 25141994420421601306972241)
    ·
      refine ⟨18856495815316200980229181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25141994420421601306972241 18856495815316200980229181)
      ·
        refine ⟨7071185930743575367585943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18856495815316200980229181 7071185930743575367585943)
        ·
          refine ⟨10606778896115363051378915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7071185930743575367585943 10606778896115363051378915)
          ·
            refine ⟨15910168344173044577068373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10606778896115363051378915 15910168344173044577068373)
            ·
              refine ⟨11652955330204866633595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 15910168344173044577068373 11652955330204866633595)
              ·
                rfl

theorem cell23_1838218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 12].length) (baseStart_1838218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838218 prefixEnd_1838218 := by exact prefixLift 1838218
  have htrace : WordTrace (prefixWord ++ tailWord_1838218) baseStart_1838218 baseEnd_1838218 := by
    simpa [prefixWord, tailWord_1838218, baseEnd_1838218] using wordTrace_append hprefix tailTrace_1838218
  have hstable : (prefixWord ++ tailWord_1838218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838218).length < 2 ^ (prefixWord ++ tailWord_1838218).sum := by decide
  have hdescent : baseEnd_1838218 < baseStart_1838218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838222 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_1838222 : Nat := 118140960795 + 1838222 * 2 ^ 59
def prefixEnd_1838222 : Nat := 4983230072969 + 3 ^ 40 * 1838222 * 2
def baseEnd_1838222 : Nat := 314630478556404060557059

theorem tailTrace_1838222 : CollatzResearch.WordTrace tailWord_1838222 prefixEnd_1838222 314630478556404060557059 := by
  unfold tailWord_1838222
  simp only [CollatzResearch.WordTrace]
  refine ⟨8380683043305389021050615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44696976230962074778936613 8380683043305389021050615)
  ·
    refine ⟨12571024564958083531575923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8380683043305389021050615 12571024564958083531575923)
    ·
      refine ⟨18856536847437125297363885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12571024564958083531575923 18856536847437125297363885)
      ·
        refine ⟨7071201317788921986511457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18856536847437125297363885 7071201317788921986511457)
        ·
          refine ⟨5303400988341691489883593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7071201317788921986511457 5303400988341691489883593)
          ·
            refine ⟨3977550741256268617412695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5303400988341691489883593 3977550741256268617412695)
            ·
              refine ⟨5966326111884402926119043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977550741256268617412695 5966326111884402926119043)
              ·
                refine ⟨8949489167826604389178565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5966326111884402926119043 8949489167826604389178565)
                ·
                  refine ⟨1678029218967488322970981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8949489167826604389178565 1678029218967488322970981)
                  ·
                    refine ⟨314630478556404060557059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678029218967488322970981 314630478556404060557059)
                    ·
                      rfl

theorem cell23_1838222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_1838222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838222 prefixEnd_1838222 := by exact prefixLift 1838222
  have htrace : WordTrace (prefixWord ++ tailWord_1838222) baseStart_1838222 baseEnd_1838222 := by
    simpa [prefixWord, tailWord_1838222, baseEnd_1838222] using wordTrace_append hprefix tailTrace_1838222
  have hstable : (prefixWord ++ tailWord_1838222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838222).length < 2 ^ (prefixWord ++ tailWord_1838222).sum := by decide
  have hdescent : baseEnd_1838222 < baseStart_1838222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838239 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 1, 6]
def baseStart_1838239 : Nat := 118140960795 + 1838239 * 2 ^ 59
def prefixEnd_1838239 : Nat := 4983230072969 + 3 ^ 40 * 1838239 * 2
def baseEnd_1838239 : Nat := 314633388280112871719533

theorem tailTrace_1838239 : CollatzResearch.WordTrace tailWord_1838239 prefixEnd_1838239 314633388280112871719533 := by
  unfold tailWord_1838239
  simp only [CollatzResearch.WordTrace]
  refine ⟨67046084387381524071773771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44697389591587682714515847 67046084387381524071773771)
  ·
    refine ⟨100569126581072286107660657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67046084387381524071773771 100569126581072286107660657)
    ·
      refine ⟨75426844935804214580745493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100569126581072286107660657 75426844935804214580745493)
      ·
        refine ⟨3535633356365822558472445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75426844935804214580745493 3535633356365822558472445)
        ·
          refine ⟨1325862508637183459427167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3535633356365822558472445 1325862508637183459427167)
          ·
            refine ⟨1988793762955775189140751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325862508637183459427167 1988793762955775189140751)
            ·
              refine ⟨2983190644433662783711127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988793762955775189140751 2983190644433662783711127)
              ·
                refine ⟨4474785966650494175566691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983190644433662783711127 4474785966650494175566691)
                ·
                  refine ⟨6712178949975741263350037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474785966650494175566691 6712178949975741263350037)
                  ·
                    refine ⟨314633388280112871719533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6712178949975741263350037 314633388280112871719533)
                    ·
                      rfl

theorem cell23_1838239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 1, 6].length) (baseStart_1838239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838239 prefixEnd_1838239 := by exact prefixLift 1838239
  have htrace : WordTrace (prefixWord ++ tailWord_1838239) baseStart_1838239 baseEnd_1838239 := by
    simpa [prefixWord, tailWord_1838239, baseEnd_1838239] using wordTrace_append hprefix tailTrace_1838239
  have hstable : (prefixWord ++ tailWord_1838239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838239).length < 2 ^ (prefixWord ++ tailWord_1838239).sum := by decide
  have hdescent : baseEnd_1838239 < baseStart_1838239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838242 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1838242 : Nat := 118140960795 + 1838242 * 2 ^ 59
def prefixEnd_1838242 : Nat := 4983230072969 + 3 ^ 40 * 1838242 * 2
def baseEnd_1838242 : Nat := 943901705282302103421085

theorem tailTrace_1838242 : CollatzResearch.WordTrace tailWord_1838242 prefixEnd_1838242 943901705282302103421085 := by
  unfold tailWord_1838242
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761548451592663896033245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44697462537580437056088653 16761548451592663896033245)
  ·
    refine ⟨6285580669347248961012467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16761548451592663896033245 6285580669347248961012467)
    ·
      refine ⟨9428371004020873441518701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6285580669347248961012467 9428371004020873441518701)
      ·
        refine ⟨3535639126507827540569513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9428371004020873441518701 3535639126507827540569513)
        ·
          refine ⟨2651729344880870655427135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535639126507827540569513 2651729344880870655427135)
          ·
            refine ⟨3977594017321305983140703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651729344880870655427135 3977594017321305983140703)
            ·
              refine ⟨5966391025981958974711055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977594017321305983140703 5966391025981958974711055)
              ·
                refine ⟨8949586538972938462066583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5966391025981958974711055 8949586538972938462066583)
                ·
                  refine ⟨13424379808459407693099875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8949586538972938462066583 13424379808459407693099875)
                  ·
                    refine ⟨20136569712689111539649813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13424379808459407693099875 20136569712689111539649813)
                    ·
                      refine ⟨943901705282302103421085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20136569712689111539649813 943901705282302103421085)
                      ·
                        rfl

theorem cell23_1838242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1838242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838242 prefixEnd_1838242 := by exact prefixLift 1838242
  have htrace : WordTrace (prefixWord ++ tailWord_1838242) baseStart_1838242 baseEnd_1838242 := by
    simpa [prefixWord, tailWord_1838242, baseEnd_1838242] using wordTrace_append hprefix tailTrace_1838242
  have hstable : (prefixWord ++ tailWord_1838242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838242).length < 2 ^ (prefixWord ++ tailWord_1838242).sum := by decide
  have hdescent : baseEnd_1838242 < baseStart_1838242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838305 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_1838305 : Nat := 118140960795 + 1838305 * 2 ^ 59
def prefixEnd_1838305 : Nat := 4983230072969 + 3 ^ 40 * 1838305 * 2
def baseEnd_1838305 : Nat := 943934054563535356933295

theorem tailTrace_1838305 : CollatzResearch.WordTrace tailWord_1838305 prefixEnd_1838305 943934054563535356933295 := by
  unfold tailWord_1838305
  simp only [CollatzResearch.WordTrace]
  refine ⟨67048491605142417343676369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44698994403428278229117579 67048491605142417343676369)
  ·
    refine ⟨50286368703856813007757277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67048491605142417343676369 50286368703856813007757277)
    ·
      refine ⟨18857388263946304877908979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50286368703856813007757277 18857388263946304877908979)
      ·
        refine ⟨28286082395919457316863469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18857388263946304877908979 28286082395919457316863469)
        ·
          refine ⟨10607280898469796493823801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28286082395919457316863469 10607280898469796493823801)
          ·
            refine ⟨7955460673852347370367851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10607280898469796493823801 7955460673852347370367851)
            ·
              refine ⟨11933191010778521055551777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955460673852347370367851 11933191010778521055551777)
              ·
                refine ⟨8949893258083890791663833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11933191010778521055551777 8949893258083890791663833)
                ·
                  refine ⟨6712419943562918093747875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8949893258083890791663833 6712419943562918093747875)
                  ·
                    refine ⟨10068629915344377140621813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6712419943562918093747875 10068629915344377140621813)
                    ·
                      refine ⟨943934054563535356933295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10068629915344377140621813 943934054563535356933295)
                      ·
                        rfl

theorem cell23_1838305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_1838305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838305 prefixEnd_1838305 := by exact prefixLift 1838305
  have htrace : WordTrace (prefixWord ++ tailWord_1838305) baseStart_1838305 baseEnd_1838305 := by
    simpa [prefixWord, tailWord_1838305, baseEnd_1838305] using wordTrace_append hprefix tailTrace_1838305
  have hstable : (prefixWord ++ tailWord_1838305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838305).length < 2 ^ (prefixWord ++ tailWord_1838305).sum := by decide
  have hdescent : baseEnd_1838305 < baseStart_1838305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838319 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 1, 4, 2]
def baseStart_1838319 : Nat := 118140960795 + 1838319 * 2 ^ 59
def prefixEnd_1838319 : Nat := 4983230072969 + 3 ^ 40 * 1838319 * 2
def baseEnd_1838319 : Nat := 943941243292698302158231

theorem tailTrace_1838319 : CollatzResearch.WordTrace tailWord_1838319 prefixEnd_1838319 943941243292698302158231 := by
  unfold tailWord_1838319
  simp only [CollatzResearch.WordTrace]
  refine ⟨67049002227091697734686011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44699334818061131823124007 67049002227091697734686011)
  ·
    refine ⟨100573503340637546602029017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67049002227091697734686011 100573503340637546602029017)
    ·
      refine ⟨75430127505478159951521763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100573503340637546602029017 75430127505478159951521763)
      ·
        refine ⟨113145191258217239927282645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75430127505478159951521763 113145191258217239927282645)
        ·
          refine ⟨2651840420114466560795687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113145191258217239927282645 2651840420114466560795687)
          ·
            refine ⟨3977760630171699841193531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651840420114466560795687 3977760630171699841193531)
            ·
              refine ⟨5966640945257549761790297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3977760630171699841193531 5966640945257549761790297)
              ·
                refine ⟨4474980708943162321342723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5966640945257549761790297 4474980708943162321342723)
                ·
                  refine ⟨6712471063414743482014085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4474980708943162321342723 6712471063414743482014085)
                  ·
                    refine ⟨1258588324390264402877641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6712471063414743482014085 1258588324390264402877641)
                    ·
                      refine ⟨943941243292698302158231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1258588324390264402877641 943941243292698302158231)
                      ·
                        rfl

theorem cell23_1838319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 4, 2].length) (baseStart_1838319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838319 prefixEnd_1838319 := by exact prefixLift 1838319
  have htrace : WordTrace (prefixWord ++ tailWord_1838319) baseStart_1838319 baseEnd_1838319 := by
    simpa [prefixWord, tailWord_1838319, baseEnd_1838319] using wordTrace_append hprefix tailTrace_1838319
  have hstable : (prefixWord ++ tailWord_1838319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838319).length < 2 ^ (prefixWord ++ tailWord_1838319).sum := by decide
  have hdescent : baseEnd_1838319 < baseStart_1838319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838412 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 1, 4, 3]
def baseStart_1838412 : Nat := 118140960795 + 1838412 * 2 ^ 59
def prefixEnd_1838412 : Nat := 4983230072969 + 3 ^ 40 * 1838412 * 2
def baseEnd_1838412 : Nat := 943988996993566438295303

theorem tailTrace_1838412 : CollatzResearch.WordTrace tailWord_1838412 prefixEnd_1838412 943988996993566438295303 := by
  unfold tailWord_1838412
  simp only [CollatzResearch.WordTrace]
  refine ⟨33526197107877387308910745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44701596143836516411880993 33526197107877387308910745)
  ·
    refine ⟨25144647830908040481683059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33526197107877387308910745 25144647830908040481683059)
    ·
      refine ⟨37716971746362060722524589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25144647830908040481683059 37716971746362060722524589)
      ·
        refine ⟨14143864404885772770946721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37716971746362060722524589 14143864404885772770946721)
        ·
          refine ⟨10607898303664329578210041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14143864404885772770946721 10607898303664329578210041)
          ·
            refine ⟨7955923727748247183657531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10607898303664329578210041 7955923727748247183657531)
            ·
              refine ⟨11933885591622370775486297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7955923727748247183657531 11933885591622370775486297)
              ·
                refine ⟨8950414193716778081614723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11933885591622370775486297 8950414193716778081614723)
                ·
                  refine ⟨13425621290575167122422085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8950414193716778081614723 13425621290575167122422085)
                  ·
                    refine ⟨2517303991982843835454141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13425621290575167122422085 2517303991982843835454141)
                    ·
                      refine ⟨943988996993566438295303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2517303991982843835454141 943988996993566438295303)
                      ·
                        rfl

theorem cell23_1838412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_1838412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838412 prefixEnd_1838412 := by exact prefixLift 1838412
  have htrace : WordTrace (prefixWord ++ tailWord_1838412) baseStart_1838412 baseEnd_1838412 := by
    simpa [prefixWord, tailWord_1838412, baseEnd_1838412] using wordTrace_append hprefix tailTrace_1838412
  have hstable : (prefixWord ++ tailWord_1838412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838412).length < 2 ^ (prefixWord ++ tailWord_1838412).sum := by decide
  have hdescent : baseEnd_1838412 < baseStart_1838412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838436 : List Nat := [2, 3, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_1838436 : Nat := 118140960795 + 1838436 * 2 ^ 59
def prefixEnd_1838436 : Nat := 4983230072969 + 3 ^ 40 * 1838436 * 2
def baseEnd_1838436 : Nat := 314667106843091448131731

theorem tailTrace_1838436 : CollatzResearch.WordTrace tailWord_1838436 prefixEnd_1838436 314667106843091448131731 := by
  unfold tailWord_1838436
  simp only [CollatzResearch.WordTrace]
  refine ⟨33526634783833913358347581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44702179711778551144463441 33526634783833913358347581)
  ·
    refine ⟨12572488043937717509380343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33526634783833913358347581 12572488043937717509380343)
    ·
      refine ⟨18858732065906576264070515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12572488043937717509380343 18858732065906576264070515)
      ·
        refine ⟨28288098098859864396105773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18858732065906576264070515 28288098098859864396105773)
        ·
          refine ⟨10608036787072449148539665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28288098098859864396105773 10608036787072449148539665)
          ·
            refine ⟨7956027590304336861404749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608036787072449148539665 7956027590304336861404749)
            ·
              refine ⟨2983510346364126323026781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7956027590304336861404749 2983510346364126323026781)
              ·
                refine ⟨1118816379886547371135043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2983510346364126323026781 1118816379886547371135043)
                ·
                  refine ⟨1678224569829821056702565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118816379886547371135043 1678224569829821056702565)
                  ·
                    refine ⟨314667106843091448131731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678224569829821056702565 314667106843091448131731)
                    ·
                      rfl

theorem cell23_1838436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_1838436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838436 prefixEnd_1838436 := by exact prefixLift 1838436
  have htrace : WordTrace (prefixWord ++ tailWord_1838436) baseStart_1838436 baseEnd_1838436 := by
    simpa [prefixWord, tailWord_1838436, baseEnd_1838436] using wordTrace_append hprefix tailTrace_1838436
  have hstable : (prefixWord ++ tailWord_1838436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838436).length < 2 ^ (prefixWord ++ tailWord_1838436).sum := by decide
  have hdescent : baseEnd_1838436 < baseStart_1838436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838453 : List Nat := [1, 3, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1838453 : Nat := 118140960795 + 1838453 * 2 ^ 59
def prefixEnd_1838453 : Nat := 4983230072969 + 3 ^ 40 * 1838453 * 2
def baseEnd_1838453 : Nat := 314670016566800259294205

theorem tailTrace_1838453 : CollatzResearch.WordTrace tailWord_1838453 prefixEnd_1838453 314670016566800259294205 := by
  unfold tailWord_1838453
  simp only [CollatzResearch.WordTrace]
  refine ⟨67053889608606238620064013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44702593072404159080042675 67053889608606238620064013)
  ·
    refine ⟨25145208603227339482524005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67053889608606238620064013 25145208603227339482524005)
    ·
      refine ⟨4714726613105126152973251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25145208603227339482524005 4714726613105126152973251)
      ·
        refine ⟨7072089919657689229459877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714726613105126152973251 7072089919657689229459877)
        ·
          refine ⟨1326016859935816730523727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7072089919657689229459877 1326016859935816730523727)
          ·
            refine ⟨1989025289903725095785591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326016859935816730523727 1989025289903725095785591)
            ·
              refine ⟨2983537934855587643678387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989025289903725095785591 2983537934855587643678387)
              ·
                refine ⟨4475306902283381465517581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2983537934855587643678387 4475306902283381465517581)
                ·
                  refine ⟨1678240088356268049569093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4475306902283381465517581 1678240088356268049569093)
                  ·
                    refine ⟨314670016566800259294205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678240088356268049569093 314670016566800259294205)
                    ·
                      rfl

theorem cell23_1838453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1838453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838453 prefixEnd_1838453 := by exact prefixLift 1838453
  have htrace : WordTrace (prefixWord ++ tailWord_1838453) baseStart_1838453 baseEnd_1838453 := by
    simpa [prefixWord, tailWord_1838453, baseEnd_1838453] using wordTrace_append hprefix tailTrace_1838453
  have hstable : (prefixWord ++ tailWord_1838453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838453).length < 2 ^ (prefixWord ++ tailWord_1838453).sum := by decide
  have hdescent : baseEnd_1838453 < baseStart_1838453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838466 : List Nat := [3, 4, 2, 1, 1, 2, 1, 3, 6]
def baseStart_1838466 : Nat := 118140960795 + 1838466 * 2 ^ 59
def prefixEnd_1838466 : Nat := 4983230072969 + 3 ^ 40 * 1838466 * 2
def baseEnd_1838466 : Nat := 104890747216545469668895

theorem tailTrace_1838466 : CollatzResearch.WordTrace tailWord_1838466 prefixEnd_1838466 104890747216545469668895 := by
  unfold tailWord_1838466
  simp only [CollatzResearch.WordTrace]
  refine ⟨16763590939389785460071813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44702909171706094560191501 16763590939389785460071813)
  ·
    refine ⟨3143173301135584773763465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16763590939389785460071813 3143173301135584773763465)
    ·
      refine ⟨2357379975851688580322599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3143173301135584773763465 2357379975851688580322599)
      ·
        refine ⟨3536069963777532870483899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357379975851688580322599 3536069963777532870483899)
        ·
          refine ⟨5304104945666299305725849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536069963777532870483899 5304104945666299305725849)
          ·
            refine ⟨3978078709249724479294387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5304104945666299305725849 3978078709249724479294387)
            ·
              refine ⟨5967118063874586718941581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978078709249724479294387 5967118063874586718941581)
              ·
                refine ⟨2237669273952970019603093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5967118063874586718941581 2237669273952970019603093)
                ·
                  refine ⟨104890747216545469668895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2237669273952970019603093 104890747216545469668895)
                  ·
                    rfl

theorem cell23_1838466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_1838466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838466 prefixEnd_1838466 := by exact prefixLift 1838466
  have htrace : WordTrace (prefixWord ++ tailWord_1838466) baseStart_1838466 baseEnd_1838466 := by
    simpa [prefixWord, tailWord_1838466, baseEnd_1838466] using wordTrace_append hprefix tailTrace_1838466
  have hstable : (prefixWord ++ tailWord_1838466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838466).length < 2 ^ (prefixWord ++ tailWord_1838466).sum := by decide
  have hdescent : baseEnd_1838466 < baseStart_1838466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838549 : List Nat := [1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1838549 : Nat := 118140960795 + 1838549 * 2 ^ 59
def prefixEnd_1838549 : Nat := 4983230072969 + 3 ^ 40 * 1838549 * 2
def baseEnd_1838549 : Nat := 944059343843232402282173

theorem tailTrace_1838549 : CollatzResearch.WordTrace tailWord_1838549 prefixEnd_1838549 944059343843232402282173 := by
  unfold tailWord_1838549
  simp only [CollatzResearch.WordTrace]
  refine ⟨67057391016258447015558701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44704927344172298010372467 67057391016258447015558701)
  ·
    refine ⟨25146521631096917630834513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67057391016258447015558701 25146521631096917630834513)
    ·
      refine ⟨18859891223322688223125885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25146521631096917630834513 18859891223322688223125885)
      ·
        refine ⟨7072459208746008083672207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18859891223322688223125885 7072459208746008083672207)
        ·
          refine ⟨10608688813119012125508311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072459208746008083672207 10608688813119012125508311)
          ·
            refine ⟨15913033219678518188262467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10608688813119012125508311 15913033219678518188262467)
            ·
              refine ⟨23869549829517777282393701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15913033219678518188262467 23869549829517777282393701)
              ·
                refine ⟨4475540593034583240448819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23869549829517777282393701 4475540593034583240448819)
                ·
                  refine ⟨6713310889551874860673229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4475540593034583240448819 6713310889551874860673229)
                  ·
                    refine ⟨2517491583581953072752461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6713310889551874860673229 2517491583581953072752461)
                    ·
                      refine ⟨944059343843232402282173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2517491583581953072752461 944059343843232402282173)
                      ·
                        rfl

theorem cell23_1838549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1838549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838549 prefixEnd_1838549 := by exact prefixLift 1838549
  have htrace : WordTrace (prefixWord ++ tailWord_1838549) baseStart_1838549 baseEnd_1838549 := by
    simpa [prefixWord, tailWord_1838549, baseEnd_1838549] using wordTrace_append hprefix tailTrace_1838549
  have hstable : (prefixWord ++ tailWord_1838549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838549).length < 2 ^ (prefixWord ++ tailWord_1838549).sum := by decide
  have hdescent : baseEnd_1838549 < baseStart_1838549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838550 : List Nat := [5, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_1838550 : Nat := 118140960795 + 1838550 * 2 ^ 59
def prefixEnd_1838550 : Nat := 4983230072969 + 3 ^ 40 * 1838550 * 2
def baseEnd_1838550 : Nat := 944059857323886898369669

theorem tailTrace_1838550 : CollatzResearch.WordTrace tailWord_1838550 prefixEnd_1838550 944059857323886898369669 := by
  unfold tailWord_1838550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191089218078426511646569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44704951659503216124230069 4191089218078426511646569)
  ·
    refine ⟨3143316913558819883734927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4191089218078426511646569 3143316913558819883734927)
    ·
      refine ⟨4714975370338229825602391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3143316913558819883734927 4714975370338229825602391)
      ·
        refine ⟨7072463055507344738403587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714975370338229825602391 7072463055507344738403587)
        ·
          refine ⟨10608694583261017107605381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072463055507344738403587 10608694583261017107605381)
          ·
            refine ⟨1989130234361440707676009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10608694583261017107605381 1989130234361440707676009)
            ·
              refine ⟨1491847675771080530757007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989130234361440707676009 1491847675771080530757007)
              ·
                refine ⟨2237771513656620796135511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491847675771080530757007 2237771513656620796135511)
                ·
                  refine ⟨3356657270484931194203267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237771513656620796135511 3356657270484931194203267)
                  ·
                    refine ⟨5034985905727396791304901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3356657270484931194203267 5034985905727396791304901)
                    ·
                      refine ⟨944059857323886898369669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5034985905727396791304901 944059857323886898369669)
                      ·
                        rfl

theorem cell23_1838550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_1838550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838550 prefixEnd_1838550 := by exact prefixLift 1838550
  have htrace : WordTrace (prefixWord ++ tailWord_1838550) baseStart_1838550 baseEnd_1838550 := by
    simpa [prefixWord, tailWord_1838550, baseEnd_1838550] using wordTrace_append hprefix tailTrace_1838550
  have hstable : (prefixWord ++ tailWord_1838550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838550).length < 2 ^ (prefixWord ++ tailWord_1838550).sum := by decide
  have hdescent : baseEnd_1838550 < baseStart_1838550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838553 : List Nat := [1, 2, 1, 2, 4, 4, 2, 1, 1, 2, 3]
def baseStart_1838553 : Nat := 118140960795 + 1838553 * 2 ^ 59
def prefixEnd_1838553 : Nat := 4983230072969 + 3 ^ 40 * 1838553 * 2
def baseEnd_1838553 : Nat := 944061397765850386632155

theorem tailTrace_1838553 : CollatzResearch.WordTrace tailWord_1838553 prefixEnd_1838553 944061397765850386632155 := by
  unfold tailWord_1838553
  simp only [CollatzResearch.WordTrace]
  refine ⟨67057536908243955698704313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44705024605495970465802875 67057536908243955698704313)
  ·
    refine ⟨50293152681182966774028235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67057536908243955698704313 50293152681182966774028235)
    ·
      refine ⟨75439729021774450161042353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50293152681182966774028235 75439729021774450161042353)
      ·
        refine ⟨56579796766330837620781765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75439729021774450161042353 56579796766330837620781765)
        ·
          refine ⟨10608711893687032053896581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56579796766330837620781765 10608711893687032053896581)
          ·
            refine ⟨1989133480066318510105609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10608711893687032053896581 1989133480066318510105609)
            ·
              refine ⟨1491850110049738882579207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989133480066318510105609 1491850110049738882579207)
              ·
                refine ⟨2237775165074608323868811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491850110049738882579207 2237775165074608323868811)
                ·
                  refine ⟨3356662747611912485803217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2237775165074608323868811 3356662747611912485803217)
                  ·
                    refine ⟨2517497060708934364352413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3356662747611912485803217 2517497060708934364352413)
                    ·
                      refine ⟨944061397765850386632155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2517497060708934364352413 944061397765850386632155)
                      ·
                        rfl

theorem cell23_1838553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 2, 1, 1, 2, 3].length) (baseStart_1838553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838553 prefixEnd_1838553 := by exact prefixLift 1838553
  have htrace : WordTrace (prefixWord ++ tailWord_1838553) baseStart_1838553 baseEnd_1838553 := by
    simpa [prefixWord, tailWord_1838553, baseEnd_1838553] using wordTrace_append hprefix tailTrace_1838553
  have hstable : (prefixWord ++ tailWord_1838553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838553).length < 2 ^ (prefixWord ++ tailWord_1838553).sum := by decide
  have hdescent : baseEnd_1838553 < baseStart_1838553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838572 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 4]
def baseStart_1838572 : Nat := 118140960795 + 1838572 * 2 ^ 59
def prefixEnd_1838572 : Nat := 4983230072969 + 3 ^ 40 * 1838572 * 2
def baseEnd_1838572 : Nat := 944071153898285812294567

theorem tailTrace_1838572 : CollatzResearch.WordTrace tailWord_1838572 prefixEnd_1838572 944071153898285812294567 := by
  unfold tailWord_1838572
  simp only [CollatzResearch.WordTrace]
  refine ⟨33529114947587560971822985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44705486596783414629097313 33529114947587560971822985)
  ·
    refine ⟨25146836210690670728867239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33529114947587560971822985 25146836210690670728867239)
    ·
      refine ⟨37720254316036006093300859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25146836210690670728867239 37720254316036006093300859)
      ·
        refine ⟨56580381474054009139951289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37720254316036006093300859 56580381474054009139951289)
        ·
          refine ⟨42435286105540506854963467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56580381474054009139951289 42435286105540506854963467)
          ·
            refine ⟨63652929158310760282445201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42435286105540506854963467 63652929158310760282445201)
            ·
              refine ⟨47739696868733070211833901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63652929158310760282445201 47739696868733070211833901)
              ·
                refine ⟨17902386325774901329437713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47739696868733070211833901 17902386325774901329437713)
                ·
                  refine ⟨13426789744331175997078285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17902386325774901329437713 13426789744331175997078285)
                  ·
                    refine ⟨5035046154124190998904357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13426789744331175997078285 5035046154124190998904357)
                    ·
                      refine ⟨944071153898285812294567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5035046154124190998904357 944071153898285812294567)
                      ·
                        rfl

theorem cell23_1838572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_1838572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838572 prefixEnd_1838572 := by exact prefixLift 1838572
  have htrace : WordTrace (prefixWord ++ tailWord_1838572) baseStart_1838572 baseEnd_1838572 := by
    simpa [prefixWord, tailWord_1838572, baseEnd_1838572] using wordTrace_append hprefix tailTrace_1838572
  have hstable : (prefixWord ++ tailWord_1838572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838572).length < 2 ^ (prefixWord ++ tailWord_1838572).sum := by decide
  have hdescent : baseEnd_1838572 < baseStart_1838572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838590 : List Nat := [4, 2, 2, 3, 2, 1, 2, 7]
def baseStart_1838590 : Nat := 118140960795 + 1838590 * 2 ^ 59
def prefixEnd_1838590 : Nat := 4983230072969 + 3 ^ 40 * 1838590 * 2
def baseEnd_1838590 : Nat := 34965940612965434884055

theorem tailTrace_1838590 : CollatzResearch.WordTrace tailWord_1838590 prefixEnd_1838590 34965940612965434884055 := by
  unfold tailWord_1838590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8382360801138738877225153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44705924272739940678534149 8382360801138738877225153)
  ·
    refine ⟨6286770600854054157918865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8382360801138738877225153 6286770600854054157918865)
    ·
      refine ⟨4715077950640540618439149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6286770600854054157918865 4715077950640540618439149)
      ·
        refine ⟨1768154231490202731914681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4715077950640540618439149 1768154231490202731914681)
        ·
          refine ⟨1326115673617652048936011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768154231490202731914681 1326115673617652048936011)
          ·
            refine ⟨1989173510426478073404017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326115673617652048936011 1989173510426478073404017)
            ·
              refine ⟨1491880132819858555053013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989173510426478073404017 1491880132819858555053013)
              ·
                refine ⟨34965940612965434884055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1491880132819858555053013 34965940612965434884055)
                ·
                  rfl

theorem cell23_1838590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_1838590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838590 prefixEnd_1838590 := by exact prefixLift 1838590
  have htrace : WordTrace (prefixWord ++ tailWord_1838590) baseStart_1838590 baseEnd_1838590 := by
    simpa [prefixWord, tailWord_1838590, baseEnd_1838590] using wordTrace_append hprefix tailTrace_1838590
  have hstable : (prefixWord ++ tailWord_1838590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838590).length < 2 ^ (prefixWord ++ tailWord_1838590).sum := by decide
  have hdescent : baseEnd_1838590 < baseStart_1838590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838706 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_1838706 : Nat := 118140960795 + 1838706 * 2 ^ 59
def prefixEnd_1838706 : Nat := 4983230072969 + 3 ^ 40 * 1838706 * 2
def baseEnd_1838706 : Nat := 314713320101996096006317

theorem tailTrace_1838706 : CollatzResearch.WordTrace tailWord_1838706 prefixEnd_1838706 314713320101996096006317 := by
  unfold tailWord_1838706
  simp only [CollatzResearch.WordTrace]
  refine ⟨16765779319172415707255993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44708744851126441886015981 16765779319172415707255993)
  ·
    refine ⟨12574334489379311780441995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16765779319172415707255993 12574334489379311780441995)
    ·
      refine ⟨18861501734068967670662993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12574334489379311780441995 18861501734068967670662993)
      ·
        refine ⟨14146126300551725752997245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18861501734068967670662993 14146126300551725752997245)
        ·
          refine ⟨5304797362706897157373967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14146126300551725752997245 5304797362706897157373967)
          ·
            refine ⟨7957196044060345736060951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5304797362706897157373967 7957196044060345736060951)
            ·
              refine ⟨11935794066090518604091427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7957196044060345736060951 11935794066090518604091427)
              ·
                refine ⟨17903691099135777906137141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11935794066090518604091427 17903691099135777906137141)
                ·
                  refine ⟨1678471040543979178700357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17903691099135777906137141 1678471040543979178700357)
                  ·
                    refine ⟨314713320101996096006317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678471040543979178700357 314713320101996096006317)
                    ·
                      rfl

theorem cell23_1838706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_1838706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838706 prefixEnd_1838706 := by exact prefixLift 1838706
  have htrace : WordTrace (prefixWord ++ tailWord_1838706) baseStart_1838706 baseEnd_1838706 := by
    simpa [prefixWord, tailWord_1838706, baseEnd_1838706] using wordTrace_append hprefix tailTrace_1838706
  have hstable : (prefixWord ++ tailWord_1838706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838706).length < 2 ^ (prefixWord ++ tailWord_1838706).sum := by decide
  have hdescent : baseEnd_1838706 < baseStart_1838706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838740 : List Nat := [2, 4, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1838740 : Nat := 118140960795 + 1838740 * 2 ^ 59
def prefixEnd_1838740 : Nat := 4983230072969 + 3 ^ 40 * 1838740 * 2
def baseEnd_1838740 : Nat := 314719139549413718331265

theorem tailTrace_1838740 : CollatzResearch.WordTrace tailWord_1838740 prefixEnd_1838740 314719139549413718331265 := by
  unfold tailWord_1838740
  simp only [CollatzResearch.WordTrace]
  refine ⟨33532178679283243317880837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44709571572377657757174449 33532178679283243317880837)
  ·
    refine ⟨6287283502365608122102657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33532178679283243317880837 6287283502365608122102657)
    ·
      refine ⟨4715462626774206091576993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6287283502365608122102657 4715462626774206091576993)
      ·
        refine ⟨3536596970080654568682745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4715462626774206091576993 3536596970080654568682745)
        ·
          refine ⟨2652447727560490926512059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3536596970080654568682745 2652447727560490926512059)
          ·
            refine ⟨3978671591340736389768089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652447727560490926512059 3978671591340736389768089)
            ·
              refine ⟨2984003693505552292326067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3978671591340736389768089 2984003693505552292326067)
              ·
                refine ⟨4476005540258328438489101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984003693505552292326067 4476005540258328438489101)
                ·
                  refine ⟨1678502077596873164433413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4476005540258328438489101 1678502077596873164433413)
                  ·
                    refine ⟨314719139549413718331265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678502077596873164433413 314719139549413718331265)
                    ·
                      rfl

theorem cell23_1838740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1838740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838740 prefixEnd_1838740 := by exact prefixLift 1838740
  have htrace : WordTrace (prefixWord ++ tailWord_1838740) baseStart_1838740 baseEnd_1838740 := by
    simpa [prefixWord, tailWord_1838740, baseEnd_1838740] using wordTrace_append hprefix tailTrace_1838740
  have hstable : (prefixWord ++ tailWord_1838740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838740).length < 2 ^ (prefixWord ++ tailWord_1838740).sum := by decide
  have hdescent : baseEnd_1838740 < baseStart_1838740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838753 : List Nat := [1, 2, 3, 3, 2, 2, 3, 1, 6]
def baseStart_1838753 : Nat := 118140960795 + 1838753 * 2 ^ 59
def prefixEnd_1838753 : Nat := 4983230072969 + 3 ^ 40 * 1838753 * 2
def baseEnd_1838753 : Nat := 104907121544083289347915

theorem tailTrace_1838753 : CollatzResearch.WordTrace tailWord_1838753 prefixEnd_1838753 104907121544083289347915 := by
  unfold tailWord_1838753
  simp only [CollatzResearch.WordTrace]
  refine ⟨67064831507519389855984913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44709887671679593237323275 67064831507519389855984913)
  ·
    refine ⟨50298623630639542391988685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67064831507519389855984913 50298623630639542391988685)
    ·
      refine ⟨18861983861489828396995757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50298623630639542391988685 18861983861489828396995757)
      ·
        refine ⟨7073243948058685648873409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18861983861489828396995757 7073243948058685648873409)
        ·
          refine ⟨5304932961044014236655057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7073243948058685648873409 5304932961044014236655057)
          ·
            refine ⟨3978699720783010677491293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5304932961044014236655057 3978699720783010677491293)
            ·
              refine ⟨1492012395293629004059235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3978699720783010677491293 1492012395293629004059235)
              ·
                refine ⟨2238018592940443506088853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492012395293629004059235 2238018592940443506088853)
                ·
                  refine ⟨104907121544083289347915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2238018592940443506088853 104907121544083289347915)
                  ·
                    rfl

theorem cell23_1838753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 3, 1, 6].length) (baseStart_1838753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838753 prefixEnd_1838753 := by exact prefixLift 1838753
  have htrace : WordTrace (prefixWord ++ tailWord_1838753) baseStart_1838753 baseEnd_1838753 := by
    simpa [prefixWord, tailWord_1838753, baseEnd_1838753] using wordTrace_append hprefix tailTrace_1838753
  have hstable : (prefixWord ++ tailWord_1838753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838753).length < 2 ^ (prefixWord ++ tailWord_1838753).sum := by decide
  have hdescent : baseEnd_1838753 < baseStart_1838753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838774 : List Nat := [5, 1, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1838774 : Nat := 118140960795 + 1838774 * 2 ^ 59
def prefixEnd_1838774 : Nat := 4983230072969 + 3 ^ 40 * 1838774 * 2
def baseEnd_1838774 : Nat := 314724958996831340656213

theorem tailTrace_1838774 : CollatzResearch.WordTrace tailWord_1838774 prefixEnd_1838774 314724958996831340656213 := by
  unfold tailWord_1838774
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191599840027706902656211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 44710398293628873628332917 4191599840027706902656211)
  ·
    refine ⟨6287399760041560353984317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4191599840027706902656211 6287399760041560353984317)
    ·
      refine ⟨2357774910015585132744119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6287399760041560353984317 2357774910015585132744119)
      ·
        refine ⟨3536662365023377699116179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357774910015585132744119 3536662365023377699116179)
        ·
          refine ⟨5304993547535066548674269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536662365023377699116179 5304993547535066548674269)
          ·
            refine ⟨1989372580325649955752851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5304993547535066548674269 1989372580325649955752851)
            ·
              refine ⟨2984058870488474933629277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989372580325649955752851 2984058870488474933629277)
              ·
                refine ⟨1119022076433178100110979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2984058870488474933629277 1119022076433178100110979)
                ·
                  refine ⟨1678533114649767150166469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119022076433178100110979 1678533114649767150166469)
                  ·
                    refine ⟨314724958996831340656213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678533114649767150166469 314724958996831340656213)
                    ·
                      rfl

theorem cell23_1838774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1838774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838774 prefixEnd_1838774 := by exact prefixLift 1838774
  have htrace : WordTrace (prefixWord ++ tailWord_1838774) baseStart_1838774 baseEnd_1838774 := by
    simpa [prefixWord, tailWord_1838774, baseEnd_1838774] using wordTrace_append hprefix tailTrace_1838774
  have hstable : (prefixWord ++ tailWord_1838774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838774).length < 2 ^ (prefixWord ++ tailWord_1838774).sum := by decide
  have hdescent : baseEnd_1838774 < baseStart_1838774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838779 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 1, 6]
def baseStart_1838779 : Nat := 118140960795 + 1838779 * 2 ^ 59
def prefixEnd_1838779 : Nat := 4983230072969 + 3 ^ 40 * 1838779 * 2
def baseEnd_1838779 : Nat := 314725814797922167468705

theorem tailTrace_1838779 : CollatzResearch.WordTrace tailWord_1838779 prefixEnd_1838779 314725814797922167468705 := by
  unfold tailWord_1838779
  simp only [CollatzResearch.WordTrace]
  refine ⟨67065779805425196296431391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44710519870283464197620927 67065779805425196296431391)
  ·
    refine ⟨100598669708137794444647087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67065779805425196296431391 100598669708137794444647087)
    ·
      refine ⟨150898004562206691666970631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100598669708137794444647087 150898004562206691666970631)
      ·
        refine ⟨226347006843310037500455947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150898004562206691666970631 226347006843310037500455947)
        ·
          refine ⟨339520510264965056250683921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226347006843310037500455947 339520510264965056250683921)
          ·
            refine ⟨254640382698723792188012941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339520510264965056250683921 254640382698723792188012941)
            ·
              refine ⟨95490143512021422070504853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254640382698723792188012941 95490143512021422070504853)
              ·
                refine ⟨4476100477126004159554915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95490143512021422070504853 4476100477126004159554915)
                ·
                  refine ⟨6714150715689006239332373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476100477126004159554915 6714150715689006239332373)
                  ·
                    refine ⟨314725814797922167468705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6714150715689006239332373 314725814797922167468705)
                    ·
                      rfl

theorem cell23_1838779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 1, 6].length) (baseStart_1838779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838779 prefixEnd_1838779 := by exact prefixLift 1838779
  have htrace : WordTrace (prefixWord ++ tailWord_1838779) baseStart_1838779 baseEnd_1838779 := by
    simpa [prefixWord, tailWord_1838779, baseEnd_1838779] using wordTrace_append hprefix tailTrace_1838779
  have hstable : (prefixWord ++ tailWord_1838779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838779).length < 2 ^ (prefixWord ++ tailWord_1838779).sum := by decide
  have hdescent : baseEnd_1838779 < baseStart_1838779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838789 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 5]
def baseStart_1838789 : Nat := 118140960795 + 1838789 * 2 ^ 59
def prefixEnd_1838789 : Nat := 4983230072969 + 3 ^ 40 * 1838789 * 2
def baseEnd_1838789 : Nat := 944182579200311463281069

theorem tailTrace_1838789 : CollatzResearch.WordTrace tailWord_1838789 prefixEnd_1838789 944182579200311463281069 := by
  unfold tailWord_1838789
  simp only [CollatzResearch.WordTrace]
  refine ⟨67066144535388968004295421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44710763023592645336196947 67066144535388968004295421)
  ·
    refine ⟨25149804200770863001610783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67066144535388968004295421 25149804200770863001610783)
    ·
      refine ⟨37724706301156294502416175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25149804200770863001610783 37724706301156294502416175)
      ·
        refine ⟨56587059451734441753624263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37724706301156294502416175 56587059451734441753624263)
        ·
          refine ⟨84880589177601662630436395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56587059451734441753624263 84880589177601662630436395)
          ·
            refine ⟨127320883766402493945654593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84880589177601662630436395 127320883766402493945654593)
            ·
              refine ⟨95490662824801870459240945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127320883766402493945654593 95490662824801870459240945)
              ·
                refine ⟨71617997118601402844430709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95490662824801870459240945 71617997118601402844430709)
                ·
                  refine ⟨6714187229868881516665379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71617997118601402844430709 6714187229868881516665379)
                  ·
                    refine ⟨10071280844803322274998069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6714187229868881516665379 10071280844803322274998069)
                    ·
                      refine ⟨944182579200311463281069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10071280844803322274998069 944182579200311463281069)
                      ·
                        rfl

theorem cell23_1838789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 5].length) (baseStart_1838789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838789 prefixEnd_1838789 := by exact prefixLift 1838789
  have htrace : WordTrace (prefixWord ++ tailWord_1838789) baseStart_1838789 baseEnd_1838789 := by
    simpa [prefixWord, tailWord_1838789, baseEnd_1838789] using wordTrace_append hprefix tailTrace_1838789
  have hstable : (prefixWord ++ tailWord_1838789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838789).length < 2 ^ (prefixWord ++ tailWord_1838789).sum := by decide
  have hdescent : baseEnd_1838789 < baseStart_1838789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838797 : List Nat := [1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1838797 : Nat := 118140960795 + 1838797 * 2 ^ 59
def prefixEnd_1838797 : Nat := 4983230072969 + 3 ^ 40 * 1838797 * 2
def baseEnd_1838797 : Nat := 944186687045547431981033

theorem tailTrace_1838797 : CollatzResearch.WordTrace tailWord_1838797 prefixEnd_1838797 944186687045547431981033 := by
  unfold tailWord_1838797
  simp only [CollatzResearch.WordTrace]
  refine ⟨67066436319359985370586645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44710957546239990247057763 67066436319359985370586645)
  ·
    refine ⟨3143739202469999314246249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 67066436319359985370586645 3143739202469999314246249)
    ·
      refine ⟨2357804401852499485684687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3143739202469999314246249 2357804401852499485684687)
      ·
        refine ⟨3536706602778749228527031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2357804401852499485684687 3536706602778749228527031)
        ·
          refine ⟨5305059904168123842790547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3536706602778749228527031 5305059904168123842790547)
          ·
            refine ⟨7957589856252185764185821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5305059904168123842790547 7957589856252185764185821)
            ·
              refine ⟨2984096196094569661569683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7957589856252185764185821 2984096196094569661569683)
              ·
                refine ⟨4476144294141854492354525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984096196094569661569683 4476144294141854492354525)
                ·
                  refine ⟨1678554110303195434632947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4476144294141854492354525 1678554110303195434632947)
                  ·
                    refine ⟨2517831165454793151949421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1678554110303195434632947 2517831165454793151949421)
                    ·
                      refine ⟨944186687045547431981033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2517831165454793151949421 944186687045547431981033)
                      ·
                        rfl

theorem cell23_1838797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1838797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838797 prefixEnd_1838797 := by exact prefixLift 1838797
  have htrace : WordTrace (prefixWord ++ tailWord_1838797) baseStart_1838797 baseEnd_1838797 := by
    simpa [prefixWord, tailWord_1838797, baseEnd_1838797] using wordTrace_append hprefix tailTrace_1838797
  have hstable : (prefixWord ++ tailWord_1838797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838797).length < 2 ^ (prefixWord ++ tailWord_1838797).sum := by decide
  have hdescent : baseEnd_1838797 < baseStart_1838797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838809 : List Nat := [1, 2, 1, 2, 3, 3, 1, 10]
def baseStart_1838809 : Nat := 118140960795 + 1838809 * 2 ^ 59
def prefixEnd_1838809 : Nat := 4983230072969 + 3 ^ 40 * 1838809 * 2
def baseEnd_1838809 : Nat := 34970105511607458704851

theorem tailTrace_1838809 : CollatzResearch.WordTrace tailWord_1838809 prefixEnd_1838809 34970105511607458704851 := by
  unfold tailWord_1838809
  simp only [CollatzResearch.WordTrace]
  refine ⟨67066873995316511420023481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44711249330211007613348987 67066873995316511420023481)
  ·
    refine ⟨50300155496487383565017611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67066873995316511420023481 50300155496487383565017611)
    ·
      refine ⟨75450233244731075347526417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50300155496487383565017611 75450233244731075347526417)
      ·
        refine ⟨56587674933548306510644813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75450233244731075347526417 56587674933548306510644813)
        ·
          refine ⟨21220378100080614941491805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56587674933548306510644813 21220378100080614941491805)
          ·
            refine ⟨7957641787530230603059427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21220378100080614941491805 7957641787530230603059427)
            ·
              refine ⟨11936462681295345904589141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7957641787530230603059427 11936462681295345904589141)
              ·
                refine ⟨34970105511607458704851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11936462681295345904589141 34970105511607458704851)
                ·
                  rfl

theorem cell23_1838809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 10].length) (baseStart_1838809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838809 prefixEnd_1838809 := by exact prefixLift 1838809
  have htrace : WordTrace (prefixWord ++ tailWord_1838809) baseStart_1838809 baseEnd_1838809 := by
    simpa [prefixWord, tailWord_1838809, baseEnd_1838809] using wordTrace_append hprefix tailTrace_1838809
  have hstable : (prefixWord ++ tailWord_1838809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838809).length < 2 ^ (prefixWord ++ tailWord_1838809).sum := by decide
  have hdescent : baseEnd_1838809 < baseStart_1838809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838876 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1838876 : Nat := 118140960795 + 1838876 * 2 ^ 59
def prefixEnd_1838876 : Nat := 4983230072969 + 3 ^ 40 * 1838876 * 2
def baseEnd_1838876 : Nat := 944227252017252622893169

theorem tailTrace_1838876 : CollatzResearch.WordTrace tailWord_1838876 prefixEnd_1838876 944227252017252622893169 := by
  unfold tailWord_1838876
  simp only [CollatzResearch.WordTrace]
  refine ⟨33534658843036890931356241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44712878457382521241808321 33534658843036890931356241)
  ·
    refine ⟨25150994132277668198517181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33534658843036890931356241 25150994132277668198517181)
    ·
      refine ⟨9431622799604125574443943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25150994132277668198517181 9431622799604125574443943)
      ·
        refine ⟨14147434199406188361665915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9431622799604125574443943 14147434199406188361665915)
        ·
          refine ⟨21221151299109282542498873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14147434199406188361665915 21221151299109282542498873)
          ·
            refine ⟨15915863474331961906874155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21221151299109282542498873 15915863474331961906874155)
            ·
              refine ⟨23873795211497942860311233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15915863474331961906874155 23873795211497942860311233)
              ·
                refine ⟨17905346408623457145233425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23873795211497942860311233 17905346408623457145233425)
                ·
                  refine ⟨13429009806467592858925069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17905346408623457145233425 13429009806467592858925069)
                  ·
                    refine ⟨5035878677425347322096901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13429009806467592858925069 5035878677425347322096901)
                    ·
                      refine ⟨944227252017252622893169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5035878677425347322096901 944227252017252622893169)
                      ·
                        rfl

theorem cell23_1838876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1838876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838876 prefixEnd_1838876 := by exact prefixLift 1838876
  have htrace : WordTrace (prefixWord ++ tailWord_1838876) baseStart_1838876 baseEnd_1838876 := by
    simpa [prefixWord, tailWord_1838876, baseEnd_1838876] using wordTrace_append hprefix tailTrace_1838876
  have hstable : (prefixWord ++ tailWord_1838876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838876).length < 2 ^ (prefixWord ++ tailWord_1838876).sum := by decide
  have hdescent : baseEnd_1838876 < baseStart_1838876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838880 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 1, 3, 2]
def baseStart_1838880 : Nat := 118140960795 + 1838880 * 2 ^ 59
def prefixEnd_1838880 : Nat := 4983230072969 + 3 ^ 40 * 1838880 * 2
def baseEnd_1838880 : Nat := 944229305939870607243151

theorem tailTrace_1838880 : CollatzResearch.WordTrace tailWord_1838880 prefixEnd_1838880 944229305939870607243151 := by
  unfold tailWord_1838880
  simp only [CollatzResearch.WordTrace]
  refine ⟨33534731789029645272929047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44712975718706193697238729 33534731789029645272929047)
  ·
    refine ⟨50302097683544467909393571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33534731789029645272929047 50302097683544467909393571)
    ·
      refine ⟨75453146525316701864090357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50302097683544467909393571 75453146525316701864090357)
      ·
        refine ⟨7073732486748440799758471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75453146525316701864090357 7073732486748440799758471)
        ·
          refine ⟨10610598730122661199637707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073732486748440799758471 10610598730122661199637707)
          ·
            refine ⟨15915898095183991799456561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10610598730122661199637707 15915898095183991799456561)
            ·
              refine ⟨11936923571387993849592421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15915898095183991799456561 11936923571387993849592421)
              ·
                refine ⟨2238173169635248846798579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11936923571387993849592421 2238173169635248846798579)
                ·
                  refine ⟨3357259754452873270197869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238173169635248846798579 3357259754452873270197869)
                  ·
                    refine ⟨1258972407919827476324201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357259754452873270197869 1258972407919827476324201)
                    ·
                      refine ⟨944229305939870607243151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1258972407919827476324201 944229305939870607243151)
                      ·
                        rfl

theorem cell23_1838880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 3, 2].length) (baseStart_1838880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838880 prefixEnd_1838880 := by exact prefixLift 1838880
  have htrace : WordTrace (prefixWord ++ tailWord_1838880) baseStart_1838880 baseEnd_1838880 := by
    simpa [prefixWord, tailWord_1838880, baseEnd_1838880] using wordTrace_append hprefix tailTrace_1838880
  have hstable : (prefixWord ++ tailWord_1838880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838880).length < 2 ^ (prefixWord ++ tailWord_1838880).sum := by decide
  have hdescent : baseEnd_1838880 < baseStart_1838880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838897 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 1, 3, 2]
def baseStart_1838897 : Nat := 118140960795 + 1838897 * 2 ^ 59
def prefixEnd_1838897 : Nat := 4983230072969 + 3 ^ 40 * 1838897 * 2
def baseEnd_1838897 : Nat := 944238035110997040730573

theorem tailTrace_1838897 : CollatzResearch.WordTrace tailWord_1838897 prefixEnd_1838897 944238035110997040730573 := by
  unfold tailWord_1838897
  simp only [CollatzResearch.WordTrace]
  refine ⟨67070083618997702449226945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44713389079331801632817963 67070083618997702449226945)
  ·
    refine ⟨50302562714248276836920209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67070083618997702449226945 50302562714248276836920209)
    ·
      refine ⟨37726922035686207627690157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50302562714248276836920209 37726922035686207627690157)
      ·
        refine ⟨14147595763382327860383809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37726922035686207627690157 14147595763382327860383809)
        ·
          refine ⟨10610696822536745895287857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14147595763382327860383809 10610696822536745895287857)
          ·
            refine ⟨7958022616902559421465893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10610696822536745895287857 7958022616902559421465893)
            ·
              refine ⟨1492129240669229891524855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7958022616902559421465893 1492129240669229891524855)
              ·
                refine ⟨2238193861003844837287283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492129240669229891524855 2238193861003844837287283)
                ·
                  refine ⟨3357290791505767255930925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238193861003844837287283 3357290791505767255930925)
                  ·
                    refine ⟨1258984046814662720974097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3357290791505767255930925 1258984046814662720974097)
                    ·
                      refine ⟨944238035110997040730573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1258984046814662720974097 944238035110997040730573)
                      ·
                        rfl

theorem cell23_1838897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_1838897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838897 prefixEnd_1838897 := by exact prefixLift 1838897
  have htrace : WordTrace (prefixWord ++ tailWord_1838897) baseStart_1838897 baseEnd_1838897 := by
    simpa [prefixWord, tailWord_1838897, baseEnd_1838897] using wordTrace_append hprefix tailTrace_1838897
  have hstable : (prefixWord ++ tailWord_1838897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838897).length < 2 ^ (prefixWord ++ tailWord_1838897).sum := by decide
  have hdescent : baseEnd_1838897 < baseStart_1838897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1838993 : List Nat := [1, 2, 2, 1, 1, 1, 4, 4, 3, 4]
def baseStart_1838993 : Nat := 118140960795 + 1838993 * 2 ^ 59
def prefixEnd_1838993 : Nat := 4983230072969 + 3 ^ 40 * 1838993 * 2
def baseEnd_1838993 : Nat := 314762443084609555043377

theorem tailTrace_1838993 : CollatzResearch.WordTrace tailWord_1838993 prefixEnd_1838993 314762443084609555043377 := by
  unfold tailWord_1838993
  simp only [CollatzResearch.WordTrace]
  refine ⟨67073585026649910844721633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44715723351099940563147755 67073585026649910844721633)
  ·
    refine ⟨50305188769987433133541225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67073585026649910844721633 50305188769987433133541225)
    ·
      refine ⟨37728891577490574850155919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50305188769987433133541225 37728891577490574850155919)
      ·
        refine ⟨56593337366235862275233879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37728891577490574850155919 56593337366235862275233879)
        ·
          refine ⟨84890006049353793412850819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56593337366235862275233879 84890006049353793412850819)
          ·
            refine ⟨127335009074030690119276229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84890006049353793412850819 127335009074030690119276229)
            ·
              refine ⟨23875314201380754397364293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127335009074030690119276229 23875314201380754397364293)
              ·
                refine ⟨4476621412758891449505805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23875314201380754397364293 4476621412758891449505805)
                ·
                  refine ⟨1678733029784584293564677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4476621412758891449505805 1678733029784584293564677)
                  ·
                    refine ⟨314762443084609555043377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678733029784584293564677 314762443084609555043377)
                    ·
                      rfl

theorem cell23_1838993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_1838993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1838993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1838993 prefixEnd_1838993 := by exact prefixLift 1838993
  have htrace : WordTrace (prefixWord ++ tailWord_1838993) baseStart_1838993 baseEnd_1838993 := by
    simpa [prefixWord, tailWord_1838993, baseEnd_1838993] using wordTrace_append hprefix tailTrace_1838993
  have hstable : (prefixWord ++ tailWord_1838993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1838993).length < 2 ^ (prefixWord ++ tailWord_1838993).sum := by decide
  have hdescent : baseEnd_1838993 < baseStart_1838993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1838993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839023 : List Nat := [1, 1, 2, 1, 2, 2, 6, 2, 6]
def baseStart_1839023 : Nat := 118140960795 + 1839023 * 2 ^ 59
def prefixEnd_1839023 : Nat := 4983230072969 + 3 ^ 40 * 1839023 * 2
def baseEnd_1839023 : Nat := 104922525963718171972777

theorem tailTrace_1839023 : CollatzResearch.WordTrace tailWord_1839023 prefixEnd_1839023 104922525963718171972777 := by
  unfold tailWord_1839023
  simp only [CollatzResearch.WordTrace]
  refine ⟨67074679216541225968313723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44716452811027483978875815 67074679216541225968313723)
  ·
    refine ⟨100612018824811838952470585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67074679216541225968313723 100612018824811838952470585)
    ·
      refine ⟨75459014118608879214352939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100612018824811838952470585 75459014118608879214352939)
      ·
        refine ⟨113188521177913318821529409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75459014118608879214352939 113188521177913318821529409)
        ·
          refine ⟨84891390883434989116147057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113188521177913318821529409 84891390883434989116147057)
          ·
            refine ⟨63668543162576241837110293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84891390883434989116147057 63668543162576241837110293)
            ·
              refine ⟨2984462960745761336114545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63668543162576241837110293 2984462960745761336114545)
              ·
                refine ⟨2238347220559321002085909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984462960745761336114545 2238347220559321002085909)
                ·
                  refine ⟨104922525963718171972777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2238347220559321002085909 104922525963718171972777)
                  ·
                    rfl

theorem cell23_1839023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 2, 6].length) (baseStart_1839023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839023 prefixEnd_1839023 := by exact prefixLift 1839023
  have htrace : WordTrace (prefixWord ++ tailWord_1839023) baseStart_1839023 baseEnd_1839023 := by
    simpa [prefixWord, tailWord_1839023, baseEnd_1839023] using wordTrace_append hprefix tailTrace_1839023
  have hstable : (prefixWord ++ tailWord_1839023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839023).length < 2 ^ (prefixWord ++ tailWord_1839023).sum := by decide
  have hdescent : baseEnd_1839023 < baseStart_1839023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839050 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_1839050 : Nat := 118140960795 + 1839050 * 2 ^ 59
def prefixEnd_1839050 : Nat := 4983230072969 + 3 ^ 40 * 1839050 * 2
def baseEnd_1839050 : Nat := 944316597651134942117369

theorem tailTrace_1839050 : CollatzResearch.WordTrace tailWord_1839050 prefixEnd_1839050 944316597651134942117369 := by
  unfold tailWord_1839050
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768915996860852394886651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44717109324962273053031069 16768915996860852394886651)
  ·
    refine ⟨25153373995291278592329977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16768915996860852394886651 25153373995291278592329977)
    ·
      refine ⟨18865030496468458944247483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25153373995291278592329977 18865030496468458944247483)
      ·
        refine ⟨28297545744702688416371225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18865030496468458944247483 28297545744702688416371225)
        ·
          refine ⟨21223159308527016312278419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28297545744702688416371225 21223159308527016312278419)
          ·
            refine ⟨31834738962790524468417629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21223159308527016312278419 31834738962790524468417629)
            ·
              refine ⟨11938027111046446675656611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31834738962790524468417629 11938027111046446675656611)
              ·
                refine ⟨17907040666569670013484917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938027111046446675656611 17907040666569670013484917)
                ·
                  refine ⟨1678785062490906563764211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17907040666569670013484917 1678785062490906563764211)
                  ·
                    refine ⟨2518177593736359845646317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1678785062490906563764211 2518177593736359845646317)
                    ·
                      refine ⟨944316597651134942117369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518177593736359845646317 944316597651134942117369)
                      ·
                        rfl

theorem cell23_1839050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_1839050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839050 prefixEnd_1839050 := by exact prefixLift 1839050
  have htrace : WordTrace (prefixWord ++ tailWord_1839050) baseStart_1839050 baseEnd_1839050 := by
    simpa [prefixWord, tailWord_1839050, baseEnd_1839050] using wordTrace_append hprefix tailTrace_1839050
  have hstable : (prefixWord ++ tailWord_1839050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839050).length < 2 ^ (prefixWord ++ tailWord_1839050).sum := by decide
  have hdescent : baseEnd_1839050 < baseStart_1839050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839074 : List Nat := [3, 3, 3, 1, 2, 2, 1, 2, 6]
def baseStart_1839074 : Nat := 118140960795 + 1839074 * 2 ^ 59
def prefixEnd_1839074 : Nat := 4983230072969 + 3 ^ 40 * 1839074 * 2
def baseEnd_1839074 : Nat := 104925435687426983135251

theorem tailTrace_1839074 : CollatzResearch.WordTrace tailWord_1839074 prefixEnd_1839074 104925435687426983135251 := by
  unfold tailWord_1839074
  simp only [CollatzResearch.WordTrace]
  refine ⟨16769134834839115419605069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44717692892904307785613517 16769134834839115419605069)
  ·
    refine ⟨6288425563064668282351901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16769134834839115419605069 6288425563064668282351901)
    ·
      refine ⟨2358159586149250605881963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6288425563064668282351901 2358159586149250605881963)
      ·
        refine ⟨3537239379223875908822945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358159586149250605881963 3537239379223875908822945)
        ·
          refine ⟨2652929534417906931617209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3537239379223875908822945 2652929534417906931617209)
          ·
            refine ⟨1989697150813430198712907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2652929534417906931617209 1989697150813430198712907)
            ·
              refine ⟨2984545726220145298069361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989697150813430198712907 2984545726220145298069361)
              ·
                refine ⟨2238409294665108973552021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984545726220145298069361 2238409294665108973552021)
                ·
                  refine ⟨104925435687426983135251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2238409294665108973552021 104925435687426983135251)
                  ·
                    rfl

theorem cell23_1839074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_1839074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839074 prefixEnd_1839074 := by exact prefixLift 1839074
  have htrace : WordTrace (prefixWord ++ tailWord_1839074) baseStart_1839074 baseEnd_1839074 := by
    simpa [prefixWord, tailWord_1839074, baseEnd_1839074] using wordTrace_append hprefix tailTrace_1839074
  have hstable : (prefixWord ++ tailWord_1839074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839074).length < 2 ^ (prefixWord ++ tailWord_1839074).sum := by decide
  have hdescent : baseEnd_1839074 < baseStart_1839074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839127 : List Nat := [1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_1839127 : Nat := 118140960795 + 1839127 * 2 ^ 59
def prefixEnd_1839127 : Nat := 4983230072969 + 3 ^ 40 * 1839127 * 2
def baseEnd_1839127 : Nat := 944356135661531140854515

theorem tailTrace_1839127 : CollatzResearch.WordTrace tailWord_1839127 prefixEnd_1839127 944356135661531140854515 := by
  unfold tailWord_1839127
  simp only [CollatzResearch.WordTrace]
  refine ⟨67078472408164451730099635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44718981605442967820066423 67078472408164451730099635)
  ·
    refine ⟨100617708612246677595149453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67078472408164451730099635 100617708612246677595149453)
    ·
      refine ⟨37731640729592504098181045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100617708612246677595149453 37731640729592504098181045)
      ·
        refine ⟨3537341318399297259204473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37731640729592504098181045 3537341318399297259204473)
        ·
          refine ⟨2653005988799472944403355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3537341318399297259204473 2653005988799472944403355)
          ·
            refine ⟨3979508983199209416605033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653005988799472944403355 3979508983199209416605033)
            ·
              refine ⟨2984631737399407062453775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3979508983199209416605033 2984631737399407062453775)
              ·
                refine ⟨4476947606099110593680663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984631737399407062453775 4476947606099110593680663)
                ·
                  refine ⟨6715421409148665890520995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476947606099110593680663 6715421409148665890520995)
                  ·
                    refine ⟨10073132113722998835781493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6715421409148665890520995 10073132113722998835781493)
                    ·
                      refine ⟨944356135661531140854515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10073132113722998835781493 944356135661531140854515)
                      ·
                        rfl

theorem cell23_1839127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_1839127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839127 prefixEnd_1839127 := by exact prefixLift 1839127
  have htrace : WordTrace (prefixWord ++ tailWord_1839127) baseStart_1839127 baseEnd_1839127 := by
    simpa [prefixWord, tailWord_1839127, baseEnd_1839127] using wordTrace_append hprefix tailTrace_1839127
  have hstable : (prefixWord ++ tailWord_1839127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839127).length < 2 ^ (prefixWord ++ tailWord_1839127).sum := by decide
  have hdescent : baseEnd_1839127 < baseStart_1839127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839161 : List Nat := [1, 2, 1, 5, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1839161 : Nat := 118140960795 + 1839161 * 2 ^ 59
def prefixEnd_1839161 : Nat := 4983230072969 + 3 ^ 40 * 1839161 * 2
def baseEnd_1839161 : Nat := 944373594003784007829359

theorem tailTrace_1839161 : CollatzResearch.WordTrace tailWord_1839161 prefixEnd_1839161 944373594003784007829359 := by
  unfold tailWord_1839161
  simp only [CollatzResearch.WordTrace]
  refine ⟨67079712490041275536837337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44719808326694183691224891 67079712490041275536837337)
  ·
    refine ⟨50309784367530956652628003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67079712490041275536837337 50309784367530956652628003)
    ·
      refine ⟨75464676551296434978942005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50309784367530956652628003 75464676551296434978942005)
      ·
        refine ⟨7074813426684040779275813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75464676551296434978942005 7074813426684040779275813)
        ·
          refine ⟨1326527517503257646114215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7074813426684040779275813 1326527517503257646114215)
          ·
            refine ⟨1989791276254886469171323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326527517503257646114215 1989791276254886469171323)
            ·
              refine ⟨2984686914382329703756985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1989791276254886469171323 2984686914382329703756985)
              ·
                refine ⟨2238515185786747277817739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984686914382329703756985 2238515185786747277817739)
                ·
                  refine ⟨3357772778680120916726609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238515185786747277817739 3357772778680120916726609)
                  ·
                    refine ⟨2518329584010090687544957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3357772778680120916726609 2518329584010090687544957)
                    ·
                      refine ⟨944373594003784007829359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518329584010090687544957 944373594003784007829359)
                      ·
                        rfl

theorem cell23_1839161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1839161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839161 prefixEnd_1839161 := by exact prefixLift 1839161
  have htrace : WordTrace (prefixWord ++ tailWord_1839161) baseStart_1839161 baseEnd_1839161 := by
    simpa [prefixWord, tailWord_1839161, baseEnd_1839161] using wordTrace_append hprefix tailTrace_1839161
  have hstable : (prefixWord ++ tailWord_1839161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839161).length < 2 ^ (prefixWord ++ tailWord_1839161).sum := by decide
  have hdescent : baseEnd_1839161 < baseStart_1839161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839163 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4]
def baseStart_1839163 : Nat := 118140960795 + 1839163 * 2 ^ 59
def prefixEnd_1839163 : Nat := 4983230072969 + 3 ^ 40 * 1839163 * 2
def baseEnd_1839163 : Nat := 944374620965093000004349

theorem tailTrace_1839163 : CollatzResearch.WordTrace tailWord_1839163 prefixEnd_1839163 944374620965093000004349 := by
  unfold tailWord_1839163
  simp only [CollatzResearch.WordTrace]
  refine ⟨67079785436034029878410143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44719856957356019918940095 67079785436034029878410143)
  ·
    refine ⟨100619678154051044817615215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67079785436034029878410143 100619678154051044817615215)
    ·
      refine ⟨150929517231076567226422823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100619678154051044817615215 150929517231076567226422823)
      ·
        refine ⟨226394275846614850839634235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150929517231076567226422823 226394275846614850839634235)
        ·
          refine ⟨339591413769922276259451353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 226394275846614850839634235 339591413769922276259451353)
          ·
            refine ⟨254693560327441707194588515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 339591413769922276259451353 254693560327441707194588515)
            ·
              refine ⟨382040340491162560791882773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254693560327441707194588515 382040340491162560791882773)
              ·
                refine ⟨17908140960523245037119505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 382040340491162560791882773 17908140960523245037119505)
                ·
                  refine ⟨13431105720392433777839629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17908140960523245037119505 13431105720392433777839629)
                  ·
                    refine ⟨5036664645147162666689861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13431105720392433777839629 5036664645147162666689861)
                    ·
                      refine ⟨944374620965093000004349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5036664645147162666689861 944374620965093000004349)
                      ·
                        rfl

theorem cell23_1839163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 4].length) (baseStart_1839163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839163 prefixEnd_1839163 := by exact prefixLift 1839163
  have htrace : WordTrace (prefixWord ++ tailWord_1839163) baseStart_1839163 baseEnd_1839163 := by
    simpa [prefixWord, tailWord_1839163, baseEnd_1839163] using wordTrace_append hprefix tailTrace_1839163
  have hstable : (prefixWord ++ tailWord_1839163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839163).length < 2 ^ (prefixWord ++ tailWord_1839163).sum := by decide
  have hdescent : baseEnd_1839163 < baseStart_1839163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839173 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_1839173 : Nat := 118140960795 + 1839173 * 2 ^ 59
def prefixEnd_1839173 : Nat := 4983230072969 + 3 ^ 40 * 1839173 * 2
def baseEnd_1839173 : Nat := 314793251923879320293101

theorem tailTrace_1839173 : CollatzResearch.WordTrace tailWord_1839173 prefixEnd_1839173 314793251923879320293101 := by
  unfold tailWord_1839173
  simp only [CollatzResearch.WordTrace]
  refine ⟨67080150165997801586274173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44720100110665201057516115 67080150165997801586274173)
  ·
    refine ⟨25155056312249175594852815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67080150165997801586274173 25155056312249175594852815)
    ·
      refine ⟨37732584468373763392279223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25155056312249175594852815 37732584468373763392279223)
      ·
        refine ⟨56598876702560645088418835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37732584468373763392279223 56598876702560645088418835)
        ·
          refine ⟨84898315053840967632628253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56598876702560645088418835 84898315053840967632628253)
          ·
            refine ⟨31836868145190362862235595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84898315053840967632628253 31836868145190362862235595)
            ·
              refine ⟨47755302217785544293353393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31836868145190362862235595 47755302217785544293353393)
              ·
                refine ⟨35816476663339158220015045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47755302217785544293353393 35816476663339158220015045)
                ·
                  refine ⟨6715589374376092166252821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35816476663339158220015045 6715589374376092166252821)
                  ·
                    refine ⟨314793251923879320293101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6715589374376092166252821 314793251923879320293101)
                    ·
                      rfl

theorem cell23_1839173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_1839173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839173 prefixEnd_1839173 := by exact prefixLift 1839173
  have htrace : WordTrace (prefixWord ++ tailWord_1839173) baseStart_1839173 baseEnd_1839173 := by
    simpa [prefixWord, tailWord_1839173, baseEnd_1839173] using wordTrace_append hprefix tailTrace_1839173
  have hstable : (prefixWord ++ tailWord_1839173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839173).length < 2 ^ (prefixWord ++ tailWord_1839173).sum := by decide
  have hdescent : baseEnd_1839173 < baseStart_1839173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839174 : List Nat := [6, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1839174 : Nat := 118140960795 + 1839174 * 2 ^ 59
def prefixEnd_1839174 : Nat := 4983230072969 + 3 ^ 40 * 1839174 * 2
def baseEnd_1839174 : Nat := 944380269252292456966799

theorem tailTrace_1839174 : CollatzResearch.WordTrace tailWord_1839174 prefixEnd_1839174 944380269252292456966799 := by
  unfold tailWord_1839174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2096255832468568086158143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 44720124425996119171373717 2096255832468568086158143)
  ·
    refine ⟨3144383748702852129237215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2096255832468568086158143 3144383748702852129237215)
    ·
      refine ⟨4716575623054278193855823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144383748702852129237215 4716575623054278193855823)
      ·
        refine ⟨7074863434581417290783735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4716575623054278193855823 7074863434581417290783735)
        ·
          refine ⟨10612295151872125936175603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7074863434581417290783735 10612295151872125936175603)
          ·
            refine ⟨15918442727808188904263405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10612295151872125936175603 15918442727808188904263405)
            ·
              refine ⟨5969416022928070839098777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15918442727808188904263405 5969416022928070839098777)
              ·
                refine ⟨4477062017196053129324083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969416022928070839098777 4477062017196053129324083)
                ·
                  refine ⟨6715593025794079693986125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477062017196053129324083 6715593025794079693986125)
                  ·
                    refine ⟨2518347384672779885244797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6715593025794079693986125 2518347384672779885244797)
                    ·
                      refine ⟨944380269252292456966799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518347384672779885244797 944380269252292456966799)
                      ·
                        rfl

theorem cell23_1839174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1839174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839174 prefixEnd_1839174 := by exact prefixLift 1839174
  have htrace : WordTrace (prefixWord ++ tailWord_1839174) baseStart_1839174 baseEnd_1839174 := by
    simpa [prefixWord, tailWord_1839174, baseEnd_1839174] using wordTrace_append hprefix tailTrace_1839174
  have hstable : (prefixWord ++ tailWord_1839174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839174).length < 2 ^ (prefixWord ++ tailWord_1839174).sum := by decide
  have hdescent : baseEnd_1839174 < baseStart_1839174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839197 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_1839197 : Nat := 118140960795 + 1839197 * 2 ^ 59
def prefixEnd_1839197 : Nat := 4983230072969 + 3 ^ 40 * 1839197 * 2
def baseEnd_1839197 : Nat := 944392079307345866979193

theorem tailTrace_1839197 : CollatzResearch.WordTrace tailWord_1839197 prefixEnd_1839197 944392079307345866979193 := by
  unfold tailWord_1839197
  simp only [CollatzResearch.WordTrace]
  refine ⟨67081025517910853685147845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44720683678607235790098563 67081025517910853685147845)
  ·
    refine ⟨12577692284608285065965221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67081025517910853685147845 12577692284608285065965221)
    ·
      refine ⟨2358317303364053449868479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12577692284608285065965221 2358317303364053449868479)
      ·
        refine ⟨3537475955046080174802719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358317303364053449868479 3537475955046080174802719)
        ·
          refine ⟨5306213932569120262204079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537475955046080174802719 5306213932569120262204079)
          ·
            refine ⟨7959320898853680393306119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306213932569120262204079 7959320898853680393306119)
            ·
              refine ⟨11938981348280520589959179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959320898853680393306119 11938981348280520589959179)
              ·
                refine ⟨17908472022420780884938769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11938981348280520589959179 17908472022420780884938769)
                ·
                  refine ⟨13431354016815585663704077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17908472022420780884938769 13431354016815585663704077)
                  ·
                    refine ⟨5036757756305844623889029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13431354016815585663704077 5036757756305844623889029)
                    ·
                      refine ⟨944392079307345866979193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5036757756305844623889029 944392079307345866979193)
                      ·
                        rfl

theorem cell23_1839197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_1839197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839197 prefixEnd_1839197 := by exact prefixLift 1839197
  have htrace : WordTrace (prefixWord ++ tailWord_1839197) baseStart_1839197 baseEnd_1839197 := by
    simpa [prefixWord, tailWord_1839197, baseEnd_1839197] using wordTrace_append hprefix tailTrace_1839197
  have hstable : (prefixWord ++ tailWord_1839197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839197).length < 2 ^ (prefixWord ++ tailWord_1839197).sum := by decide
  have hdescent : baseEnd_1839197 < baseStart_1839197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839200 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3]
def baseStart_1839200 : Nat := 118140960795 + 1839200 * 2 ^ 59
def prefixEnd_1839200 : Nat := 4983230072969 + 3 ^ 40 * 1839200 * 2
def baseEnd_1839200 : Nat := 944393619749309355241679

theorem tailTrace_1839200 : CollatzResearch.WordTrace tailWord_1839200 prefixEnd_1839200 944393619749309355241679 := by
  unfold tailWord_1839200
  simp only [CollatzResearch.WordTrace]
  refine ⟨33540567468449992598753527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44720756624599990131671369 33540567468449992598753527)
  ·
    refine ⟨50310851202674988898130291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33540567468449992598753527 50310851202674988898130291)
    ·
      refine ⟨75466276804012483347195437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50310851202674988898130291 75466276804012483347195437)
      ·
        refine ⟨28299853801504681255198289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75466276804012483347195437 28299853801504681255198289)
        ·
          refine ⟨21224890351128510941398717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28299853801504681255198289 21224890351128510941398717)
          ·
            refine ⟨7959333881673191603024519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21224890351128510941398717 7959333881673191603024519)
            ·
              refine ⟨11939000822509787404536779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959333881673191603024519 11939000822509787404536779)
              ·
                refine ⟨17908501233764681106805169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939000822509787404536779 17908501233764681106805169)
                ·
                  refine ⟨13431375925323510830103877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17908501233764681106805169 13431375925323510830103877)
                  ·
                    refine ⟨2518382985998158280644477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13431375925323510830103877 2518382985998158280644477)
                    ·
                      refine ⟨944393619749309355241679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518382985998158280644477 944393619749309355241679)
                      ·
                        rfl

theorem cell23_1839200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 2, 4, 3].length) (baseStart_1839200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839200 prefixEnd_1839200 := by exact prefixLift 1839200
  have htrace : WordTrace (prefixWord ++ tailWord_1839200) baseStart_1839200 baseEnd_1839200 := by
    simpa [prefixWord, tailWord_1839200, baseEnd_1839200] using wordTrace_append hprefix tailTrace_1839200
  have hstable : (prefixWord ++ tailWord_1839200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839200).length < 2 ^ (prefixWord ++ tailWord_1839200).sum := by decide
  have hdescent : baseEnd_1839200 < baseStart_1839200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839214 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2]
def baseStart_1839214 : Nat := 118140960795 + 1839214 * 2 ^ 59
def prefixEnd_1839214 : Nat := 4983230072969 + 3 ^ 40 * 1839214 * 2
def baseEnd_1839214 : Nat := 944400808478472300466615

theorem tailTrace_1839214 : CollatzResearch.WordTrace tailWord_1839214 prefixEnd_1839214 944400808478472300466615 := by
  unfold tailWord_1839214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8385205694856158198564587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44721097039232843725677797 8385205694856158198564587)
  ·
    refine ⟨12577808542284237297846881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8385205694856158198564587 12577808542284237297846881)
    ·
      refine ⟨9433356406713177973385161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12577808542284237297846881 9433356406713177973385161)
      ·
        refine ⟨7075017305034883480038871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9433356406713177973385161 7075017305034883480038871)
        ·
          refine ⟨10612525957552325220058307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7075017305034883480038871 10612525957552325220058307)
          ·
            refine ⟨15918788936328487830087461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10612525957552325220058307 15918788936328487830087461)
            ·
              refine ⟨2984772925561591468141399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15918788936328487830087461 2984772925561591468141399)
              ·
                refine ⟨4477159388342387202212099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984772925561591468141399 4477159388342387202212099)
                ·
                  refine ⟨6715739082513580803318149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477159388342387202212099 6715739082513580803318149)
                  ·
                    refine ⟨1259201077971296400622153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6715739082513580803318149 1259201077971296400622153)
                    ·
                      refine ⟨944400808478472300466615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259201077971296400622153 944400808478472300466615)
                      ·
                        rfl

theorem cell23_1839214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_1839214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839214 prefixEnd_1839214 := by exact prefixLift 1839214
  have htrace : WordTrace (prefixWord ++ tailWord_1839214) baseStart_1839214 baseEnd_1839214 := by
    simpa [prefixWord, tailWord_1839214, baseEnd_1839214] using wordTrace_append hprefix tailTrace_1839214
  have hstable : (prefixWord ++ tailWord_1839214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839214).length < 2 ^ (prefixWord ++ tailWord_1839214).sum := by decide
  have hdescent : baseEnd_1839214 < baseStart_1839214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839237 : List Nat := [1, 3, 1, 1, 5, 1, 1, 5, 5]
def baseStart_1839237 : Nat := 118140960795 + 1839237 * 2 ^ 59
def prefixEnd_1839237 : Nat := 4983230072969 + 3 ^ 40 * 1839237 * 2
def baseEnd_1839237 : Nat := 104934735392613967831001

theorem tailTrace_1839237 : CollatzResearch.WordTrace tailWord_1839237 prefixEnd_1839237 104934735392613967831001 := by
  unfold tailWord_1839237
  simp only [CollatzResearch.WordTrace]
  refine ⟨67082484437765940516603965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44721656291843960344402643 67082484437765940516603965)
  ·
    refine ⟨25155931664162227693726487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67082484437765940516603965 25155931664162227693726487)
    ·
      refine ⟨37733897496243341540589731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25155931664162227693726487 37733897496243341540589731)
      ·
        refine ⟨56600846244365012310884597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37733897496243341540589731 56600846244365012310884597)
        ·
          refine ⟨5306329335409219904145431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56600846244365012310884597 5306329335409219904145431)
          ·
            refine ⟨7959494003113829856218147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306329335409219904145431 7959494003113829856218147)
            ·
              refine ⟨11939241004670744784327221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959494003113829856218147 11939241004670744784327221)
              ·
                refine ⟨1119303844187882323530677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11939241004670744784327221 1119303844187882323530677)
                ·
                  refine ⟨104934735392613967831001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1119303844187882323530677 104934735392613967831001)
                  ·
                    rfl

theorem cell23_1839237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_1839237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839237 prefixEnd_1839237 := by exact prefixLift 1839237
  have htrace : WordTrace (prefixWord ++ tailWord_1839237) baseStart_1839237 baseEnd_1839237 := by
    simpa [prefixWord, tailWord_1839237, baseEnd_1839237] using wordTrace_append hprefix tailTrace_1839237
  have hstable : (prefixWord ++ tailWord_1839237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839237).length < 2 ^ (prefixWord ++ tailWord_1839237).sum := by decide
  have hdescent : baseEnd_1839237 < baseStart_1839237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839260 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1839260 : Nat := 118140960795 + 1839260 * 2 ^ 59
def prefixEnd_1839260 : Nat := 4983230072969 + 3 ^ 40 * 1839260 * 2
def baseEnd_1839260 : Nat := 944424428588579120491403

theorem tailTrace_1839260 : CollatzResearch.WordTrace tailWord_1839260 prefixEnd_1839260 944424428588579120491403 := by
  unfold tailWord_1839260
  simp only [CollatzResearch.WordTrace]
  refine ⟨33541661658341307722345617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44722215544455076963127489 33541661658341307722345617)
  ·
    refine ⟨25156246243755980791759213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33541661658341307722345617 25156246243755980791759213)
    ·
      refine ⟨9433592341408492796909705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25156246243755980791759213 9433592341408492796909705)
      ·
        refine ⟨7075194256056369597682279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9433592341408492796909705 7075194256056369597682279)
        ·
          refine ⟨10612791384084554396523419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7075194256056369597682279 10612791384084554396523419)
          ·
            refine ⟨15919187076126831594785129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10612791384084554396523419 15919187076126831594785129)
            ·
              refine ⟨11939390307095123696088847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15919187076126831594785129 11939390307095123696088847)
              ·
                refine ⟨17909085460642685544133271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939390307095123696088847 17909085460642685544133271)
                ·
                  refine ⟨26863628190964028316199907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17909085460642685544133271 26863628190964028316199907)
                  ·
                    refine ⟨40295442286446042474299861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26863628190964028316199907 40295442286446042474299861)
                    ·
                      refine ⟨944424428588579120491403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40295442286446042474299861 944424428588579120491403)
                      ·
                        rfl

theorem cell23_1839260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1839260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839260 prefixEnd_1839260 := by exact prefixLift 1839260
  have htrace : WordTrace (prefixWord ++ tailWord_1839260) baseStart_1839260 baseEnd_1839260 := by
    simpa [prefixWord, tailWord_1839260, baseEnd_1839260] using wordTrace_append hprefix tailTrace_1839260
  have hstable : (prefixWord ++ tailWord_1839260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839260).length < 2 ^ (prefixWord ++ tailWord_1839260).sum := by decide
  have hdescent : baseEnd_1839260 < baseStart_1839260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839307 : List Nat := [1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 3]
def baseStart_1839307 : Nat := 118140960795 + 1839307 * 2 ^ 59
def prefixEnd_1839307 : Nat := 4983230072969 + 3 ^ 40 * 1839307 * 2
def baseEnd_1839307 : Nat := 944448562179340436603687

theorem tailTrace_1839307 : CollatzResearch.WordTrace tailWord_1839307 prefixEnd_1839307 944448562179340436603687 := by
  unfold tailWord_1839307
  simp only [CollatzResearch.WordTrace]
  refine ⟨67085037547512342471652175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44723358365008228314434783 67085037547512342471652175)
  ·
    refine ⟨100627556321268513707478263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67085037547512342471652175 100627556321268513707478263)
    ·
      refine ⟨150941334481902770561217395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100627556321268513707478263 150941334481902770561217395)
      ·
        refine ⟨226412001722854155841826093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150941334481902770561217395 226412001722854155841826093)
        ·
          refine ⟨84904500646070308440684785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 226412001722854155841826093 84904500646070308440684785)
          ·
            refine ⟨63678375484552731330513589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84904500646070308440684785 63678375484552731330513589)
            ·
              refine ⟨5969847701676818562235649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63678375484552731330513589 5969847701676818562235649)
              ·
                refine ⟨4477385776257613921676737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5969847701676818562235649 4477385776257613921676737)
                ·
                  refine ⟨3358039332193210441257553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4477385776257613921676737 3358039332193210441257553)
                  ·
                    refine ⟨2518529499144907830943165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3358039332193210441257553 2518529499144907830943165)
                    ·
                      refine ⟨944448562179340436603687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518529499144907830943165 944448562179340436603687)
                      ·
                        rfl

theorem cell23_1839307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 2, 3].length) (baseStart_1839307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839307 prefixEnd_1839307 := by exact prefixLift 1839307
  have htrace : WordTrace (prefixWord ++ tailWord_1839307) baseStart_1839307 baseEnd_1839307 := by
    simpa [prefixWord, tailWord_1839307, baseEnd_1839307] using wordTrace_append hprefix tailTrace_1839307
  have hstable : (prefixWord ++ tailWord_1839307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839307).length < 2 ^ (prefixWord ++ tailWord_1839307).sum := by decide
  have hdescent : baseEnd_1839307 < baseStart_1839307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839314 : List Nat := [3, 2, 2, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1839314 : Nat := 118140960795 + 1839314 * 2 ^ 59
def prefixEnd_1839314 : Nat := 4983230072969 + 3 ^ 40 * 1839314 * 2
def baseEnd_1839314 : Nat := 314817385514640636405385

theorem tailTrace_1839314 : CollatzResearch.WordTrace tailWord_1839314 prefixEnd_1839314 314817385514640636405385 := by
  unfold tailWord_1839314
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771323214621745666789249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44723528572324655111437997 16771323214621745666789249)
  ·
    refine ⟨12578492410966309250091937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16771323214621745666789249 12578492410966309250091937)
    ·
      refine ⟨9433869308224731937568953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12578492410966309250091937 9433869308224731937568953)
      ·
        refine ⟨7075401981168548953176715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9433869308224731937568953 7075401981168548953176715)
        ·
          refine ⟨10613102971752823429765073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7075401981168548953176715 10613102971752823429765073)
          ·
            refine ⟨7959827228814617572323805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10613102971752823429765073 7959827228814617572323805)
            ·
              refine ⟨2984935210805481589621427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7959827228814617572323805 2984935210805481589621427)
              ·
                refine ⟨4477402816208222384432141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984935210805481589621427 4477402816208222384432141)
                ·
                  refine ⟨1679026056078083394162053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4477402816208222384432141 1679026056078083394162053)
                  ·
                    refine ⟨314817385514640636405385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679026056078083394162053 314817385514640636405385)
                    ·
                      rfl

theorem cell23_1839314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1839314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839314 prefixEnd_1839314 := by exact prefixLift 1839314
  have htrace : WordTrace (prefixWord ++ tailWord_1839314) baseStart_1839314 baseEnd_1839314 := by
    simpa [prefixWord, tailWord_1839314, baseEnd_1839314] using wordTrace_append hprefix tailTrace_1839314
  have hstable : (prefixWord ++ tailWord_1839314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839314).length < 2 ^ (prefixWord ++ tailWord_1839314).sum := by decide
  have hdescent : baseEnd_1839314 < baseStart_1839314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839341 : List Nat := [1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 3]
def baseStart_1839341 : Nat := 118140960795 + 1839341 * 2 ^ 59
def prefixEnd_1839341 : Nat := 4983230072969 + 3 ^ 40 * 1839341 * 2
def baseEnd_1839341 : Nat := 944466020521593303578531

theorem tailTrace_1839341 : CollatzResearch.WordTrace tailWord_1839341 prefixEnd_1839341 944466020521593303578531 := by
  unfold tailWord_1839341
  simp only [CollatzResearch.WordTrace]
  refine ⟨67086277629389166278389877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44724185086259444185593251 67086277629389166278389877)
  ·
    refine ⟨6289338527755234338599051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67086277629389166278389877 6289338527755234338599051)
    ·
      refine ⟨9434007791632851507898577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289338527755234338599051 9434007791632851507898577)
      ·
        refine ⟨7075505843724638630923933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9434007791632851507898577 7075505843724638630923933)
        ·
          refine ⟨2653314691396739486596475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7075505843724638630923933 2653314691396739486596475)
          ·
            refine ⟨3979972037095109229894713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653314691396739486596475 3979972037095109229894713)
            ·
              refine ⟨2984979027821331922421035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3979972037095109229894713 2984979027821331922421035)
              ·
                refine ⟨4477468541731997883631553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984979027821331922421035 4477468541731997883631553)
                ·
                  refine ⟨3358101406298998412723665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4477468541731997883631553 3358101406298998412723665)
                  ·
                    refine ⟨2518576054724248809542749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3358101406298998412723665 2518576054724248809542749)
                    ·
                      refine ⟨944466020521593303578531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518576054724248809542749 944466020521593303578531)
                      ·
                        rfl

theorem cell23_1839341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_1839341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839341 prefixEnd_1839341 := by exact prefixLift 1839341
  have htrace : WordTrace (prefixWord ++ tailWord_1839341) baseStart_1839341 baseEnd_1839341 := by
    simpa [prefixWord, tailWord_1839341, baseEnd_1839341] using wordTrace_append hprefix tailTrace_1839341
  have hstable : (prefixWord ++ tailWord_1839341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839341).length < 2 ^ (prefixWord ++ tailWord_1839341).sum := by decide
  have hdescent : baseEnd_1839341 < baseStart_1839341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839357 : List Nat := [1, 4, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1839357 : Nat := 118140960795 + 1839357 * 2 ^ 59
def prefixEnd_1839357 : Nat := 4983230072969 + 3 ^ 40 * 1839357 * 2
def baseEnd_1839357 : Nat := 314824745404021746992819

theorem tailTrace_1839357 : CollatzResearch.WordTrace tailWord_1839357 prefixEnd_1839357 314824745404021746992819 := by
  unfold tailWord_1839357
  simp only [CollatzResearch.WordTrace]
  refine ⟨67086861197331201010972325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44724574131554134007314883 67086861197331201010972325)
  ·
    refine ⟨12578786474499600189557311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67086861197331201010972325 12578786474499600189557311)
    ·
      refine ⟨18868179711749400284335967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12578786474499600189557311 18868179711749400284335967)
      ·
        refine ⟨28302269567624100426503951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18868179711749400284335967 28302269567624100426503951)
        ·
          refine ⟨42453404351436150639755927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28302269567624100426503951 42453404351436150639755927)
          ·
            refine ⟨63680106527154225959633891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42453404351436150639755927 63680106527154225959633891)
            ·
              refine ⟨95520159790731338939450837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63680106527154225959633891 95520159790731338939450837)
              ·
                refine ⟨2238753745095265756393379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 95520159790731338939450837 2238753745095265756393379)
                ·
                  refine ⟨3358130617642898634590069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2238753745095265756393379 3358130617642898634590069)
                  ·
                    refine ⟨314824745404021746992819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3358130617642898634590069 314824745404021746992819)
                    ·
                      rfl

theorem cell23_1839357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1839357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839357 prefixEnd_1839357 := by exact prefixLift 1839357
  have htrace : WordTrace (prefixWord ++ tailWord_1839357) baseStart_1839357 baseEnd_1839357 := by
    simpa [prefixWord, tailWord_1839357, baseEnd_1839357] using wordTrace_append hprefix tailTrace_1839357
  have hstable : (prefixWord ++ tailWord_1839357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839357).length < 2 ^ (prefixWord ++ tailWord_1839357).sum := by decide
  have hdescent : baseEnd_1839357 < baseStart_1839357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839371 : List Nat := [1, 1, 1, 1, 5, 2, 3, 4, 1, 1, 3]
def baseStart_1839371 : Nat := 118140960795 + 1839371 * 2 ^ 59
def prefixEnd_1839371 : Nat := 4983230072969 + 3 ^ 40 * 1839371 * 2
def baseEnd_1839371 : Nat := 944481424941228186203393

theorem tailTrace_1839371 : CollatzResearch.WordTrace tailWord_1839371 prefixEnd_1839371 944481424941228186203393 := by
  unfold tailWord_1839371
  simp only [CollatzResearch.WordTrace]
  refine ⟨67087371819280481401981967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44724914546186987601321311 67087371819280481401981967)
  ·
    refine ⟨100631057728920722102972951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67087371819280481401981967 100631057728920722102972951)
    ·
      refine ⟨150946586593381083154459427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100631057728920722102972951 150946586593381083154459427)
      ·
        refine ⟨226419879890071624731689141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150946586593381083154459427 226419879890071624731689141)
        ·
          refine ⟨21226863739694214818595857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 226419879890071624731689141 21226863739694214818595857)
          ·
            refine ⟨15920147804770661113946893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21226863739694214818595857 15920147804770661113946893)
            ·
              refine ⟨5970055426788997917730085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15920147804770661113946893 5970055426788997917730085)
              ·
                refine ⟨1119385392522937109574391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5970055426788997917730085 1119385392522937109574391)
                ·
                  refine ⟨1679078088784405664361587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119385392522937109574391 1679078088784405664361587)
                  ·
                    refine ⟨2518617133176608496542381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1679078088784405664361587 2518617133176608496542381)
                    ·
                      refine ⟨944481424941228186203393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518617133176608496542381 944481424941228186203393)
                      ·
                        rfl

theorem cell23_1839371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 4, 1, 1, 3].length) (baseStart_1839371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839371 prefixEnd_1839371 := by exact prefixLift 1839371
  have htrace : WordTrace (prefixWord ++ tailWord_1839371) baseStart_1839371 baseEnd_1839371 := by
    simpa [prefixWord, tailWord_1839371, baseEnd_1839371] using wordTrace_append hprefix tailTrace_1839371
  have hstable : (prefixWord ++ tailWord_1839371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839371).length < 2 ^ (prefixWord ++ tailWord_1839371).sum := by decide
  have hdescent : baseEnd_1839371 < baseStart_1839371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839377 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 4]
def baseStart_1839377 : Nat := 118140960795 + 1839377 * 2 ^ 59
def prefixEnd_1839377 : Nat := 4983230072969 + 3 ^ 40 * 1839377 * 2
def baseEnd_1839377 : Nat := 944484505825155162728365

theorem tailTrace_1839377 : CollatzResearch.WordTrace tailWord_1839377 prefixEnd_1839377 944484505825155162728365 := by
  unfold tailWord_1839377
  simp only [CollatzResearch.WordTrace]
  refine ⟨67087590657258744426700385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44725060438172496284466923 67087590657258744426700385)
  ·
    refine ⟨50315692992944058320025289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67087590657258744426700385 50315692992944058320025289)
    ·
      refine ⟨37736769744708043740018967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50315692992944058320025289 37736769744708043740018967)
      ·
        refine ⟨56605154617062065610028451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37736769744708043740018967 56605154617062065610028451)
        ·
          refine ⟨84907731925593098415042677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56605154617062065610028451 84907731925593098415042677)
          ·
            refine ⟨7960099868024352976410251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84907731925593098415042677 7960099868024352976410251)
            ·
              refine ⟨11940149802036529464615377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960099868024352976410251 11940149802036529464615377)
              ·
                refine ⟨8955112351527397098461533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11940149802036529464615377 8955112351527397098461533)
                ·
                  refine ⟨3358167131822773911923075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8955112351527397098461533 3358167131822773911923075)
                  ·
                    refine ⟨5037250697734160867884613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3358167131822773911923075 5037250697734160867884613)
                    ·
                      refine ⟨944484505825155162728365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5037250697734160867884613 944484505825155162728365)
                      ·
                        rfl

theorem cell23_1839377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 4].length) (baseStart_1839377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839377 prefixEnd_1839377 := by exact prefixLift 1839377
  have htrace : WordTrace (prefixWord ++ tailWord_1839377) baseStart_1839377 baseEnd_1839377 := by
    simpa [prefixWord, tailWord_1839377, baseEnd_1839377] using wordTrace_append hprefix tailTrace_1839377
  have hstable : (prefixWord ++ tailWord_1839377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839377).length < 2 ^ (prefixWord ++ tailWord_1839377).sum := by decide
  have hdescent : baseEnd_1839377 < baseStart_1839377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839394 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 3, 1, 4]
def baseStart_1839394 : Nat := 118140960795 + 1839394 * 2 ^ 59
def prefixEnd_1839394 : Nat := 4983230072969 + 3 ^ 40 * 1839394 * 2
def baseEnd_1839394 : Nat := 944493234996281596215787

theorem tailTrace_1839394 : CollatzResearch.WordTrace tailWord_1839394 prefixEnd_1839394 944493234996281596215787 := by
  unfold tailWord_1839394
  simp only [CollatzResearch.WordTrace]
  refine ⟨16772052674549289082517309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44725473798798104220046157 16772052674549289082517309)
  ·
    refine ⟨6289519752955983405943991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16772052674549289082517309 6289519752955983405943991)
    ·
      refine ⟨9434279629433975108915987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289519752955983405943991 9434279629433975108915987)
      ·
        refine ⟨14151419444150962663373981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9434279629433975108915987 14151419444150962663373981)
        ·
          refine ⟨5306782291556610998765243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14151419444150962663373981 5306782291556610998765243)
          ·
            refine ⟨7960173437334916498147865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306782291556610998765243 7960173437334916498147865)
            ·
              refine ⟨5970130078001187373610899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7960173437334916498147865 5970130078001187373610899)
              ·
                refine ⟨8955195117001781060416349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5970130078001187373610899 8955195117001781060416349)
                ·
                  refine ⟨3358198168875667897656131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8955195117001781060416349 3358198168875667897656131)
                  ·
                    refine ⟨5037297253313501846484197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3358198168875667897656131 5037297253313501846484197)
                    ·
                      refine ⟨944493234996281596215787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5037297253313501846484197 944493234996281596215787)
                      ·
                        rfl

theorem cell23_1839394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 3, 1, 4].length) (baseStart_1839394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839394 prefixEnd_1839394 := by exact prefixLift 1839394
  have htrace : WordTrace (prefixWord ++ tailWord_1839394) baseStart_1839394 baseEnd_1839394 := by
    simpa [prefixWord, tailWord_1839394, baseEnd_1839394] using wordTrace_append hprefix tailTrace_1839394
  have hstable : (prefixWord ++ tailWord_1839394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839394).length < 2 ^ (prefixWord ++ tailWord_1839394).sum := by decide
  have hdescent : baseEnd_1839394 < baseStart_1839394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839407 : List Nat := [1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_1839407 : Nat := 118140960795 + 1839407 * 2 ^ 59
def prefixEnd_1839407 : Nat := 4983230072969 + 3 ^ 40 * 1839407 * 2
def baseEnd_1839407 : Nat := 944499910244790045353227

theorem tailTrace_1839407 : CollatzResearch.WordTrace tailWord_1839407 prefixEnd_1839407 944499910244790045353227 := by
  unfold tailWord_1839407
  simp only [CollatzResearch.WordTrace]
  refine ⟨67088684847150059550292475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44725789898100039700194983 67088684847150059550292475)
  ·
    refine ⟨100633027270725089325438713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67088684847150059550292475 100633027270725089325438713)
    ·
      refine ⟨75474770453043816994079035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100633027270725089325438713 75474770453043816994079035)
      ·
        refine ⟨113212155679565725491118553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75474770453043816994079035 113212155679565725491118553)
        ·
          refine ⟨84909116759674294118338915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113212155679565725491118553 84909116759674294118338915)
          ·
            refine ⟨127363675139511441177508373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84909116759674294118338915 127363675139511441177508373)
            ·
              refine ⟨5970172272164598805195705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127363675139511441177508373 5970172272164598805195705)
              ·
                refine ⟨4477629204123449103896779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5970172272164598805195705 4477629204123449103896779)
                ·
                  refine ⟨6716443806185173655845169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4477629204123449103896779 6716443806185173655845169)
                  ·
                    refine ⟨5037332854638880241883877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6716443806185173655845169 5037332854638880241883877)
                    ·
                      refine ⟨944499910244790045353227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5037332854638880241883877 944499910244790045353227)
                      ·
                        rfl

theorem cell23_1839407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_1839407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839407 prefixEnd_1839407 := by exact prefixLift 1839407
  have htrace : WordTrace (prefixWord ++ tailWord_1839407) baseStart_1839407 baseEnd_1839407 := by
    simpa [prefixWord, tailWord_1839407, baseEnd_1839407] using wordTrace_append hprefix tailTrace_1839407
  have hstable : (prefixWord ++ tailWord_1839407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839407).length < 2 ^ (prefixWord ++ tailWord_1839407).sum := by decide
  have hdescent : baseEnd_1839407 < baseStart_1839407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839417 : List Nat := [1, 2, 1, 6, 1, 2, 10]
def baseStart_1839417 : Nat := 118140960795 + 1839417 * 2 ^ 59
def prefixEnd_1839417 : Nat := 4983230072969 + 3 ^ 40 * 1839417 * 2
def baseEnd_1839417 : Nat := 11660556111744876620101

theorem tailTrace_1839417 : CollatzResearch.WordTrace tailWord_1839417 prefixEnd_1839417 11660556111744876620101 := by
  unfold tailWord_1839417
  simp only [CollatzResearch.WordTrace]
  refine ⟨67089049577113831258156505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44726033051409220838771003 67089049577113831258156505)
  ·
    refine ⟨50316787182835373443617379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67089049577113831258156505 50316787182835373443617379)
    ·
      refine ⟨75475180774253060165426069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50316787182835373443617379 75475180774253060165426069)
      ·
        refine ⟨3537899098793112195254347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 75475180774253060165426069 3537899098793112195254347)
        ·
          refine ⟨5306848648189668292881521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537899098793112195254347 5306848648189668292881521)
          ·
            refine ⟨3980136486142251219661141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5306848648189668292881521 3980136486142251219661141)
            ·
              refine ⟨11660556111744876620101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3980136486142251219661141 11660556111744876620101)
              ·
                rfl

theorem cell23_1839417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 10].length) (baseStart_1839417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839417 prefixEnd_1839417 := by exact prefixLift 1839417
  have htrace : WordTrace (prefixWord ++ tailWord_1839417) baseStart_1839417 baseEnd_1839417 := by
    simpa [prefixWord, tailWord_1839417, baseEnd_1839417] using wordTrace_append hprefix tailTrace_1839417
  have hstable : (prefixWord ++ tailWord_1839417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839417).length < 2 ^ (prefixWord ++ tailWord_1839417).sum := by decide
  have hdescent : baseEnd_1839417 < baseStart_1839417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839427 : List Nat := [1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 3]
def baseStart_1839427 : Nat := 118140960795 + 1839427 * 2 ^ 59
def prefixEnd_1839427 : Nat := 4983230072969 + 3 ^ 40 * 1839427 * 2
def baseEnd_1839427 : Nat := 944510179857879967103135

theorem tailTrace_1839427 : CollatzResearch.WordTrace tailWord_1839427 prefixEnd_1839427 944510179857879967103135 := by
  unfold tailWord_1839427
  simp only [CollatzResearch.WordTrace]
  refine ⟨67089414307077602966020535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44726276204718401977347023 67089414307077602966020535)
  ·
    refine ⟨100634121460616404449030803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67089414307077602966020535 100634121460616404449030803)
    ·
      refine ⟨150951182190924606673546205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100634121460616404449030803 150951182190924606673546205)
      ·
        refine ⟨56606693321596727502579827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150951182190924606673546205 56606693321596727502579827)
        ·
          refine ⟨84910039982395091253869741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56606693321596727502579827 84910039982395091253869741)
          ·
            refine ⟨31841264993398159220201153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84910039982395091253869741 31841264993398159220201153)
            ·
              refine ⟨23880948745048619415150865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31841264993398159220201153 23880948745048619415150865)
              ·
                refine ⟨17910711558786464561363149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23880948745048619415150865 17910711558786464561363149)
                ·
                  refine ⟨6716516834544924210511181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17910711558786464561363149 6716516834544924210511181)
                  ·
                    refine ⟨2518693812954346578941693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6716516834544924210511181 2518693812954346578941693)
                    ·
                      refine ⟨944510179857879967103135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518693812954346578941693 944510179857879967103135)
                      ·
                        rfl

theorem cell23_1839427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_1839427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839427 prefixEnd_1839427 := by exact prefixLift 1839427
  have htrace : WordTrace (prefixWord ++ tailWord_1839427) baseStart_1839427 baseEnd_1839427 := by
    simpa [prefixWord, tailWord_1839427, baseEnd_1839427] using wordTrace_append hprefix tailTrace_1839427
  have hstable : (prefixWord ++ tailWord_1839427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839427).length < 2 ^ (prefixWord ++ tailWord_1839427).sum := by decide
  have hdescent : baseEnd_1839427 < baseStart_1839427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839484 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 5, 4, 2]
def baseStart_1839484 : Nat := 118140960795 + 1839484 * 2 ^ 59
def prefixEnd_1839484 : Nat := 4983230072969 + 3 ^ 40 * 1839484 * 2
def baseEnd_1839484 : Nat := 944539448255186244090373

theorem tailTrace_1839484 : CollatzResearch.WordTrace tailWord_1839484 prefixEnd_1839484 944539448255186244090373 := by
  unfold tailWord_1839484
  simp only [CollatzResearch.WordTrace]
  refine ⟨33545746633935550850422753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44727662178580734467230337 33545746633935550850422753)
  ·
    refine ⟨25159309975451663137817065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33545746633935550850422753 25159309975451663137817065)
    ·
      refine ⟨18869482481588747353362799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25159309975451663137817065 18869482481588747353362799)
      ·
        refine ⟨28304223722383121030044199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18869482481588747353362799 28304223722383121030044199)
        ·
          refine ⟨42456335583574681545066299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28304223722383121030044199 42456335583574681545066299)
          ·
            refine ⟨63684503375362022317599449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42456335583574681545066299 63684503375362022317599449)
            ·
              refine ⟨47763377531521516738199587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63684503375362022317599449 47763377531521516738199587)
              ·
                refine ⟨71645066297282275107299381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47763377531521516738199587 71645066297282275107299381)
                ·
                  refine ⟨6716724965370213291309317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71645066297282275107299381 6716724965370213291309317)
                  ·
                    refine ⟨1259385931006914992120497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716724965370213291309317 1259385931006914992120497)
                    ·
                      refine ⟨944539448255186244090373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259385931006914992120497 944539448255186244090373)
                      ·
                        rfl

theorem cell23_1839484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 4, 2].length) (baseStart_1839484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839484 prefixEnd_1839484 := by exact prefixLift 1839484
  have htrace : WordTrace (prefixWord ++ tailWord_1839484) baseStart_1839484 baseEnd_1839484 := by
    simpa [prefixWord, tailWord_1839484, baseEnd_1839484] using wordTrace_append hprefix tailTrace_1839484
  have hstable : (prefixWord ++ tailWord_1839484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839484).length < 2 ^ (prefixWord ++ tailWord_1839484).sum := by decide
  have hdescent : baseEnd_1839484 < baseStart_1839484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839487 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_1839487 : Nat := 118140960795 + 1839487 * 2 ^ 59
def prefixEnd_1839487 : Nat := 4983230072969 + 3 ^ 40 * 1839487 * 2
def baseEnd_1839487 : Nat := 944540988697149732352859

theorem tailTrace_1839487 : CollatzResearch.WordTrace tailWord_1839487 prefixEnd_1839487 944540988697149732352859 := by
  unfold tailWord_1839487
  simp only [CollatzResearch.WordTrace]
  refine ⟨67091602686860233213204715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44727735124573488808803143 67091602686860233213204715)
  ·
    refine ⟨100637404030290349819807073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67091602686860233213204715 100637404030290349819807073)
    ·
      refine ⟨75478053022717762364855305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100637404030290349819807073 75478053022717762364855305)
      ·
        refine ⟨56608539767038321773641479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75478053022717762364855305 56608539767038321773641479)
        ·
          refine ⟨84912809650557482660462219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56608539767038321773641479 84912809650557482660462219)
          ·
            refine ⟨127369214475836223990693329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84912809650557482660462219 127369214475836223990693329)
            ·
              refine ⟨95526910856877167993019997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127369214475836223990693329 95526910856877167993019997)
              ·
                refine ⟨35822591571328937997382499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95526910856877167993019997 35822591571328937997382499)
                ·
                  refine ⟨53733887356993406996073749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35822591571328937997382499 53733887356993406996073749)
                  ·
                    refine ⟨2518775969859065952940957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53733887356993406996073749 2518775969859065952940957)
                    ·
                      refine ⟨944540988697149732352859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518775969859065952940957 944540988697149732352859)
                      ·
                        rfl

theorem cell23_1839487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_1839487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839487 prefixEnd_1839487 := by exact prefixLift 1839487
  have htrace : WordTrace (prefixWord ++ tailWord_1839487) baseStart_1839487 baseEnd_1839487 := by
    simpa [prefixWord, tailWord_1839487, baseEnd_1839487] using wordTrace_append hprefix tailTrace_1839487
  have hstable : (prefixWord ++ tailWord_1839487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839487).length < 2 ^ (prefixWord ++ tailWord_1839487).sum := by decide
  have hdescent : baseEnd_1839487 < baseStart_1839487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839518 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1839518 : Nat := 118140960795 + 1839518 * 2 ^ 59
def prefixEnd_1839518 : Nat := 4983230072969 + 3 ^ 40 * 1839518 * 2
def baseEnd_1839518 : Nat := 944556906597439111065217

theorem tailTrace_1839518 : CollatzResearch.WordTrace tailWord_1839518 prefixEnd_1839518 944556906597439111065217 := by
  unfold tailWord_1839518
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386591668718490688447901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44728488899831950338388805 8386591668718490688447901)
  ·
    refine ⟨3144971875769434008167963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8386591668718490688447901 3144971875769434008167963)
    ·
      refine ⟨4717457813654151012251945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3144971875769434008167963 4717457813654151012251945)
      ·
        refine ⟨3538093360240613259188959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4717457813654151012251945 3538093360240613259188959)
        ·
          refine ⟨5307140040360919888783439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3538093360240613259188959 5307140040360919888783439)
          ·
            refine ⟨7960710060541379833175159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307140040360919888783439 7960710060541379833175159)
            ·
              refine ⟨11941065090812069749762739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960710060541379833175159 11941065090812069749762739)
              ·
                refine ⟨17911597636218104624644109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11941065090812069749762739 17911597636218104624644109)
                ·
                  refine ⟨6716849113581789234241541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17911597636218104624644109 6716849113581789234241541)
                  ·
                    refine ⟨1259409208796585481420289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6716849113581789234241541 1259409208796585481420289)
                    ·
                      refine ⟨944556906597439111065217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259409208796585481420289 944556906597439111065217)
                      ·
                        rfl

theorem cell23_1839518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1839518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839518 prefixEnd_1839518 := by exact prefixLift 1839518
  have htrace : WordTrace (prefixWord ++ tailWord_1839518) baseStart_1839518 baseEnd_1839518 := by
    simpa [prefixWord, tailWord_1839518, baseEnd_1839518] using wordTrace_append hprefix tailTrace_1839518
  have hstable : (prefixWord ++ tailWord_1839518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839518).length < 2 ^ (prefixWord ++ tailWord_1839518).sum := by decide
  have hdescent : baseEnd_1839518 < baseStart_1839518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839584 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 5, 4]
def baseStart_1839584 : Nat := 118140960795 + 1839584 * 2 ^ 59
def prefixEnd_1839584 : Nat := 4983230072969 + 3 ^ 40 * 1839584 * 2
def baseEnd_1839584 : Nat := 314863598773545284279971

theorem tailTrace_1839584 : CollatzResearch.WordTrace tailWord_1839584 prefixEnd_1839584 314863598773545284279971 := by
  unfold tailWord_1839584
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547570283754409389742903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44730093711672545852990537 33547570283754409389742903)
  ·
    refine ⟨50321355425631614084614355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33547570283754409389742903 50321355425631614084614355)
    ·
      refine ⟨75482033138447421126921533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50321355425631614084614355 75482033138447421126921533)
      ·
        refine ⟨28305762426917782922595575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75482033138447421126921533 28305762426917782922595575)
        ·
          refine ⟨42458643640376674383893363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28305762426917782922595575 42458643640376674383893363)
          ·
            refine ⟨63687965460565011575840045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42458643640376674383893363 63687965460565011575840045)
            ·
              refine ⟨23882987047711879340940017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63687965460565011575840045 23882987047711879340940017)
              ·
                refine ⟨17912240285783909505705013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23882987047711879340940017 17912240285783909505705013)
                ·
                  refine ⟨1679272526792241516159845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17912240285783909505705013 1679272526792241516159845)
                  ·
                    refine ⟨314863598773545284279971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679272526792241516159845 314863598773545284279971)
                    ·
                      rfl

theorem cell23_1839584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 5, 4].length) (baseStart_1839584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839584 prefixEnd_1839584 := by exact prefixLift 1839584
  have htrace : WordTrace (prefixWord ++ tailWord_1839584) baseStart_1839584 baseEnd_1839584 := by
    simpa [prefixWord, tailWord_1839584, baseEnd_1839584] using wordTrace_append hprefix tailTrace_1839584
  have hstable : (prefixWord ++ tailWord_1839584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839584).length < 2 ^ (prefixWord ++ tailWord_1839584).sum := by decide
  have hdescent : baseEnd_1839584 < baseStart_1839584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839586 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1839586 : Nat := 118140960795 + 1839586 * 2 ^ 59
def prefixEnd_1839586 : Nat := 4983230072969 + 3 ^ 40 * 1839586 * 2
def baseEnd_1839586 : Nat := 944591823281944845014905

theorem tailTrace_1839586 : CollatzResearch.WordTrace tailWord_1839586 prefixEnd_1839586 944591823281944845014905 := by
  unfold tailWord_1839586
  simp only [CollatzResearch.WordTrace]
  refine ⟨16773803378375393280264653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44730142342334382080705741 16773803378375393280264653)
  ·
    refine ⟨6290176266890772480099245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16773803378375393280264653 6290176266890772480099245)
    ·
      refine ⟨2358816100084039680037217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6290176266890772480099245 2358816100084039680037217)
      ·
        refine ⟨1769112075063029760027913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2358816100084039680037217 1769112075063029760027913)
        ·
          refine ⟨1326834056297272320020935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769112075063029760027913 1326834056297272320020935)
          ·
            refine ⟨1990251084445908480031403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326834056297272320020935 1990251084445908480031403)
            ·
              refine ⟨2985376626668862720047105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990251084445908480031403 2985376626668862720047105)
              ·
                refine ⟨2239032470001647040035329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985376626668862720047105 2239032470001647040035329)
                ·
                  refine ⟨1679274352501235280026497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239032470001647040035329 1679274352501235280026497)
                  ·
                    refine ⟨1259455764375926460019873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1679274352501235280026497 1259455764375926460019873)
                    ·
                      refine ⟨944591823281944845014905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259455764375926460019873 944591823281944845014905)
                      ·
                        rfl

theorem cell23_1839586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1839586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839586 prefixEnd_1839586 := by exact prefixLift 1839586
  have htrace : WordTrace (prefixWord ++ tailWord_1839586) baseStart_1839586 baseEnd_1839586 := by
    simpa [prefixWord, tailWord_1839586, baseEnd_1839586] using wordTrace_append hprefix tailTrace_1839586
  have hstable : (prefixWord ++ tailWord_1839586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839586).length < 2 ^ (prefixWord ++ tailWord_1839586).sum := by decide
  have hdescent : baseEnd_1839586 < baseStart_1839586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839591 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_1839591 : Nat := 118140960795 + 1839591 * 2 ^ 59
def prefixEnd_1839591 : Nat := 4983230072969 + 3 ^ 40 * 1839591 * 2
def baseEnd_1839591 : Nat := 944594390685217325452381

theorem tailTrace_1839591 : CollatzResearch.WordTrace tailWord_1839591 prefixEnd_1839591 944594390685217325452381 := by
  unfold tailWord_1839591
  simp only [CollatzResearch.WordTrace]
  refine ⟨67095395878483458974990627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44730263918988972649993751 67095395878483458974990627)
  ·
    refine ⟨100643093817725188462485941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67095395878483458974990627 100643093817725188462485941)
    ·
      refine ⟨9435290045411736418358057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 100643093817725188462485941 9435290045411736418358057)
      ·
        refine ⟨7076467534058802313768543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9435290045411736418358057 7076467534058802313768543)
        ·
          refine ⟨10614701301088203470652815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076467534058802313768543 10614701301088203470652815)
          ·
            refine ⟨15922051951632305205979223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614701301088203470652815 15922051951632305205979223)
            ·
              refine ⟨23883077927448457808968835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15922051951632305205979223 23883077927448457808968835)
              ·
                refine ⟨35824616891172686713453253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23883077927448457808968835 35824616891172686713453253)
                ·
                  refine ⟨6717115667094878758772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35824616891172686713453253 6717115667094878758772485)
                  ·
                    refine ⟨1259459187580289767269841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6717115667094878758772485 1259459187580289767269841)
                    ·
                      refine ⟨944594390685217325452381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259459187580289767269841 944594390685217325452381)
                      ·
                        rfl

theorem cell23_1839591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_1839591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839591 prefixEnd_1839591 := by exact prefixLift 1839591
  have htrace : WordTrace (prefixWord ++ tailWord_1839591) baseStart_1839591 baseEnd_1839591 := by
    simpa [prefixWord, tailWord_1839591, baseEnd_1839591] using wordTrace_append hprefix tailTrace_1839591
  have hstable : (prefixWord ++ tailWord_1839591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839591).length < 2 ^ (prefixWord ++ tailWord_1839591).sum := by decide
  have hdescent : baseEnd_1839591 < baseStart_1839591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839601 : List Nat := [1, 2, 2, 2, 3, 1, 4, 1, 3, 4]
def baseStart_1839601 : Nat := 118140960795 + 1839601 * 2 ^ 59
def prefixEnd_1839601 : Nat := 4983230072969 + 3 ^ 40 * 1839601 * 2
def baseEnd_1839601 : Nat := 314866508497254095442445

theorem tailTrace_1839601 : CollatzResearch.WordTrace tailWord_1839601 prefixEnd_1839601 314866508497254095442445 := by
  unfold tailWord_1839601
  simp only [CollatzResearch.WordTrace]
  refine ⟨67095760608447230682854657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44730507072298153788569771 67095760608447230682854657)
  ·
    refine ⟨50321820456335423012140993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67095760608447230682854657 50321820456335423012140993)
    ·
      refine ⟨37741365342251567259105745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50321820456335423012140993 37741365342251567259105745)
      ·
        refine ⟨28306024006688675444329309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37741365342251567259105745 28306024006688675444329309)
        ·
          refine ⟨10614759002508253291623491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28306024006688675444329309 10614759002508253291623491)
          ·
            refine ⟨15922138503762379937435237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614759002508253291623491 15922138503762379937435237)
            ·
              refine ⟨2985400969455446238269107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15922138503762379937435237 2985400969455446238269107)
              ·
                refine ⟨4478101454183169357403661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985400969455446238269107 4478101454183169357403661)
                ·
                  refine ⟨1679288045318688509026373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4478101454183169357403661 1679288045318688509026373)
                  ·
                    refine ⟨314866508497254095442445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679288045318688509026373 314866508497254095442445)
                    ·
                      rfl

theorem cell23_1839601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_1839601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839601 prefixEnd_1839601 := by exact prefixLift 1839601
  have htrace : WordTrace (prefixWord ++ tailWord_1839601) baseStart_1839601 baseEnd_1839601 := by
    simpa [prefixWord, tailWord_1839601, baseEnd_1839601] using wordTrace_append hprefix tailTrace_1839601
  have hstable : (prefixWord ++ tailWord_1839601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839601).length < 2 ^ (prefixWord ++ tailWord_1839601).sum := by decide
  have hdescent : baseEnd_1839601 < baseStart_1839601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839607 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_1839607 : Nat := 118140960795 + 1839607 * 2 ^ 59
def prefixEnd_1839607 : Nat := 4983230072969 + 3 ^ 40 * 1839607 * 2
def baseEnd_1839607 : Nat := 944602606375689262852307

theorem tailTrace_1839607 : CollatzResearch.WordTrace tailWord_1839607 prefixEnd_1839607 944602606375689262852307 := by
  unfold tailWord_1839607
  simp only [CollatzResearch.WordTrace]
  refine ⟨67095979446425493707573075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44730652964283662471715383 67095979446425493707573075)
  ·
    refine ⟨100643969169638240561359613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67095979446425493707573075 100643969169638240561359613)
    ·
      refine ⟨37741488438614340210509855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100643969169638240561359613 37741488438614340210509855)
      ·
        refine ⟨56612232657921510315764783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37741488438614340210509855 56612232657921510315764783)
        ·
          refine ⟨84918348986882265473647175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56612232657921510315764783 84918348986882265473647175)
          ·
            refine ⟨127377523480323398210470763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84918348986882265473647175 127377523480323398210470763)
            ·
              refine ⟨191066285220485097315706145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127377523480323398210470763 191066285220485097315706145)
              ·
                refine ⟨143299713915363822986779609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 191066285220485097315706145 143299713915363822986779609)
                ·
                  refine ⟨107474785436522867240084707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 143299713915363822986779609 107474785436522867240084707)
                  ·
                    refine ⟨161212178154784300860127061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107474785436522867240084707 161212178154784300860127061)
                    ·
                      refine ⟨944602606375689262852307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 161212178154784300860127061 944602606375689262852307)
                      ·
                        rfl

theorem cell23_1839607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_1839607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839607 prefixEnd_1839607 := by exact prefixLift 1839607
  have htrace : WordTrace (prefixWord ++ tailWord_1839607) baseStart_1839607 baseEnd_1839607 := by
    simpa [prefixWord, tailWord_1839607, baseEnd_1839607] using wordTrace_append hprefix tailTrace_1839607
  have hstable : (prefixWord ++ tailWord_1839607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839607).length < 2 ^ (prefixWord ++ tailWord_1839607).sum := by decide
  have hdescent : baseEnd_1839607 < baseStart_1839607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839624 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 1, 7, 3]
def baseStart_1839624 : Nat := 118140960795 + 1839624 * 2 ^ 59
def prefixEnd_1839624 : Nat := 4983230072969 + 3 ^ 40 * 1839624 * 2
def baseEnd_1839624 : Nat := 944611335546815696339729

theorem tailTrace_1839624 : CollatzResearch.WordTrace tailWord_1839624 prefixEnd_1839624 944611335546815696339729 := by
  unfold tailWord_1839624
  simp only [CollatzResearch.WordTrace]
  refine ⟨33548299743681952805470963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44731066324909270407294617 33548299743681952805470963)
  ·
    refine ⟨50322449615522929208206445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33548299743681952805470963 50322449615522929208206445)
    ·
      refine ⟨18870918605821098453077417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50322449615522929208206445 18870918605821098453077417)
      ·
        refine ⟨14153188954365823839808063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18870918605821098453077417 14153188954365823839808063)
        ·
          refine ⟨21229783431548735759712095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14153188954365823839808063 21229783431548735759712095)
          ·
            refine ⟨31844675147323103639568143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21229783431548735759712095 31844675147323103639568143)
            ·
              refine ⟨47767012720984655459352215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31844675147323103639568143 47767012720984655459352215)
              ·
                refine ⟨71650519081476983189028323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47767012720984655459352215 71650519081476983189028323)
                ·
                  refine ⟨107475778622215474783542485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71650519081476983189028323 107475778622215474783542485)
                  ·
                    refine ⟨2518963561458175190239277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 107475778622215474783542485 2518963561458175190239277)
                    ·
                      refine ⟨944611335546815696339729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2518963561458175190239277 944611335546815696339729)
                      ·
                        rfl

theorem cell23_1839624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 1, 7, 3].length) (baseStart_1839624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839624 prefixEnd_1839624 := by exact prefixLift 1839624
  have htrace : WordTrace (prefixWord ++ tailWord_1839624) baseStart_1839624 baseEnd_1839624 := by
    simpa [prefixWord, tailWord_1839624, baseEnd_1839624] using wordTrace_append hprefix tailTrace_1839624
  have hstable : (prefixWord ++ tailWord_1839624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839624).length < 2 ^ (prefixWord ++ tailWord_1839624).sum := by decide
  have hdescent : baseEnd_1839624 < baseStart_1839624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839652 : List Nat := [2, 3, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1839652 : Nat := 118140960795 + 1839652 * 2 ^ 59
def prefixEnd_1839652 : Nat := 4983230072969 + 3 ^ 40 * 1839652 * 2
def baseEnd_1839652 : Nat := 314875237668380528929867

theorem tailTrace_1839652 : CollatzResearch.WordTrace tailWord_1839652 prefixEnd_1839652 314875237668380528929867 := by
  unfold tailWord_1839652
  simp only [CollatzResearch.WordTrace]
  refine ⟨33548810365631233196480605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44731747154174977595307473 33548810365631233196480605)
  ·
    refine ⟨12580803887111712448680227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33548810365631233196480605 12580803887111712448680227)
    ·
      refine ⟨18871205830667568673020341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12580803887111712448680227 18871205830667568673020341)
      ·
        refine ⟨1769175546625084563095657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18871205830667568673020341 1769175546625084563095657)
        ·
          refine ⟨1326881659968813422321743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769175546625084563095657 1326881659968813422321743)
          ·
            refine ⟨1990322489953220133482615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326881659968813422321743 1990322489953220133482615)
            ·
              refine ⟨2985483734929830200223923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990322489953220133482615 2985483734929830200223923)
              ·
                refine ⟨4478225602394745300335885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985483734929830200223923 4478225602394745300335885)
                ·
                  refine ⟨1679334600898029487625957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4478225602394745300335885 1679334600898029487625957)
                  ·
                    refine ⟨314875237668380528929867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679334600898029487625957 314875237668380528929867)
                    ·
                      rfl

theorem cell23_1839652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1839652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839652 prefixEnd_1839652 := by exact prefixLift 1839652
  have htrace : WordTrace (prefixWord ++ tailWord_1839652) baseStart_1839652 baseEnd_1839652 := by
    simpa [prefixWord, tailWord_1839652, baseEnd_1839652] using wordTrace_append hprefix tailTrace_1839652
  have hstable : (prefixWord ++ tailWord_1839652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839652).length < 2 ^ (prefixWord ++ tailWord_1839652).sum := by decide
  have hdescent : baseEnd_1839652 < baseStart_1839652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839701 : List Nat := [1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1839701 : Nat := 118140960795 + 1839701 * 2 ^ 59
def prefixEnd_1839701 : Nat := 4983230072969 + 3 ^ 40 * 1839701 * 2
def baseEnd_1839701 : Nat := 944650873557211895076875

theorem tailTrace_1839701 : CollatzResearch.WordTrace tailWord_1839701 prefixEnd_1839701 944650873557211895076875 := by
  unfold tailWord_1839701
  simp only [CollatzResearch.WordTrace]
  refine ⟨67099407908084947761494957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44732938605389965174329971 67099407908084947761494957)
  ·
    refine ⟨25162277965531855410560609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67099407908084947761494957 25162277965531855410560609)
    ·
      refine ⟨18871708474148891557920457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25162277965531855410560609 18871708474148891557920457)
      ·
        refine ⟨14153781355611668668440343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18871708474148891557920457 14153781355611668668440343)
        ·
          refine ⟨21230672033417503002660515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14153781355611668668440343 21230672033417503002660515)
          ·
            refine ⟨31846008050126254503990773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21230672033417503002660515 31846008050126254503990773)
            ·
              refine ⟨2985563254699336359749135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31846008050126254503990773 2985563254699336359749135)
              ·
                refine ⟨4478344882049004539623703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985563254699336359749135 4478344882049004539623703)
                ·
                  refine ⟨6717517323073506809435555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478344882049004539623703 6717517323073506809435555)
                  ·
                    refine ⟨10076275984610260214153333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6717517323073506809435555 10076275984610260214153333)
                    ·
                      refine ⟨944650873557211895076875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10076275984610260214153333 944650873557211895076875)
                      ·
                        rfl

theorem cell23_1839701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1839701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839701 prefixEnd_1839701 := by exact prefixLift 1839701
  have htrace : WordTrace (prefixWord ++ tailWord_1839701) baseStart_1839701 baseEnd_1839701 := by
    simpa [prefixWord, tailWord_1839701, baseEnd_1839701] using wordTrace_append hprefix tailTrace_1839701
  have hstable : (prefixWord ++ tailWord_1839701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839701).length < 2 ^ (prefixWord ++ tailWord_1839701).sum := by decide
  have hdescent : baseEnd_1839701 < baseStart_1839701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839724 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 6]
def baseStart_1839724 : Nat := 118140960795 + 1839724 * 2 ^ 59
def prefixEnd_1839724 : Nat := 4983230072969 + 3 ^ 40 * 1839724 * 2
def baseEnd_1839724 : Nat := 944662683612265305089269

theorem tailTrace_1839724 : CollatzResearch.WordTrace tailWord_1839724 prefixEnd_1839724 944662683612265305089269 := by
  unfold tailWord_1839724
  simp only [CollatzResearch.WordTrace]
  refine ⟨33550123393500811344791113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44733497858001081793054817 33550123393500811344791113)
  ·
    refine ⟨25162592545125608508593335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33550123393500811344791113 25162592545125608508593335)
    ·
      refine ⟨37743888817688412762890003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25162592545125608508593335 37743888817688412762890003)
      ·
        refine ⟨56615833226532619144335005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37743888817688412762890003 56615833226532619144335005)
        ·
          refine ⟨21230937459949732179125627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56615833226532619144335005 21230937459949732179125627)
          ·
            refine ⟨31846406189924598268688441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21230937459949732179125627 31846406189924598268688441)
            ·
              refine ⟨23884804642443448701516331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31846406189924598268688441 23884804642443448701516331)
              ·
                refine ⟨35827206963665173052274497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23884804642443448701516331 35827206963665173052274497)
                ·
                  refine ⟨26870405222748879789205873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35827206963665173052274497 26870405222748879789205873)
                  ·
                    refine ⟨20152803917061659841904405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26870405222748879789205873 20152803917061659841904405)
                    ·
                      refine ⟨944662683612265305089269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 20152803917061659841904405 944662683612265305089269)
                      ·
                        rfl

theorem cell23_1839724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 6].length) (baseStart_1839724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839724 prefixEnd_1839724 := by exact prefixLift 1839724
  have htrace : WordTrace (prefixWord ++ tailWord_1839724) baseStart_1839724 baseEnd_1839724 := by
    simpa [prefixWord, tailWord_1839724, baseEnd_1839724] using wordTrace_append hprefix tailTrace_1839724
  have hstable : (prefixWord ++ tailWord_1839724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839724).length < 2 ^ (prefixWord ++ tailWord_1839724).sum := by decide
  have hdescent : baseEnd_1839724 < baseStart_1839724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839728 : List Nat := [2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4]
def baseStart_1839728 : Nat := 118140960795 + 1839728 * 2 ^ 59
def prefixEnd_1839728 : Nat := 4983230072969 + 3 ^ 40 * 1839728 * 2
def baseEnd_1839728 : Nat := 944664737534883289439251

theorem tailTrace_1839728 : CollatzResearch.WordTrace tailWord_1839728 prefixEnd_1839728 944664737534883289439251 := by
  unfold tailWord_1839728
  simp only [CollatzResearch.WordTrace]
  refine ⟨33550196339493565686363919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44733595119324754248485225 33550196339493565686363919)
  ·
    refine ⟨50325294509240348529545879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33550196339493565686363919 50325294509240348529545879)
    ·
      refine ⟨75487941763860522794318819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50325294509240348529545879 75487941763860522794318819)
      ·
        refine ⟨113231912645790784191478229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75487941763860522794318819 113231912645790784191478229)
        ·
          refine ⟨2653872952635721504487771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 113231912645790784191478229 2653872952635721504487771)
          ·
            refine ⟨3980809428953582256731657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653872952635721504487771 3980809428953582256731657)
            ·
              refine ⟨2985607071715186692548743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3980809428953582256731657 2985607071715186692548743)
              ·
                refine ⟨4478410607572780038823115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985607071715186692548743 4478410607572780038823115)
                ·
                  refine ⟨6717615911359170058234673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478410607572780038823115 6717615911359170058234673)
                  ·
                    refine ⟨5038211933519377543676005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6717615911359170058234673 5038211933519377543676005)
                    ·
                      refine ⟨944664737534883289439251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5038211933519377543676005 944664737534883289439251)
                      ·
                        rfl

theorem cell23_1839728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 1, 2, 4].length) (baseStart_1839728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839728 prefixEnd_1839728 := by exact prefixLift 1839728
  have htrace : WordTrace (prefixWord ++ tailWord_1839728) baseStart_1839728 baseEnd_1839728 := by
    simpa [prefixWord, tailWord_1839728, baseEnd_1839728] using wordTrace_append hprefix tailTrace_1839728
  have hstable : (prefixWord ++ tailWord_1839728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839728).length < 2 ^ (prefixWord ++ tailWord_1839728).sum := by decide
  have hdescent : baseEnd_1839728 < baseStart_1839728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839746 : List Nat := [3, 4, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1839746 : Nat := 118140960795 + 1839746 * 2 ^ 59
def prefixEnd_1839746 : Nat := 4983230072969 + 3 ^ 40 * 1839746 * 2
def baseEnd_1839746 : Nat := 314891326728888073004723

theorem tailTrace_1839746 : CollatzResearch.WordTrace tailWord_1839746 prefixEnd_1839746 314891326728888073004723 := by
  unfold tailWord_1839746
  simp only [CollatzResearch.WordTrace]
  refine ⟨16775262298230480111720773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44734032795281280297922061 16775262298230480111720773)
  ·
    refine ⟨3145361680918215020947645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16775262298230480111720773 3145361680918215020947645)
    ·
      refine ⟨1179510630344330632855367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3145361680918215020947645 1179510630344330632855367)
      ·
        refine ⟨1769265945516495949283051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179510630344330632855367 1769265945516495949283051)
        ·
          refine ⟨2653898918274743923924577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769265945516495949283051 2653898918274743923924577)
          ·
            refine ⟨1990424188706057942943433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2653898918274743923924577 1990424188706057942943433)
            ·
              refine ⟨1492818141529543457207575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990424188706057942943433 1492818141529543457207575)
              ·
                refine ⟨2239227212294315185811363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492818141529543457207575 2239227212294315185811363)
                ·
                  refine ⟨3358840818441472778717045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239227212294315185811363 3358840818441472778717045)
                  ·
                    refine ⟨314891326728888073004723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3358840818441472778717045 314891326728888073004723)
                    ·
                      rfl

theorem cell23_1839746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1839746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839746 prefixEnd_1839746 := by exact prefixLift 1839746
  have htrace : WordTrace (prefixWord ++ tailWord_1839746) baseStart_1839746 baseEnd_1839746 := by
    simpa [prefixWord, tailWord_1839746, baseEnd_1839746] using wordTrace_append hprefix tailTrace_1839746
  have hstable : (prefixWord ++ tailWord_1839746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839746).length < 2 ^ (prefixWord ++ tailWord_1839746).sum := by decide
  have hdescent : baseEnd_1839746 < baseStart_1839746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839748 : List Nat := [2, 3, 2, 1, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1839748 : Nat := 118140960795 + 1839748 * 2 ^ 59
def prefixEnd_1839748 : Nat := 4983230072969 + 3 ^ 40 * 1839748 * 2
def baseEnd_1839748 : Nat := 944675007147973211189159

theorem tailTrace_1839748 : CollatzResearch.WordTrace tailWord_1839748 prefixEnd_1839748 944675007147973211189159 := by
  unfold tailWord_1839748
  simp only [CollatzResearch.WordTrace]
  refine ⟨33550561069457337394227949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44734081425943116525637265 33550561069457337394227949)
  ·
    refine ⟨12581460401046501522835481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33550561069457337394227949 12581460401046501522835481)
    ·
      refine ⟨9436095300784876142126611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12581460401046501522835481 9436095300784876142126611)
      ·
        refine ⟨14154142951177314213189917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9436095300784876142126611 14154142951177314213189917)
        ·
          refine ⟨5307803606691492829946219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14154142951177314213189917 5307803606691492829946219)
          ·
            refine ⟨7961705410037239244919329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307803606691492829946219 7961705410037239244919329)
            ·
              refine ⟨5971279057527929433689497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7961705410037239244919329 5971279057527929433689497)
              ·
                refine ⟨4478459293145947075267123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5971279057527929433689497 4478459293145947075267123)
                ·
                  refine ⟨6717688939718920612900685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4478459293145947075267123 6717688939718920612900685)
                  ·
                    refine ⟨2519133352394595229837757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6717688939718920612900685 2519133352394595229837757)
                    ·
                      refine ⟨944675007147973211189159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2519133352394595229837757 944675007147973211189159)
                      ·
                        rfl

theorem cell23_1839748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1839748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839748 prefixEnd_1839748 := by exact prefixLift 1839748
  have htrace : WordTrace (prefixWord ++ tailWord_1839748) baseStart_1839748 baseEnd_1839748 := by
    simpa [prefixWord, tailWord_1839748, baseEnd_1839748] using wordTrace_append hprefix tailTrace_1839748
  have hstable : (prefixWord ++ tailWord_1839748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839748).length < 2 ^ (prefixWord ++ tailWord_1839748).sum := by decide
  have hdescent : baseEnd_1839748 < baseStart_1839748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839805 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 4, 2, 2]
def baseStart_1839805 : Nat := 118140960795 + 1839805 * 2 ^ 59
def prefixEnd_1839805 : Nat := 4983230072969 + 3 ^ 40 * 1839805 * 2
def baseEnd_1839805 : Nat := 944704275545279488176397

theorem tailTrace_1839805 : CollatzResearch.WordTrace tailWord_1839805 prefixEnd_1839805 944704275545279488176397 := by
  unfold tailWord_1839805
  simp only [CollatzResearch.WordTrace]
  refine ⟨67103201099708173523280869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44735467399805449015520579 67103201099708173523280869)
  ·
    refine ⟨12581850206195282535615163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67103201099708173523280869 12581850206195282535615163)
    ·
      refine ⟨18872775309292923803422745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12581850206195282535615163 18872775309292923803422745)
      ·
        refine ⟨14154581481969692852567059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18872775309292923803422745 14154581481969692852567059)
        ·
          refine ⟨21231872222954539278850589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14154581481969692852567059 21231872222954539278850589)
          ·
            refine ⟨7961952083607952229568971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21231872222954539278850589 7961952083607952229568971)
            ·
              refine ⟨11942928125411928344353457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7961952083607952229568971 11942928125411928344353457)
              ·
                refine ⟨8957196094058946258265093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11942928125411928344353457 8957196094058946258265093)
                ·
                  refine ⟨1679474267636052423424705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8957196094058946258265093 1679474267636052423424705)
                  ·
                    refine ⟨1259605700727039317568529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1679474267636052423424705 1259605700727039317568529)
                    ·
                      refine ⟨944704275545279488176397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259605700727039317568529 944704275545279488176397)
                      ·
                        rfl

theorem cell23_1839805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 2, 2].length) (baseStart_1839805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839805 prefixEnd_1839805 := by exact prefixLift 1839805
  have htrace : WordTrace (prefixWord ++ tailWord_1839805) baseStart_1839805 baseEnd_1839805 := by
    simpa [prefixWord, tailWord_1839805, baseEnd_1839805] using wordTrace_append hprefix tailTrace_1839805
  have hstable : (prefixWord ++ tailWord_1839805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839805).length < 2 ^ (prefixWord ++ tailWord_1839805).sum := by decide
  have hdescent : baseEnd_1839805 < baseStart_1839805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839839 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 2, 2, 2]
def baseStart_1839839 : Nat := 118140960795 + 1839839 * 2 ^ 59
def prefixEnd_1839839 : Nat := 4983230072969 + 3 ^ 40 * 1839839 * 2
def baseEnd_1839839 : Nat := 944721733887532355151241

theorem tailTrace_1839839 : CollatzResearch.WordTrace tailWord_1839839 prefixEnd_1839839 944721733887532355151241 := by
  unfold tailWord_1839839
  simp only [CollatzResearch.WordTrace]
  refine ⟨67104441181584997330018571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44736294121056664886679047 67104441181584997330018571)
  ·
    refine ⟨100656661772377495995027857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67104441181584997330018571 100656661772377495995027857)
    ·
      refine ⟨75492496329283121996270893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100656661772377495995027857 75492496329283121996270893)
      ·
        refine ⟨28309686123481170748601585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75492496329283121996270893 28309686123481170748601585)
        ·
          refine ⟨21232264592610878061451189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28309686123481170748601585 21232264592610878061451189)
          ·
            refine ⟨1990524805557269818261049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21232264592610878061451189 1990524805557269818261049)
            ·
              refine ⟨1492893604167952363695787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990524805557269818261049 1492893604167952363695787)
              ·
                refine ⟨2239340406251928545543681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492893604167952363695787 2239340406251928545543681)
                ·
                  refine ⟨1679505304688946409157761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239340406251928545543681 1679505304688946409157761)
                  ·
                    refine ⟨1259628978516709806868321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1679505304688946409157761 1259628978516709806868321)
                    ·
                      refine ⟨944721733887532355151241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259628978516709806868321 944721733887532355151241)
                      ·
                        rfl

theorem cell23_1839839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_1839839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839839 prefixEnd_1839839 := by exact prefixLift 1839839
  have htrace : WordTrace (prefixWord ++ tailWord_1839839) baseStart_1839839 baseEnd_1839839 := by
    simpa [prefixWord, tailWord_1839839, baseEnd_1839839] using wordTrace_append hprefix tailTrace_1839839
  have hstable : (prefixWord ++ tailWord_1839839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839839).length < 2 ^ (prefixWord ++ tailWord_1839839).sum := by decide
  have hdescent : baseEnd_1839839 < baseStart_1839839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839858 : List Nat := [3, 2, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_1839858 : Nat := 118140960795 + 1839858 * 2 ^ 59
def prefixEnd_1839858 : Nat := 4983230072969 + 3 ^ 40 * 1839858 * 2
def baseEnd_1839858 : Nat := 314910496673322593604551

theorem tailTrace_1839858 : CollatzResearch.WordTrace tailWord_1839858 prefixEnd_1839858 314910496673322593604551 := by
  unfold tailWord_1839858
  simp only [CollatzResearch.WordTrace]
  refine ⟨16776283542129040893740057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44736756112344109049973485 16776283542129040893740057)
  ·
    refine ⟨12582212656596780670305043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16776283542129040893740057 12582212656596780670305043)
    ·
      refine ⟨18873318984895171005457565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12582212656596780670305043 18873318984895171005457565)
      ·
        refine ⟨7077494619335689127046587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18873318984895171005457565 7077494619335689127046587)
        ·
          refine ⟨10616241929003533690569881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077494619335689127046587 10616241929003533690569881)
          ·
            refine ⟨7962181446752650267927411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10616241929003533690569881 7962181446752650267927411)
            ·
              refine ⟨11943272170128975401891117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962181446752650267927411 11943272170128975401891117)
              ·
                refine ⟨4478727063798365775709169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11943272170128975401891117 4478727063798365775709169)
                ·
                  refine ⟨3359045297848774331781877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4478727063798365775709169 3359045297848774331781877)
                  ·
                    refine ⟨314910496673322593604551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3359045297848774331781877 314910496673322593604551)
                    ·
                      rfl

theorem cell23_1839858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_1839858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839858 prefixEnd_1839858 := by exact prefixLift 1839858
  have htrace : WordTrace (prefixWord ++ tailWord_1839858) baseStart_1839858 baseEnd_1839858 := by
    simpa [prefixWord, tailWord_1839858, baseEnd_1839858] using wordTrace_append hprefix tailTrace_1839858
  have hstable : (prefixWord ++ tailWord_1839858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839858).length < 2 ^ (prefixWord ++ tailWord_1839858).sum := by decide
  have hdescent : baseEnd_1839858 < baseStart_1839858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839898 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1839898 : Nat := 118140960795 + 1839898 * 2 ^ 59
def prefixEnd_1839898 : Nat := 4983230072969 + 3 ^ 40 * 1839898 * 2
def baseEnd_1839898 : Nat := 944752029246147624313469

theorem tailTrace_1839898 : CollatzResearch.WordTrace tailWord_1839898 prefixEnd_1839898 944752029246147624313469 := by
  unfold tailWord_1839898
  simp only [CollatzResearch.WordTrace]
  refine ⟨16776648272092812601604087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44737728725580833604277565 16776648272092812601604087)
  ·
    refine ⟨25164972408139218902406131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16776648272092812601604087 25164972408139218902406131)
    ·
      refine ⟨37747458612208828353609197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25164972408139218902406131 37747458612208828353609197)
      ·
        refine ⟨14155296979578310632603449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37747458612208828353609197 14155296979578310632603449)
        ·
          refine ⟨10616472734683732974452587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14155296979578310632603449 10616472734683732974452587)
          ·
            refine ⟨15924709102025599461678881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616472734683732974452587 15924709102025599461678881)
            ·
              refine ⟨11943531826519199596259161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15924709102025599461678881 11943531826519199596259161)
              ·
                refine ⟨8957648869889399697194371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11943531826519199596259161 8957648869889399697194371)
                ·
                  refine ⟨13436473304834099545791557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8957648869889399697194371 13436473304834099545791557)
                  ·
                    refine ⟨2519338744656393664835917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13436473304834099545791557 2519338744656393664835917)
                    ·
                      refine ⟨944752029246147624313469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2519338744656393664835917 944752029246147624313469)
                      ·
                        rfl

theorem cell23_1839898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1839898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839898 prefixEnd_1839898 := by exact prefixLift 1839898
  have htrace : WordTrace (prefixWord ++ tailWord_1839898) baseStart_1839898 baseEnd_1839898 := by
    simpa [prefixWord, tailWord_1839898, baseEnd_1839898] using wordTrace_append hprefix tailTrace_1839898
  have hstable : (prefixWord ++ tailWord_1839898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839898).length < 2 ^ (prefixWord ++ tailWord_1839898).sum := by decide
  have hdescent : baseEnd_1839898 < baseStart_1839898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839922 : List Nat := [3, 2, 1, 1, 3, 1, 4, 3, 1, 4]
def baseStart_1839922 : Nat := 118140960795 + 1839922 * 2 ^ 59
def prefixEnd_1839922 : Nat := 4983230072969 + 3 ^ 40 * 1839922 * 2
def baseEnd_1839922 : Nat := 314921450927285176804453

theorem tailTrace_1839922 : CollatzResearch.WordTrace tailWord_1839922 prefixEnd_1839922 314921450927285176804453 := by
  unfold tailWord_1839922
  simp only [CollatzResearch.WordTrace]
  refine ⟨16776867110071075626322505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44738312293522868336860013 16776867110071075626322505)
  ·
    refine ⟨12582650332553306719741879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16776867110071075626322505 12582650332553306719741879)
    ·
      refine ⟨18873975498829960079612819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12582650332553306719741879 18873975498829960079612819)
      ·
        refine ⟨28310963248244940119419229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18873975498829960079612819 28310963248244940119419229)
        ·
          refine ⟨10616611218091852544782211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28310963248244940119419229 10616611218091852544782211)
          ·
            refine ⟨15924916827137778817173317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616611218091852544782211 15924916827137778817173317)
            ·
              refine ⟨2985921905088333528219997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15924916827137778817173317 2985921905088333528219997)
              ·
                refine ⟨1119720714408125073082499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2985921905088333528219997 1119720714408125073082499)
                ·
                  refine ⟨1679581071612187609623749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119720714408125073082499 1679581071612187609623749)
                  ·
                    refine ⟨314921450927285176804453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679581071612187609623749 314921450927285176804453)
                    ·
                      rfl

theorem cell23_1839922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_1839922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839922 prefixEnd_1839922 := by exact prefixLift 1839922
  have htrace : WordTrace (prefixWord ++ tailWord_1839922) baseStart_1839922 baseEnd_1839922 := by
    simpa [prefixWord, tailWord_1839922, baseEnd_1839922] using wordTrace_append hprefix tailTrace_1839922
  have hstable : (prefixWord ++ tailWord_1839922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839922).length < 2 ^ (prefixWord ++ tailWord_1839922).sum := by decide
  have hdescent : baseEnd_1839922 < baseStart_1839922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839935 : List Nat := [1, 1, 2, 2, 5, 3, 1, 2, 6]
def baseStart_1839935 : Nat := 118140960795 + 1839935 * 2 ^ 59
def prefixEnd_1839935 : Nat := 4983230072969 + 3 ^ 40 * 1839935 * 2
def baseEnd_1839935 : Nat := 104974558670040442172311

theorem tailTrace_1839935 : CollatzResearch.WordTrace tailWord_1839935 prefixEnd_1839935 104974558670040442172311 := by
  unfold tailWord_1839935
  simp only [CollatzResearch.WordTrace]
  refine ⟨67107942589237205725513259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44738628392824803817008839 67107942589237205725513259)
  ·
    refine ⟨100661913883855808588269889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67107942589237205725513259 100661913883855808588269889)
    ·
      refine ⟨75496435412891856441202417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100661913883855808588269889 75496435412891856441202417)
      ·
        refine ⟨56622326559668892330901813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75496435412891856441202417 56622326559668892330901813)
        ·
          refine ⟨5308343114968958656022045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56622326559668892330901813 5308343114968958656022045)
          ·
            refine ⟨1990628668113359496008267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5308343114968958656022045 1990628668113359496008267)
            ·
              refine ⟨2985943002170039244012401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990628668113359496008267 2985943002170039244012401)
              ·
                refine ⟨2239457251627529433009301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985943002170039244012401 2239457251627529433009301)
                ·
                  refine ⟨104974558670040442172311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2239457251627529433009301 104974558670040442172311)
                  ·
                    rfl

theorem cell23_1839935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 2, 6].length) (baseStart_1839935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839935 prefixEnd_1839935 := by exact prefixLift 1839935
  have htrace : WordTrace (prefixWord ++ tailWord_1839935) baseStart_1839935 baseEnd_1839935 := by
    simpa [prefixWord, tailWord_1839935, baseEnd_1839935] using wordTrace_append hprefix tailTrace_1839935
  have hstable : (prefixWord ++ tailWord_1839935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839935).length < 2 ^ (prefixWord ++ tailWord_1839935).sum := by decide
  have hdescent : baseEnd_1839935 < baseStart_1839935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839941 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_1839941 : Nat := 118140960795 + 1839941 * 2 ^ 59
def prefixEnd_1839941 : Nat := 4983230072969 + 3 ^ 40 * 1839941 * 2
def baseEnd_1839941 : Nat := 944774108914290956075771

theorem tailTrace_1839941 : CollatzResearch.WordTrace tailWord_1839941 prefixEnd_1839941 944774108914290956075771 := by
  unfold tailWord_1839941
  simp only [CollatzResearch.WordTrace]
  refine ⟨67108161427215468750231677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44738774284810312500154451 67108161427215468750231677)
  ·
    refine ⟨25165560535205800781336879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67108161427215468750231677 25165560535205800781336879)
    ·
      refine ⟨37748340802808701172005319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25165560535205800781336879 37748340802808701172005319)
      ·
        refine ⟨56622511204213051758007979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37748340802808701172005319 56622511204213051758007979)
        ·
          refine ⟨84933766806319577637011969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56622511204213051758007979 84933766806319577637011969)
          ·
            refine ⟨63700325104739683227758977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84933766806319577637011969 63700325104739683227758977)
            ·
              refine ⟨47775243828554762420819233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63700325104739683227758977 47775243828554762420819233)
              ·
                refine ⟨35831432871416071815614425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47775243828554762420819233 35831432871416071815614425)
                ·
                  refine ⟨26873574653562053861710819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35831432871416071815614425 26873574653562053861710819)
                  ·
                    refine ⟨40310361980343080792566229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26873574653562053861710819 40310361980343080792566229)
                    ·
                      refine ⟨944774108914290956075771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 40310361980343080792566229 944774108914290956075771)
                      ·
                        rfl

theorem cell23_1839941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_1839941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839941 prefixEnd_1839941 := by exact prefixLift 1839941
  have htrace : WordTrace (prefixWord ++ tailWord_1839941) baseStart_1839941 baseEnd_1839941 := by
    simpa [prefixWord, tailWord_1839941, baseEnd_1839941] using wordTrace_append hprefix tailTrace_1839941
  have hstable : (prefixWord ++ tailWord_1839941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839941).length < 2 ^ (prefixWord ++ tailWord_1839941).sum := by decide
  have hdescent : baseEnd_1839941 < baseStart_1839941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839945 : List Nat := [1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 3]
def baseStart_1839945 : Nat := 118140960795 + 1839945 * 2 ^ 59
def prefixEnd_1839945 : Nat := 4983230072969 + 3 ^ 40 * 1839945 * 2
def baseEnd_1839945 : Nat := 944776162836908940425753

theorem tailTrace_1839945 : CollatzResearch.WordTrace tailWord_1839945 prefixEnd_1839945 944776162836908940425753 := by
  unfold tailWord_1839945
  simp only [CollatzResearch.WordTrace]
  refine ⟨67108307319200977433377289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44738871546133984955584859 67108307319200977433377289)
  ·
    refine ⟨50331230489400733075032967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67108307319200977433377289 50331230489400733075032967)
    ·
      refine ⟨75496845734101099612549451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50331230489400733075032967 75496845734101099612549451)
      ·
        refine ⟨113245268601151649418824177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75496845734101099612549451 113245268601151649418824177)
        ·
          refine ⟨84933951450863737064118133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113245268601151649418824177 84933951450863737064118133)
          ·
            refine ⟨7962557948518475349761075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84933951450863737064118133 7962557948518475349761075)
            ·
              refine ⟨11943836922777713024641613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962557948518475349761075 11943836922777713024641613)
              ·
                refine ⟨4478938846041642384240605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11943836922777713024641613 4478938846041642384240605)
                ·
                  refine ⟨1679602067265615894090227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4478938846041642384240605 1679602067265615894090227)
                  ·
                    refine ⟨2519403100898423841135341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1679602067265615894090227 2519403100898423841135341)
                    ·
                      refine ⟨944776162836908940425753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2519403100898423841135341 944776162836908940425753)
                      ·
                        rfl

theorem cell23_1839945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 1, 3].length) (baseStart_1839945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839945 prefixEnd_1839945 := by exact prefixLift 1839945
  have htrace : WordTrace (prefixWord ++ tailWord_1839945) baseStart_1839945 baseEnd_1839945 := by
    simpa [prefixWord, tailWord_1839945, baseEnd_1839945] using wordTrace_append hprefix tailTrace_1839945
  have hstable : (prefixWord ++ tailWord_1839945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839945).length < 2 ^ (prefixWord ++ tailWord_1839945).sum := by decide
  have hdescent : baseEnd_1839945 < baseStart_1839945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1839985 : List Nat := [1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 4]
def baseStart_1839985 : Nat := 118140960795 + 1839985 * 2 ^ 59
def prefixEnd_1839985 : Nat := 4983230072969 + 3 ^ 40 * 1839985 * 2
def baseEnd_1839985 : Nat := 944796702063088783925569

theorem tailTrace_1839985 : CollatzResearch.WordTrace tailWord_1839985 prefixEnd_1839985 944796702063088783925569 := by
  unfold tailWord_1839985
  simp only [CollatzResearch.WordTrace]
  refine ⟨67109766239056064264833409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44739844159370709509888939 67109766239056064264833409)
  ·
    refine ⟨50332324679292048198625057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67109766239056064264833409 50332324679292048198625057)
    ·
      refine ⟨37749243509469036148968793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50332324679292048198625057 37749243509469036148968793)
      ·
        refine ⟨28311932632101777111726595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37749243509469036148968793 28311932632101777111726595)
        ·
          refine ⟨42467898948152665667589893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28311932632101777111726595 42467898948152665667589893)
          ·
            refine ⟨7962731052778624812673105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42467898948152665667589893 7962731052778624812673105)
            ·
              refine ⟨5972048289583968609504829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7962731052778624812673105 5972048289583968609504829)
              ·
                refine ⟨2239518108593988228564311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5972048289583968609504829 2239518108593988228564311)
                ·
                  refine ⟨3359277162890982342846467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239518108593988228564311 3359277162890982342846467)
                  ·
                    refine ⟨5038915744336473514269701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3359277162890982342846467 5038915744336473514269701)
                    ·
                      refine ⟨944796702063088783925569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5038915744336473514269701 944796702063088783925569)
                      ·
                        rfl

theorem cell23_1839985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_1839985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1839985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1839985 prefixEnd_1839985 := by exact prefixLift 1839985
  have htrace : WordTrace (prefixWord ++ tailWord_1839985) baseStart_1839985 baseEnd_1839985 := by
    simpa [prefixWord, tailWord_1839985, baseEnd_1839985] using wordTrace_append hprefix tailTrace_1839985
  have hstable : (prefixWord ++ tailWord_1839985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1839985).length < 2 ^ (prefixWord ++ tailWord_1839985).sum := by decide
  have hdescent : baseEnd_1839985 < baseStart_1839985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1839985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840008 : List Nat := [2, 1, 3, 3, 2, 1, 1, 10]
def baseStart_1840008 : Nat := 118140960795 + 1840008 * 2 ^ 59
def prefixEnd_1840008 : Nat := 4983230072969 + 3 ^ 40 * 1840008 * 2
def baseEnd_1840008 : Nat := 34992907856227488664369

theorem tailTrace_1840008 : CollatzResearch.WordTrace tailWord_1840008 prefixEnd_1840008 34992907856227488664369 := by
  unfold tailWord_1840008
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555302558986369596460339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44740403411981826128613785 33555302558986369596460339)
  ·
    refine ⟨50332953838479554394690509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33555302558986369596460339 50332953838479554394690509)
    ·
      refine ⟨18874857689429832898008941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50332953838479554394690509 18874857689429832898008941)
      ·
        refine ⟨7078071633536187336753353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18874857689429832898008941 7078071633536187336753353)
        ·
          refine ⟨5308553725152140502565015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7078071633536187336753353 5308553725152140502565015)
          ·
            refine ⟨7962830587728210753847523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5308553725152140502565015 7962830587728210753847523)
            ·
              refine ⟨11944245881592316130771285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7962830587728210753847523 11944245881592316130771285)
              ·
                refine ⟨34992907856227488664369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 11944245881592316130771285 34992907856227488664369)
                ·
                  rfl

theorem cell23_1840008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 10].length) (baseStart_1840008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840008 prefixEnd_1840008 := by exact prefixLift 1840008
  have htrace : WordTrace (prefixWord ++ tailWord_1840008) baseStart_1840008 baseEnd_1840008 := by
    simpa [prefixWord, tailWord_1840008, baseEnd_1840008] using wordTrace_append hprefix tailTrace_1840008
  have hstable : (prefixWord ++ tailWord_1840008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840008).length < 2 ^ (prefixWord ++ tailWord_1840008).sum := by decide
  have hdescent : baseEnd_1840008 < baseStart_1840008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840012 : List Nat := [2, 2, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_1840012 : Nat := 118140960795 + 1840012 * 2 ^ 59
def prefixEnd_1840012 : Nat := 4983230072969 + 3 ^ 40 * 1840012 * 2
def baseEnd_1840012 : Nat := 314936855346920059429315

theorem tailTrace_1840012 : CollatzResearch.WordTrace tailWord_1840012 prefixEnd_1840012 314936855346920059429315 := by
  unfold tailWord_1840012
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555375504979123938033145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 44740500673305498584044193 33555375504979123938033145)
  ·
    refine ⟨25166531628734342953524859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33555375504979123938033145 25166531628734342953524859)
    ·
      refine ⟨37749797443101514430287289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25166531628734342953524859 37749797443101514430287289)
      ·
        refine ⟨28312348082326135822715467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37749797443101514430287289 28312348082326135822715467)
        ·
          refine ⟨42468522123489203734073201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28312348082326135822715467 42468522123489203734073201)
          ·
            refine ⟨31851391592616902800554901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42468522123489203734073201 31851391592616902800554901)
            ·
              refine ⟨1493033980903917318776011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31851391592616902800554901 1493033980903917318776011)
              ·
                refine ⟨2239550971355875978164017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493033980903917318776011 2239550971355875978164017)
                ·
                  refine ⟨1679663228516906983623013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239550971355875978164017 1679663228516906983623013)
                  ·
                    refine ⟨314936855346920059429315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679663228516906983623013 314936855346920059429315)
                    ·
                      rfl

theorem cell23_1840012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_1840012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840012 prefixEnd_1840012 := by exact prefixLift 1840012
  have htrace : WordTrace (prefixWord ++ tailWord_1840012) baseStart_1840012 baseEnd_1840012 := by
    simpa [prefixWord, tailWord_1840012, baseEnd_1840012] using wordTrace_append hprefix tailTrace_1840012
  have hstable : (prefixWord ++ tailWord_1840012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840012).length < 2 ^ (prefixWord ++ tailWord_1840012).sum := by decide
  have hdescent : baseEnd_1840012 < baseStart_1840012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840035 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 3]
def baseStart_1840035 : Nat := 118140960795 + 1840035 * 2 ^ 59
def prefixEnd_1840035 : Nat := 4983230072969 + 3 ^ 40 * 1840035 * 2
def baseEnd_1840035 : Nat := 944822376095813588300339

theorem tailTrace_1840035 : CollatzResearch.WordTrace tailWord_1840035 prefixEnd_1840035 944822376095813588300339 := by
  unfold tailWord_1840035
  simp only [CollatzResearch.WordTrace]
  refine ⟨67111589888874922804153559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44741059925916615202769039 67111589888874922804153559)
  ·
    refine ⟨100667384833312384206230339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67111589888874922804153559 100667384833312384206230339)
    ·
      refine ⟨151001077249968576309345509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100667384833312384206230339 151001077249968576309345509)
      ·
        refine ⟨28312701984369108058002283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 151001077249968576309345509 28312701984369108058002283)
        ·
          refine ⟨42469052976553662087003425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28312701984369108058002283 42469052976553662087003425)
          ·
            refine ⟨31851789732415246565252569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42469052976553662087003425 31851789732415246565252569)
            ·
              refine ⟨23888842299311434923939427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31851789732415246565252569 23888842299311434923939427)
              ·
                refine ⟨35833263448967152385909141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23888842299311434923939427 35833263448967152385909141)
                ·
                  refine ⟨1679684224170335268089491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 35833263448967152385909141 1679684224170335268089491)
                  ·
                    refine ⟨2519526336255502902134237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1679684224170335268089491 2519526336255502902134237)
                    ·
                      refine ⟨944822376095813588300339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2519526336255502902134237 944822376095813588300339)
                      ·
                        rfl

theorem cell23_1840035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_1840035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840035 prefixEnd_1840035 := by exact prefixLift 1840035
  have htrace : WordTrace (prefixWord ++ tailWord_1840035) baseStart_1840035 baseEnd_1840035 := by
    simpa [prefixWord, tailWord_1840035, baseEnd_1840035] using wordTrace_append hprefix tailTrace_1840035
  have hstable : (prefixWord ++ tailWord_1840035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840035).length < 2 ^ (prefixWord ++ tailWord_1840035).sum := by decide
  have hdescent : baseEnd_1840035 < baseStart_1840035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840039 : List Nat := [1, 1, 6, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1840039 : Nat := 118140960795 + 1840039 * 2 ^ 59
def prefixEnd_1840039 : Nat := 4983230072969 + 3 ^ 40 * 1840039 * 2
def baseEnd_1840039 : Nat := 944824430018431572650321

theorem tailTrace_1840039 : CollatzResearch.WordTrace tailWord_1840039 prefixEnd_1840039 944824430018431572650321 := by
  unfold tailWord_1840039
  simp only [CollatzResearch.WordTrace]
  refine ⟨67111735780860431487299171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 44741157187240287658199447 67111735780860431487299171)
  ·
    refine ⟨100667603671290647230948757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67111735780860431487299171 100667603671290647230948757)
    ·
      refine ⟨4718793922091749088950723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100667603671290647230948757 4718793922091749088950723)
      ·
        refine ⟨7078190883137623633426085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4718793922091749088950723 7078190883137623633426085)
        ·
          refine ⟨1327160790588304431267391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7078190883137623633426085 1327160790588304431267391)
          ·
            refine ⟨1990741185882456646901087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327160790588304431267391 1990741185882456646901087)
            ·
              refine ⟨2986111778823684970351631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990741185882456646901087 2986111778823684970351631)
              ·
                refine ⟨4479167668235527455527447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986111778823684970351631 4479167668235527455527447)
                ·
                  refine ⟨6718751502353291183291171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479167668235527455527447 6718751502353291183291171)
                  ·
                    refine ⟨10078127253529936774936757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6718751502353291183291171 10078127253529936774936757)
                    ·
                      refine ⟨944824430018431572650321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10078127253529936774936757 944824430018431572650321)
                      ·
                        rfl

theorem cell23_1840039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1840039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840039 prefixEnd_1840039 := by exact prefixLift 1840039
  have htrace : WordTrace (prefixWord ++ tailWord_1840039) baseStart_1840039 baseEnd_1840039 := by
    simpa [prefixWord, tailWord_1840039, baseEnd_1840039] using wordTrace_append hprefix tailTrace_1840039
  have hstable : (prefixWord ++ tailWord_1840039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840039).length < 2 ^ (prefixWord ++ tailWord_1840039).sum := by decide
  have hdescent : baseEnd_1840039 < baseStart_1840039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840058 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1840058 : Nat := 118140960795 + 1840058 * 2 ^ 59
def prefixEnd_1840058 : Nat := 4983230072969 + 3 ^ 40 * 1840058 * 2
def baseEnd_1840058 : Nat := 944834186150866998312733

theorem tailTrace_1840058 : CollatzResearch.WordTrace tailWord_1840058 prefixEnd_1840058 944834186150866998312733 := by
  unfold tailWord_1840058
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778107191947899433060207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44741619178527731821493885 16778107191947899433060207)
  ·
    refine ⟨25167160787921849149590311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16778107191947899433060207 25167160787921849149590311)
    ·
      refine ⟨37750741181882773724385467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25167160787921849149590311 37750741181882773724385467)
      ·
        refine ⟨56626111772824160586578201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37750741181882773724385467 56626111772824160586578201)
        ·
          refine ⟨42469583829618120439933651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56626111772824160586578201 42469583829618120439933651)
          ·
            refine ⟨63704375744427180659900477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42469583829618120439933651 63704375744427180659900477)
            ·
              refine ⟨23889140904160192747462679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63704375744427180659900477 23889140904160192747462679)
              ·
                refine ⟨35833711356240289121194019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23889140904160192747462679 35833711356240289121194019)
                ·
                  refine ⟨53750567034360433681791029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35833711356240289121194019 53750567034360433681791029)
                  ·
                    refine ⟨5039115659471290657667909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53750567034360433681791029 5039115659471290657667909)
                    ·
                      refine ⟨944834186150866998312733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 5039115659471290657667909 944834186150866998312733)
                      ·
                        rfl

theorem cell23_1840058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1840058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840058 prefixEnd_1840058 := by exact prefixLift 1840058
  have htrace : WordTrace (prefixWord ++ tailWord_1840058) baseStart_1840058 baseEnd_1840058 := by
    simpa [prefixWord, tailWord_1840058, baseEnd_1840058] using wordTrace_append hprefix tailTrace_1840058
  have hstable : (prefixWord ++ tailWord_1840058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840058).length < 2 ^ (prefixWord ++ tailWord_1840058).sum := by decide
  have hdescent : baseEnd_1840058 < baseStart_1840058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840062 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2]
def baseStart_1840062 : Nat := 118140960795 + 1840062 * 2 ^ 59
def prefixEnd_1840062 : Nat := 4983230072969 + 3 ^ 40 * 1840062 * 2
def baseEnd_1840062 : Nat := 944836240073484982662715

theorem tailTrace_1840062 : CollatzResearch.WordTrace tailWord_1840062 prefixEnd_1840062 944836240073484982662715 := by
  unfold tailWord_1840062
  simp only [CollatzResearch.WordTrace]
  refine ⟨8389071832472138301923305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 44741716439851404276924293 8389071832472138301923305)
  ·
    refine ⟨6291803874354103726442479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8389071832472138301923305 6291803874354103726442479)
    ·
      refine ⟨9437705811531155589663719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291803874354103726442479 9437705811531155589663719)
      ·
        refine ⟨14156558717296733384495579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9437705811531155589663719 14156558717296733384495579)
        ·
          refine ⟨21234838075945100076743369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14156558717296733384495579 21234838075945100076743369)
          ·
            refine ⟨15926128556958825057557527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21234838075945100076743369 15926128556958825057557527)
            ·
              refine ⟨23889192835438237586336291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15926128556958825057557527 23889192835438237586336291)
              ·
                refine ⟨35833789253157356379504437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23889192835438237586336291 35833789253157356379504437)
                ·
                  refine ⟨3359417742483502160578541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35833789253157356379504437 3359417742483502160578541)
                  ·
                    refine ⟨1259781653431313310216953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3359417742483502160578541 1259781653431313310216953)
                    ·
                      refine ⟨944836240073484982662715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1259781653431313310216953 944836240073484982662715)
                      ·
                        rfl

theorem cell23_1840062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_1840062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840062 prefixEnd_1840062 := by exact prefixLift 1840062
  have htrace : WordTrace (prefixWord ++ tailWord_1840062) baseStart_1840062 baseEnd_1840062 := by
    simpa [prefixWord, tailWord_1840062, baseEnd_1840062] using wordTrace_append hprefix tailTrace_1840062
  have hstable : (prefixWord ++ tailWord_1840062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840062).length < 2 ^ (prefixWord ++ tailWord_1840062).sum := by decide
  have hdescent : baseEnd_1840062 < baseStart_1840062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1840146 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_1840146 : Nat := 118140960795 + 1840146 * 2 ^ 59
def prefixEnd_1840146 : Nat := 4983230072969 + 3 ^ 40 * 1840146 * 2
def baseEnd_1840146 : Nat := 944879372448462654012329

theorem tailTrace_1840146 : CollatzResearch.WordTrace tailWord_1840146 prefixEnd_1840146 944879372448462654012329 := by
  unfold tailWord_1840146
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778909597868197190361073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 44743758927648525840962861 16778909597868197190361073)
  ·
    refine ⟨12584182198401147892770805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16778909597868197190361073 12584182198401147892770805)
    ·
      refine ⟨1179767081100107614947263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12584182198401147892770805 1179767081100107614947263)
      ·
        refine ⟨1769650621650161422420895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179767081100107614947263 1769650621650161422420895)
        ·
          refine ⟨2654475932475242133631343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769650621650161422420895 2654475932475242133631343)
          ·
            refine ⟨3981713898712863200447015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654475932475242133631343 3981713898712863200447015)
            ·
              refine ⟨5972570848069294800670523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3981713898712863200447015 5972570848069294800670523)
              ·
                refine ⟨8958856272103942201005785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972570848069294800670523 8958856272103942201005785)
                ·
                  refine ⟨6719142204077956650754339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8958856272103942201005785 6719142204077956650754339)
                  ·
                    refine ⟨10078713306116934976131509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6719142204077956650754339 10078713306116934976131509)
                    ·
                      refine ⟨944879372448462654012329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 10078713306116934976131509 944879372448462654012329)
                      ·
                        rfl

theorem cell23_1840146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_1840146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1840146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1840146 prefixEnd_1840146 := by exact prefixLift 1840146
  have htrace : WordTrace (prefixWord ++ tailWord_1840146) baseStart_1840146 baseEnd_1840146 := by
    simpa [prefixWord, tailWord_1840146, baseEnd_1840146] using wordTrace_append hprefix tailTrace_1840146
  have hstable : (prefixWord ++ tailWord_1840146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1840146).length < 2 ^ (prefixWord ++ tailWord_1840146).sum := by decide
  have hdescent : baseEnd_1840146 < baseStart_1840146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1840146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
